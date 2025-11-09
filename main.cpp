#include <cstdint>
#include <fcntl.h>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <ranges>
#include <unordered_set>
#include <vector>
#include <wabt/binary-reader-ir.h>
#include <wabt/binary-reader.h>
#include <wabt/error-formatter.h>
#include <wabt/feature.h>
#include <wabt/ir.h>
#include <wabt/stream.h>
#include <wabt/binary-writer.h>
#include <wabt/leb128.h>
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/VirtualFileSystem.h"
#include "llvm/ProfileData/InstrProfReader.h"
#include <sys/mman.h>

// assume single threaded execution
static wabt::Result result;
static std::unique_ptr<wabt::FileStream> log_stream;
static wabt::Features features;

struct PairHash {
    template <class T1, class T2>
    std::size_t operator () (const std::pair<T1, T2>& p) const {
        auto h1 = std::hash<T1>{}(p.first);
        auto h2 = std::hash<T2>{}(p.second);
        // A common way to combine hashes.
        return h1 ^ (h2 << 1);
    }
};

std::unique_ptr<wabt::Module> parse_module(const char* wasm_in) {
    std::vector<uint8_t> file_data;
    result = wabt::ReadFile(wasm_in, &file_data);

    if (wabt::Failed(result)) {
        throw std::runtime_error{std::format("Error reading input file: {}", wasm_in)};
    }

    wabt::Errors errors;
    auto module = std::make_unique<wabt::Module>();
    wabt::ReadBinaryOptions options(features, log_stream.get(), true, true, true);
    result = ReadBinaryIr(wasm_in, file_data.data(), file_data.size(), options, &errors, module.get());
    if (wabt::Failed(result)) {
        FormatErrorsToFile(errors, wabt::Location::Type::Binary);
    }
    return module;
}

struct CallTargetInfo {
    uint32_t func_idx;
    uint64_t count;
};

struct ProfileData {
    std::map<uint32_t, std::map<uint32_t, uint8_t>> branch_hints;
    std::unordered_set<std::pair<uint32_t, uint32_t>, PairHash> branch_entries;
    std::map<uint32_t, std::map<uint32_t, std::vector<CallTargetInfo>>> value_hints;
    std::unordered_set<std::pair<uint32_t, uint32_t>, PairHash> value_entries;
};

auto parse_profile(const char* profile_in, float prob_high, float prob_low, bool non_binary_hints) {
    auto FS = llvm::vfs::getRealFileSystem();
    auto readerRes = llvm::InstrProfReader::create(profile_in, *FS);
    if (auto err = readerRes.takeError()) {
        throw std::runtime_error{std::format("Error creating profile reader: {}", llvm::toString(std::move(err)))};
    }
    auto reader = std::move(readerRes.get());
    assert(reader->isIRLevelProfile());

    ProfileData profile_data;

    for (const auto &Entry: *reader) {
        uint32_t func_idx;
        uint32_t offset;
        if (sscanf(Entry.Name.data(), "%d_%d", &func_idx, &offset) == EOF) {
            throw std::runtime_error{std::format("Error parsing function index and offset from profile entry: {}", Entry.Name.str())};
        }
        if (func_idx >= 169) continue;

        // Handle branch profiling (counter records)
        if (Entry.Counts.size() == 2) {
            if (Entry.Counts[0] + Entry.Counts[1] == 0) {
                continue;
            }
            float hint_value_f = Entry.Counts[0] / static_cast<float>(Entry.Counts[0] + Entry.Counts[1]);
            uint8_t hint_value;
            if (non_binary_hints) {
                hint_value = std::min(static_cast<uint8_t>(hint_value_f * 128), static_cast<uint8_t>(127));
            } else {
                // Use thresholds to determine hint emission
                if (hint_value_f >= prob_high) {
                    hint_value = 1; // true branch
                } else if (hint_value_f <= prob_low) {
                    hint_value = 0; // false branch
                } else {
                    continue; // Do not emit a hint if between thresholds
                }
            }

            if (!profile_data.branch_hints.contains(func_idx)) {
                profile_data.branch_hints.insert({func_idx, std::map<uint32_t, uint8_t>()});
            }
            profile_data.branch_hints[func_idx].insert({offset, hint_value});
            profile_data.branch_entries.insert({func_idx, offset});
        }

        // Handle value profiling records
        // Value profile data contains target function indices for indirect calls
        // The offset from the Entry name tells us which instruction this profile data is for
        uint32_t numValueSites = Entry.getNumValueSites(llvm::IPVK_IndirectCallTarget);
        if (numValueSites > 0) {
            // For each value site in this entry, we collect the target function indices
            // Typically there should be one value site per entry when using func_idx_offset naming
            for (uint32_t site = 0; site < numValueSites; ++site) {
                auto valueArray = Entry.getValueArrayForSite(llvm::IPVK_IndirectCallTarget, site);
                if (valueArray.empty()) continue;

                std::vector<CallTargetInfo> targets;
                for (const auto &valueData : valueArray) {
                    // valueData.Value contains the func_idx of the indirect call target
                    // valueData.Count contains the number of times this target was called
                    targets.push_back({static_cast<uint32_t>(valueData.Value), valueData.Count});
                }

                if (!targets.empty()) {
                    if (!profile_data.value_hints.contains(func_idx)) {
                        profile_data.value_hints.insert({func_idx, std::map<uint32_t, std::vector<CallTargetInfo>>()});
                    }
                    // Use the offset from the Entry name for this value site
                    // If there are multiple sites, we might need to adjust the offset
                    uint32_t site_offset = (numValueSites > 1) ? offset + site : offset;
                    profile_data.value_hints[func_idx].insert({site_offset, std::move(targets)});
                    profile_data.value_entries.insert({func_idx, site_offset});
                }
            }
        }
    }
    return profile_data;
}

void check_existing_hints(wabt::Module &module, ProfileData& profile_data, bool non_binary_hints) {
    // Check existing branch hints
    if (auto it = std::ranges::find_if(module.customs,
                                       [](const wabt::Custom &c) { return c.name == "metadata.code.branch_hint"; });
        it != module.customs.end()) {
        auto *data = it->data.data();
        auto *end = data + it->data.size();
        uint32_t numFuncHints;
        data += wabt::ReadU32Leb128(data, end, &numFuncHints);
        for (uint32_t i = 0; i < numFuncHints; ++i) {
            uint32_t func_idx;
            data += wabt::ReadU32Leb128(data, end, &func_idx);
            uint32_t numOffsets;
            data += wabt::ReadU32Leb128(data, end, &numOffsets);
            for (uint32_t j = 0; j < numOffsets; ++j) {
                uint32_t offset;
                data += wabt::ReadU32Leb128(data, end, &offset);
                uint32_t size;
                data += wabt::ReadU32Leb128(data, end, &size);
                uint32_t value;
                data += wabt::ReadU32Leb128(data, end, &value);
                if (!non_binary_hints && value > 0x1) {
                    std::cerr << "Error: found non-binary hint value with non-binary hints disabled" << std::endl;
                    throw std::runtime_error{"Error: found non-binary hint value"};
                }
                if (!profile_data.branch_entries.contains({func_idx, offset})) {
                    if (!profile_data.branch_hints.contains(func_idx)) {
                        profile_data.branch_hints.insert({func_idx, std::map<uint32_t, uint8_t>()});
                    }
                    profile_data.branch_hints[func_idx].insert({offset, value});
                }
            }
        }
        module.customs.erase(it);
    }

    // Check existing indirect call hints
    if (auto it = std::ranges::find_if(module.customs,
                                       [](const wabt::Custom &c) { return c.name == "metadata.code.call_targets"; });
        it != module.customs.end()) {
        auto *data = it->data.data();
        auto *end = data + it->data.size();
        uint32_t numFuncHints;
        data += wabt::ReadU32Leb128(data, end, &numFuncHints);
        for (uint32_t i = 0; i < numFuncHints; ++i) {
            uint32_t func_idx;
            data += wabt::ReadU32Leb128(data, end, &func_idx);
            uint32_t numOffsets;
            data += wabt::ReadU32Leb128(data, end, &numOffsets);
            for (uint32_t j = 0; j < numOffsets; ++j) {
                uint32_t offset;
                data += wabt::ReadU32Leb128(data, end, &offset);
                uint32_t hint_length;
                data += wabt::ReadU32Leb128(data, end, &hint_length);
                // Read targets with frequency percentages
                std::vector<CallTargetInfo> targets;
                auto *hint_end = data + hint_length;
                while (data < hint_end) {
                    uint32_t target_idx;
                    data += wabt::ReadU32Leb128(data, end, &target_idx);
                    uint32_t frequency_percent;
                    data += wabt::ReadU32Leb128(data, end, &frequency_percent);
                    // Convert percentage back to count (approximate, we don't have exact total)
                    targets.push_back({target_idx, frequency_percent});
                }
                if (!profile_data.value_entries.contains({func_idx, offset})) {
                    if (!profile_data.value_hints.contains(func_idx)) {
                        profile_data.value_hints.insert({func_idx, std::map<uint32_t, std::vector<CallTargetInfo>>()});
                    }
                    profile_data.value_hints[func_idx].insert({offset, std::move(targets)});
                }
            }
        }
        module.customs.erase(it);
    }
}

std::string expr_type_to_str(wabt::ExprType type) {
    switch (type) {
        case wabt::ExprType::AtomicLoad: return "AtomicLoad";
        case wabt::ExprType::AtomicRmw: return "AtomicRmw";
        case wabt::ExprType::AtomicRmwCmpxchg: return "AtomicRmwCmpxchg";
        case wabt::ExprType::AtomicStore: return "AtomicStore";
        case wabt::ExprType::AtomicNotify: return "AtomicNotify";
        case wabt::ExprType::AtomicFence: return "AtomicFence";
        case wabt::ExprType::AtomicWait: return "AtomicWait";
        case wabt::ExprType::Binary: return "Binary";
        case wabt::ExprType::Block: return "Block";
        case wabt::ExprType::Br: return "Br";
        case wabt::ExprType::BrIf: return "BrIf";
        case wabt::ExprType::BrTable: return "BrTable";
        case wabt::ExprType::Call: return "Call";
        case wabt::ExprType::CallIndirect: return "CallIndirect";
        case wabt::ExprType::CallRef: return "CallRef";
        case wabt::ExprType::CodeMetadata: return "CodeMetadata";
        case wabt::ExprType::Compare: return "Compare";
        case wabt::ExprType::Const: return "Const";
        case wabt::ExprType::Convert: return "Convert";
        case wabt::ExprType::Drop: return "Drop";
        case wabt::ExprType::GlobalGet: return "GlobalGet";
        case wabt::ExprType::GlobalSet: return "GlobalSet";
        case wabt::ExprType::If: return "If";
        case wabt::ExprType::Load: return "Load";
        case wabt::ExprType::LocalGet: return "LocalGet";
        case wabt::ExprType::LocalSet: return "LocalSet";
        case wabt::ExprType::LocalTee: return "LocalTee";
        case wabt::ExprType::Loop: return "Loop";
        case wabt::ExprType::MemoryCopy: return "MemoryCopy";
        case wabt::ExprType::DataDrop: return "DataDrop";
        case wabt::ExprType::MemoryFill: return "MemoryFill";
        case wabt::ExprType::MemoryGrow: return "MemoryGrow";
        case wabt::ExprType::MemoryInit: return "MemoryInit";
        case wabt::ExprType::MemorySize: return "MemorySize";
        case wabt::ExprType::Nop: return "Nop";
        case wabt::ExprType::RefIsNull: return "RefIsNull";
        case wabt::ExprType::RefFunc: return "RefFunc";
        case wabt::ExprType::RefNull: return "RefNull";
        case wabt::ExprType::Rethrow: return "Rethrow";
        case wabt::ExprType::Return: return "Return";
        case wabt::ExprType::ReturnCall: return "ReturnCall";
        case wabt::ExprType::ReturnCallIndirect: return "ReturnCallIndirect";
        case wabt::ExprType::Select: return "Select";
        case wabt::ExprType::SimdLaneOp: return "SimdLaneOp";
        case wabt::ExprType::SimdLoadLane: return "SimdLoadLane";
        case wabt::ExprType::SimdStoreLane: return "SimdStoreLane";
        case wabt::ExprType::SimdShuffleOp: return "SimdShuffleOp";
        case wabt::ExprType::LoadSplat: return "LoadSplat";
        case wabt::ExprType::LoadZero: return "LoadZero";
        case wabt::ExprType::Store: return "Store";
        case wabt::ExprType::TableCopy: return "TableCopy";
        case wabt::ExprType::ElemDrop: return "ElemDrop";
        case wabt::ExprType::TableInit: return "TableInit";
        case wabt::ExprType::TableGet: return "TableGet";
        case wabt::ExprType::TableGrow: return "TableGrow";
        case wabt::ExprType::TableSize: return "TableSize";
        case wabt::ExprType::TableSet: return "TableSet";
        case wabt::ExprType::TableFill: return "TableFill";
        case wabt::ExprType::Ternary: return "Ternary";
        case wabt::ExprType::Throw: return "Throw";
        case wabt::ExprType::ThrowRef: return "ThrowRef";
        case wabt::ExprType::Try: return "Try";
        case wabt::ExprType::TryTable: return "TryTable";
        case wabt::ExprType::Unary: return "Unary";
        case wabt::ExprType::Unreachable: return "Unreachable";
    };
    throw std::runtime_error{std::format("Unknown expression type: {}", static_cast<int>(type))};
}

void visit_exprs(const wabt::ExprList &exprs, auto f, size_t& prev_offset) {
    for (const auto &expr : exprs) {
        f(expr, prev_offset);
        prev_offset = expr.loc.offset;
        switch (expr.type()) {
            case wabt::ExprType::Block:
                visit_exprs(static_cast<const wabt::BlockExpr &>(expr).block.exprs, f, prev_offset);
                break;
            case wabt::ExprType::Loop:
                visit_exprs(static_cast<const wabt::LoopExpr &>(expr).block.exprs, f, prev_offset);
                break;
            case wabt::ExprType::If: {
                const auto& if_expr = static_cast<const wabt::IfExpr&>(expr);
                visit_exprs(if_expr.true_.exprs, f, prev_offset);
                if (!if_expr.false_.empty()) {
                    visit_exprs(if_expr.false_, f, prev_offset);
                }
                break;
            }
            case wabt::ExprType::Try:
            case wabt::ExprType::TryTable: {
                const auto& try_expr = static_cast<const wabt::TryExpr&>(expr);
                visit_exprs(try_expr.block.exprs, f, prev_offset);
                for (const auto& catch_ : try_expr.catches) {
                    visit_exprs(catch_.exprs, f, prev_offset);
                }
                break;
            }
            default:
                break;
        }
    }
}

void validate_profile_hints(wabt::Module &module, const ProfileData &profile_data) {
    // Validate branch hints
    for (const auto &[func_idx, offsets] : profile_data.branch_hints) {
        wabt::Var func_var;
        func_var.set_index(func_idx);
        wabt::Func *func = module.GetFunc(func_var);
        if (!func) {
            throw std::runtime_error{std::format("Function with index {} from profile not found in module.", func_idx)};
        }

        std::string func_name = func->name;
        size_t base_offset = func->loc.offset;

        std::set<uint32_t> offsets_to_find;
        for (const auto &offset : offsets | std::views::keys) {
            offsets_to_find.insert(offset);
        }

        auto validation_func = [&](const wabt::Expr& expr, size_t offset) {
            if (offsets_to_find.empty()) return;

            size_t expr_offset = offset - base_offset;
            if (offsets_to_find.contains(expr_offset)) {
                if (expr.type() != wabt::ExprType::BrIf) {
                    std::cerr << std::format("Offset {} for function {} ({}) from branch profile is not a BrIf instruction, but {}.\n", expr_offset, func_name, func_idx, expr_type_to_str(expr.type()));
                }
                offsets_to_find.erase(expr_offset);
            }
        };

        size_t offset = base_offset;
        visit_exprs(func->exprs, validation_func, offset);

        if (!offsets_to_find.empty()) {
            for (const auto &offset : offsets_to_find) {
                 std::cerr << std::format("Offset {} for function {} ({}) from branch profile not found in module.\n", offset, func_name, func_idx);
            }
        }
    }

    // Validate indirect call hints
    for (const auto &[func_idx, offsets] : profile_data.value_hints) {
        wabt::Var func_var;
        func_var.set_index(func_idx);
        wabt::Func *func = module.GetFunc(func_var);
        if (!func) {
            throw std::runtime_error{std::format("Function with index {} from value profile not found in module.", func_idx)};
        }

        std::string func_name = func->name;
        size_t base_offset = func->loc.offset;

        std::set<uint32_t> offsets_to_find;
        for (const auto &offset : offsets | std::views::keys) {
            offsets_to_find.insert(offset);
        }

        auto validation_func = [&](const wabt::Expr& expr, size_t offset) {
            if (offsets_to_find.empty()) return;

            size_t expr_offset = offset - base_offset;
            if (offsets_to_find.contains(expr_offset)) {
                if (expr.type() != wabt::ExprType::CallIndirect) {
                    std::cerr << std::format("Offset {} for function {} ({}) from value profile is not a CallIndirect instruction, but {}.\n", expr_offset, func_name, func_idx, expr_type_to_str(expr.type()));
                }
                offsets_to_find.erase(expr_offset);
            }
        };

        size_t offset = base_offset;
        visit_exprs(func->exprs, validation_func, offset);

        if (!offsets_to_find.empty()) {
            for (const auto &offset : offsets_to_find) {
                 std::cerr << std::format("Offset {} for function {} ({}) from value profile not found in module.\n", offset, func_name, func_idx);
            }
        }
    }
}

wabt::Custom add_branch_metadata_section(wabt::Module &module, const std::map<uint32_t, std::map<uint32_t, uint8_t>> &hints) {
    wabt::MemoryStream s{};
    wabt::WriteU32Leb128(&s, hints.size(), "num funcs");
    for (const auto &[func_idx, offsets]: hints) {
        wabt::WriteU32Leb128(&s, func_idx, "func idx");
        wabt::WriteU32Leb128(&s, offsets.size(), "num offsets");
        for (auto [offset, value]: offsets) {
            wabt::WriteU32Leb128(&s, offset, "offset");
            wabt::WriteU32Leb128(&s, 1, "size");
            wabt::WriteU32Leb128(&s, value, "value");
        }
    }
    wabt::Custom branch_hints_section{wabt::Location(), "metadata.code.branch_hint"};
    branch_hints_section.data = s.output_buffer().data;
    return branch_hints_section;
}

wabt::Custom add_indirect_call_metadata_section(wabt::Module &module, const std::map<uint32_t, std::map<uint32_t, std::vector<CallTargetInfo>>> &hints) {
    wabt::MemoryStream s{};
    wabt::WriteU32Leb128(&s, hints.size(), "num funcs");
    for (const auto &[func_idx, offsets]: hints) {
        wabt::WriteU32Leb128(&s, func_idx, "func idx");
        wabt::WriteU32Leb128(&s, offsets.size(), "num offsets");
        for (const auto &[offset, targets]: offsets) {
            // Calculate total count for percentage computation
            uint64_t total_count = 0;
            for (const auto &target : targets) {
                total_count += target.count;
            }

            // Write offset
            wabt::WriteU32Leb128(&s, offset, "offset");

            // Write hint data to temporary stream to calculate length
            wabt::MemoryStream hint_data{};
            for (const auto &target : targets) {
                wabt::WriteU32Leb128(&hint_data, target.func_idx, "target func_idx");
                // Calculate frequency as percentage (0-100)
                uint32_t frequency_percent = total_count > 0
                    ? static_cast<uint32_t>((target.count * 100) / total_count)
                    : 0;
                wabt::WriteU32Leb128(&hint_data, frequency_percent, "call frequency percent");
            }

            // Write hint length
            size_t hint_length = hint_data.output_buffer().data.size();
            wabt::WriteU32Leb128(&s, hint_length, "hint length");

            // Write hint data
            s.WriteData(hint_data.output_buffer().data.data(), hint_length, "call targets");
        }
    }
    wabt::Custom indirect_call_hints_section{wabt::Location(), "metadata.code.call_targets"};
    indirect_call_hints_section.data = s.output_buffer().data;
    return indirect_call_hints_section;
}

void dump_sections_into_wasm_file(const std::vector<wabt::Custom> &sections, const char *wasm_in, const char *wasm_out) {
    std::filesystem::copy_file(wasm_in, wasm_out, std::filesystem::copy_options::overwrite_existing);
    size_t og_size = std::filesystem::file_size(wasm_out);

    // Calculate total size of new sections
    size_t total_custom_section_size = 0;
    for (const auto &section : sections) {
        total_custom_section_size += 1 + 5 + 5 + section.name.size() + section.data.size();
    }

    size_t new_module_size = og_size + total_custom_section_size;
    std::filesystem::resize_file(wasm_out, new_module_size);

    int file_fd = open(wasm_out, O_RDWR);
    auto* file_map = static_cast<uint8_t*>(mmap(nullptr, new_module_size, PROT_READ | PROT_WRITE, MAP_SHARED, file_fd, 0));
    assert(file_map != MAP_FAILED);
    auto* file_end = file_map + new_module_size;

    constexpr size_t magic_len = 4;
    constexpr size_t version_len = 4;
    size_t off = magic_len + version_len;

    // remove previous hints (both branch and indirect call)
    size_t removed_section_size = 0;
    while (off < new_module_size) {
        size_t section_start = off;
        uint8_t section_type = file_map[off];
        uint32_t section_size;
        const size_t size_size = wabt::ReadU32Leb128(file_map + off + 1, file_map + new_module_size, &section_size);
        off += 1 + size_size;
        if (section_type == static_cast<uint8_t>(wabt::BinarySection::Custom)) {
            uint32_t name_len;
            const size_t name_size = wabt::ReadU32Leb128(file_map + off, file_map + new_module_size, &name_len);
            const std::string_view name{reinterpret_cast<const char *>(file_map + off + name_size), name_len};
            if (name == "metadata.code.branch_hint" || name == "metadata.code.indirect_call_hint" || name == "metadata.code.call_targets") {
                const size_t section_end = section_start + 1 + size_size + section_size;
                memmove(file_map + section_start, file_map + section_end, new_module_size - section_end);
                removed_section_size += section_end - section_start;
                off = section_start;
                continue;
            }
        }
        off += section_size;
    }
    off = magic_len + version_len; // reset to after magic and version

    // find code section
    while (file_map[off] != static_cast<uint8_t>(wabt::BinarySection::Code)) {
        uint32_t section_size;
        const size_t size_size = wabt::ReadU32Leb128(file_map + off + 1, file_map + new_module_size, &section_size);
        off += 1 + size_size + section_size;
    }

    // Insert all custom sections before the code section
    memmove(file_map + off + total_custom_section_size, file_map + off, og_size - off);

    for (const auto &section : sections) {
        file_map[off++] = static_cast<uint8_t>(wabt::BinarySection::Custom);
        // -1 because the section type byte is not counted
        off += wabt::WriteFixedU32Leb128Raw(file_map + off, file_end, 5 + section.name.size() + section.data.size());
        // name vec size
        off += wabt::WriteFixedU32Leb128Raw(file_map + off, file_end, section.name.size());
        // name vec
        memcpy(file_map + off, section.name.data(), section.name.size());
        off += section.name.size();
        // data
        memcpy(file_map + off, section.data.data(), section.data.size());
        off += section.data.size();
    }

    // check that the moving worked
    assert(file_map[off] == static_cast<uint8_t>(wabt::BinarySection::Code));

    munmap(file_map, new_module_size);
    std::filesystem::resize_file(wasm_out, new_module_size - removed_section_size);
}

int main(int argc, char **argv) {
    // Default threshold values
    float prob_high = 0.5f;
    float prob_low = 0.5f;
    bool non_binary_hints = false;
    bool generate_branch_hints = false;
    bool generate_call_target_hints = false;

    // Parse command-line flags
    int argi = 1;
    while (argi < argc && strncmp(argv[argi], "--", 2) == 0) {
        if (strncmp(argv[argi], "--wasm-branch-prob-high=", 24) == 0) {
            prob_high = std::stof(argv[argi] + 24);
        } else if (strncmp(argv[argi], "--wasm-branch-prob-low=", 23) == 0) {
            prob_low = std::stof(argv[argi] + 23);
        } else if (strncmp(argv[argi], "--wasm-non-binary-hints", 23) == 0) {
            non_binary_hints = true;
        } else if (strncmp(argv[argi], "--wasm-branch-hints", 19) == 0) {
            generate_branch_hints = true;
        } else if (strncmp(argv[argi], "--wasm-call-target-hints", 24) == 0) {
            generate_call_target_hints = true;
        } else {
            printf("Unknown flag: %s\n", argv[argi]);
            return 1;
        }
        ++argi;
    }

    if (non_binary_hints && (prob_high != 0.5f || prob_low != 0.5f)) {
        std::cerr << "Error: --wasm-non-binary-hints cannot be used with --wasm-branch-prob-high or --wasm-branch-prob-low" << std::endl;
        return 1;
    }

    if (!generate_branch_hints && !generate_call_target_hints) {
        std::cerr << "Error: At least one of --wasm-branch-hints or --wasm-call-target-hints must be specified" << std::endl;
        return 1;
    }

    if (argc - argi != 3) {
        printf("Usage: %s [--wasm-branch-hints] [--wasm-call-target-hints] [--wasm-branch-prob-high=<float>] [--wasm-branch-prob-low=<float>] [--wasm-non-binary-hints] <input.wasm> <output.wasm> <input.profraw>\n", argv[0]);
        return 1;
    }
    const char *wasm_in = argv[argi];
    const char *wasm_out = argv[argi + 1];
    const char *profile_in = argv[argi + 2];

    const auto module = parse_module(wasm_in);
    auto profile_data = parse_profile(profile_in, prob_high, prob_low, non_binary_hints);
    check_existing_hints(*module, profile_data, non_binary_hints);
    validate_profile_hints(*module, profile_data);

    std::vector<wabt::Custom> custom_sections;

    if (generate_branch_hints && !profile_data.branch_hints.empty()) {
        custom_sections.push_back(add_branch_metadata_section(*module, profile_data.branch_hints));
    }

    if (generate_call_target_hints && !profile_data.value_hints.empty()) {
        custom_sections.push_back(add_indirect_call_metadata_section(*module, profile_data.value_hints));
    }

    if (!custom_sections.empty()) {
        dump_sections_into_wasm_file(custom_sections, wasm_in, wasm_out);
    } else {
        std::filesystem::copy_file(wasm_in, wasm_out, std::filesystem::copy_options::overwrite_existing);
    }

    return 0;
}
