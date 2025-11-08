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

auto parse_profile(const char* profile_in, float prob_high, float prob_low, bool non_binary_hints) {
    auto FS = llvm::vfs::getRealFileSystem();
    auto readerRes = llvm::InstrProfReader::create(profile_in, *FS);
    if (auto err = readerRes.takeError()) {
        throw std::runtime_error{std::format("Error creating profile reader: {}", llvm::toString(std::move(err)))};
    }
    auto reader = std::move(readerRes.get());
    assert(reader->isIRLevelProfile());
    std::map<uint32_t, std::map<uint32_t, uint8_t>> hints;
    std::unordered_set<std::pair<uint32_t, uint32_t>, PairHash> entries;
    for (const auto &Entry: *reader) {
        uint32_t func_idx;
        uint32_t offset;
        if (sscanf(Entry.Name.data(), "%d_%d", &func_idx, &offset) == EOF) {
            throw std::runtime_error{std::format("Error parsing function index and offset from profile entry: {}", Entry.Name.str())};
        }
        if (func_idx >= 169) continue;
        assert(Entry.Counts.size() == 2);
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
//                printf("%f >= %f\n", hint_value_f, prob_high);
            } else if (hint_value_f <= prob_low) {
                hint_value = 0; // false branch
//                printf("%f < %f\n", hint_value_f, prob_low);
            } else {
//                printf("%f between %f and %f\n", hint_value_f, prob_low, prob_high);
                continue; // Do not emit a hint if between thresholds
            }
        }
//        printf("%lu / %lu => %f => %d\n", Entry.Counts[0], Entry.Counts[1], hint_value_f, hint_value);

        if (!hints.contains(func_idx)) {
            hints.insert({func_idx, std::map<uint32_t, uint8_t>()});
        }
        hints[func_idx].insert({offset, hint_value});
        entries.insert({func_idx, offset});
    }
    return std::make_pair(hints, entries);
}

void check_existing_hints(wabt::Module &module, const std::unordered_set<std::pair<uint32_t, uint32_t>, PairHash> &entries, std::map<uint32_t, std::map<uint32_t, uint8_t>>& hints, bool non_binary_hints) {
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
                if (!entries.contains({func_idx, offset})) {
                    if (!hints.contains(func_idx)) {
                        hints.insert({func_idx, std::map<uint32_t, uint8_t>()});
                    }
                    hints[func_idx].insert({offset, value});
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

void validate_profile_hints(wabt::Module &module, const std::map<uint32_t, std::map<uint32_t, uint8_t>> &hints) {
    for (const auto &[func_idx, offsets] : hints) {
        wabt::Var func_var;
        func_var.set_index(func_idx);
        wabt::Func *func = module.GetFunc(func_var);
        if (!func) {
            throw std::runtime_error{std::format("Function with index {} from profile not found in module.", func_idx)};
        }

        std::string func_name = func->name;
        size_t base_offset = func->loc.offset;
        // std::cout << std::format("Validating function {} ({}) with base offset {:x}\n", func_name, func_idx, base_offset);

        std::set<uint32_t> offsets_to_find;
        for (const auto &offset : offsets | std::views::keys) {
            offsets_to_find.insert(offset);
        }

        auto validation_func = [&](const wabt::Expr& expr, size_t offset) {
            if (offsets_to_find.empty()) return;

            size_t expr_offset = offset - base_offset;
            if (offsets_to_find.contains(expr_offset)) {
                if (expr.type() != wabt::ExprType::BrIf) {
                    std::cerr << std::format("Offset {} for function {} ({}) from profile is not a BrIf instruction, but {}.\n", expr_offset, func_name, func_idx, expr_type_to_str(expr.type()));
                }
                // std::cout << std::format("Found offset {} for function {} ({}) from profile at {:x}.\n", expr_offset, func_name, func_idx, offset);
                offsets_to_find.erase(expr_offset);
            }
        };
        auto print_func = [&](const wabt::Expr& expr, size_t offset) {
                std::cout << std::format("{} | {:x}: {}\n", offset - base_offset, offset, expr_type_to_str(expr.type()));
        };

        // size_t offset = base_offset;
        // visit_exprs(func->exprs, print_func, offset);
        // std::cout.flush();
        size_t offset = base_offset;
        visit_exprs(func->exprs, validation_func, offset);

        if (!offsets_to_find.empty()) {
            for (const auto &offset : offsets_to_find) {
                 std::cerr << std::format("Offset {} for function {} ({}) from profile not found in module.\n", offset, func_name, func_idx);
            }
//            throw std::runtime_error{"Not all profile hints could be validated."};
        }
    }
}

wabt::Custom add_metadata_section(wabt::Module &module, const std::map<uint32_t, std::map<uint32_t, uint8_t>> &hints) {
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

void dump_section_into_wasm_file(wabt::Custom &section, const char *wasm_in, const char *wasm_out) {
    std::filesystem::copy_file(wasm_in, wasm_out, std::filesystem::copy_options::overwrite_existing);
    size_t og_size = std::filesystem::file_size(wasm_out);
    size_t custom_section_size = 1 + 5 + 5 + section.name.size() + section.data.size();
    size_t new_module_size = og_size + custom_section_size;
    std::filesystem::resize_file(wasm_out, new_module_size);

    int file_fd = open(wasm_out, O_RDWR);
    auto* file_map = static_cast<uint8_t*>(mmap(nullptr, new_module_size, PROT_READ | PROT_WRITE, MAP_SHARED, file_fd, 0));
    assert(file_map != MAP_FAILED);
    auto* file_end = file_map + new_module_size;

    constexpr size_t magic_len = 4;
    constexpr size_t version_len = 4;
    size_t off = magic_len + version_len;

    // remove previous branch hints
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
            if (name == "metadata.code.branch_hint") {
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
    // make space for branch hints
    memmove(file_map + off + custom_section_size, file_map + off, og_size - off);
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

    // check that the moving worked
    assert(file_map[off + section.data.size()] == static_cast<uint8_t>(wabt::BinarySection::Code));

    munmap(file_map, new_module_size);
    std::filesystem::resize_file(wasm_out, new_module_size - removed_section_size);
}

int main(int argc, char **argv) {
    // Default threshold values
    float prob_high = 0.5f;
    float prob_low = 0.5f;
    bool non_binary_hints = false;

    // Parse command-line flags
    int argi = 1;
    while (argi < argc && strncmp(argv[argi], "--", 2) == 0) {
        if (strncmp(argv[argi], "--wasm-branch-prob-high=", 24) == 0) {
            prob_high = std::stof(argv[argi] + 24);
        } else if (strncmp(argv[argi], "--wasm-branch-prob-low=", 23) == 0) {
            prob_low = std::stof(argv[argi] + 23);
        } else if (strncmp(argv[argi], "--wasm-non-binary-hints", 23) == 0) {
            non_binary_hints = true;
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

    if (argc - argi != 3) {
        printf("Usage: %s [--wasm-branch-prob-high=<float>] [--wasm-branch-prob-low=<float>] [--wasm-non-binary-hints] <input.wasm> <output.wasm> <input.profraw>\n", argv[0]);
        return 1;
    }
    const char *wasm_in = argv[argi];
    const char *wasm_out = argv[argi + 1];
    const char *profile_in = argv[argi + 2];

    const auto module = parse_module(wasm_in);
    auto [hints, entries] = parse_profile(profile_in, prob_high, prob_low, non_binary_hints);
    check_existing_hints(*module, entries, hints, non_binary_hints);
    validate_profile_hints(*module, hints);
    wabt::Custom branch_hints = add_metadata_section(*module, hints);
    dump_section_into_wasm_file(branch_hints, wasm_in, wasm_out);

    return 0;
}
