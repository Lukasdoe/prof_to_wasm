#include <cstdint>
#include <iostream>
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


int main(int argc, char** argv) {
    if (argc != 4) {
        printf("Usage: %s <input.wasm> <output.wasm> <input.profraw>\n", argv[0]);
    }
    const char* wasm_in = argv[1];
    const char* wasm_out = argv[2];
    const char* profile_in = argv[3];

    wabt::Result result;
    std::vector<uint8_t> file_data;
    result = wabt::ReadFile(wasm_in, &file_data);

    if (wabt::Failed(result)) {
        std::cerr << "Error reading input file: " << wasm_in << std::endl;
        return 1;
    }

    wabt::Errors errors;
    wabt::Module module;
    wabt::Features features;
    std::unique_ptr<wabt::FileStream> log_stream;
    wabt::ReadBinaryOptions options(features, log_stream.get(),true, true,true);
    result = ReadBinaryIr(wasm_in, file_data.data(), file_data.size(), options, &errors, &module);
    if (wabt::Failed(result)) {
        FormatErrorsToFile(errors, wabt::Location::Type::Binary);
    }


    //
    auto FS = llvm::vfs::getRealFileSystem();
    auto readerRes = llvm::InstrProfReader::create(profile_in, *FS);
    if (auto err = readerRes.takeError()) {
        std::cerr << "Error creating profile reader: " << llvm::toString(std::move(err)) << std::endl;
        return 1;
    }
    auto reader = std::move(readerRes.get());
    assert(reader->isIRLevelProfile());
    std::map<uint32_t, std::map<uint32_t, uint8_t>> hints;
    for (const auto &Entry : *reader) {
        uint32_t func_idx;
        uint32_t offset;
        if (sscanf(Entry.Name.data(), "%d_%d", &func_idx, &offset) == EOF) {
            std::cerr << "Error parsing function index and offset from profile entry: " << Entry.Name.str() << std::endl;
            return 1;
        }
        assert(Entry.Counts.size() == 2);
        if (Entry.Counts[0] + Entry.Counts[1] == 0) {
            continue;
        }
        float hint_value_f = Entry.Counts[0] / (float)(Entry.Counts[0] + Entry.Counts[1]);
        uint8_t hint_value = 0;
        if (hint_value_f > 0.5) {
            hint_value = 1; // true branch
        } else if (hint_value_f <= 0.5) {
            hint_value = 0; // false branch
        } else {
            __builtin_unreachable();
        }
        printf("Func: %d: C_true: %lu, C_false: %lu => %f => %d\n", func_idx, Entry.Counts[0], Entry.Counts[1], hint_value_f, hint_value);

        if (!hints.contains(func_idx)) {
            hints.insert({func_idx, std::map<uint32_t, uint8_t>()});
        }
        hints[func_idx].insert({offset, hint_value});
    }

    //
    wabt::Custom branch_hints_section{wabt::Location(), "metadata.code.branch_hint"};
    wabt::MemoryStream s{};
    wabt::WriteU32Leb128(&s, hints.size(), "num funcs");
    for (auto [func_idx, offsets] : hints) {
        wabt::WriteU32Leb128(&s, func_idx, "func idx");
        wabt::WriteU32Leb128(&s, offsets.size(), "num offsets");
        for (auto [offset, value] : offsets) {
            wabt::WriteU32Leb128(&s, offset, "offset");
            wabt::WriteU32Leb128(&s, 1, "size");
            wabt::WriteU32Leb128(&s, value, "value");
        }
    }
    branch_hints_section.data = s.output_buffer().data;
    module.customs.push_back(branch_hints_section);
    //


    wabt::MemoryStream stream(log_stream.get());
    wabt::WriteBinaryOptions write_binary_options;
    write_binary_options.features = features;
    result = WriteBinaryModule(&stream, &module, write_binary_options);
    if (wabt::Failed(result)) {
        std::cerr << "Error writing binary module to memory." << std::endl;
        return 1;
    }

    result = stream.output_buffer().WriteToFile(wasm_out);
    if (wabt::Failed(result)) {
        std::cerr << "Error writing output file: " << wasm_out << std::endl;
        return 1;
    }
    return 0;
}
