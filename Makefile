# ============================================================================
# Makefile — Pryde compiler (frontend + IR pipeline)
# ============================================================================
# Requires: c3c v0.8.1  (auto-fetched to /tmp/c3/c3c if missing)
#           LLVM 22.1.x toolchain: llvm-as-22 llc-22 opt-22 ld.lld-22
#           Available from: https://apt.llvm.org/  (Debian trixie channel)
#
# Targets:
#   make              — build ./pryde
#   make asan         — AddressSanitizer build  → ./pryde_asan
#   make test         — build + conformance (87) + redteam (115)
#   make conform      — conformance suite only
#   make redteam      — red-team suite only
#   make clean        — remove built binaries + generated .ll/.bc/.o files
#   make c3c          — fetch c3c if missing (idempotent)
#   make runtime      — compile runtime/compiler_rt.c → runtime/compiler_rt.o
#
# LLVM 22 pipeline (no Clang anywhere):
#   ./pryde --emit-llvm output.ll source.pry        # emit LLVM 22 IR text
#   llvm-as-22 output.ll -o output.bc               # assemble to bitcode
#   opt-22 -O2 output.bc -o output.opt.bc           # optimise
#   llc-22 -filetype=obj -relocation-model=pic \
#          output.opt.bc -o output.o                # compile to ELF object
#   ld.lld-22 crt1.o crti.o output.o compiler_rt.o \
#             crtn.o -lc --dynamic-linker ... \
#             -o program                            # link with lld
# ============================================================================

C3C       := /tmp/c3/c3c
C3C_VER   := v0.8.1
C3C_URL   := https://github.com/c3lang/c3c/releases/download/$(C3C_VER)/c3-linux-static.tar.gz

BINARY    := pryde
ASAN      := pryde_asan

# LLVM 22 toolchain
LLVM_AS   := llvm-as-22
LLVM_OPT  := opt-22
LLC       := llc-22
LLD       := ld.lld-22
LLVM_AR   := llvm-ar-22
LLVM_DIS  := llvm-dis-22

# System paths for linking (x86-64 Linux)
CRT_DIR   := /usr/lib/x86_64-linux-gnu
LIB_DIRS  := -L/usr/lib/x86_64-linux-gnu -L/lib/x86_64-linux-gnu
DYNLINKER := /lib64/ld-linux-x86-64.so.2

MODULES := \
	lexer.c3       \
	ast.c3         \
	parser.c3      \
	resolve.c3     \
	typecheck.c3   \
	effectcheck.c3 \
	lint.c3        \
	integrity.c3   \
	ssi.c3         \
	ssi_ir.c3      \
	sasi.c3        \
	sasi_opt.c3    \
	rewrite.c3     \
	pgen.c3        \
	stage.c3       \
	irdl_msp.c3    \
	mono.c3        \
	codegen.c3     \
	pride.c3

.PHONY: all asan test conform redteam clean c3c runtime

all: c3c $(BINARY)

$(BINARY): $(MODULES)
	$(C3C) compile $(MODULES) -o $(BINARY)
	@chmod +x $(BINARY)
	@echo "Built: ./$(BINARY)"

asan: c3c $(MODULES)
	$(C3C) compile $(MODULES) --sanitize=address -O0 -o $(ASAN)
	@chmod +x $(ASAN)
	@echo "Built: ./$(ASAN)"

runtime: runtime/compiler_rt.c
	gcc -O2 -std=c11 -pthread -Wall -Wextra -fno-strict-aliasing \
	    -fPIC -c runtime/compiler_rt.c -o runtime/compiler_rt.o
	@echo "Built: runtime/compiler_rt.o"

test: all conform redteam

conform: all
	@echo "--- Conformance suite ---"
	@bash conformance/run.sh

redteam: all
	@echo "--- Red-team suite ---"
	@cd redteam && bash run.sh

clean:
	@rm -f $(BINARY) $(ASAN) *.ll *.bc *.o
	@rm -f runtime/compiler_rt.o
	@echo "Cleaned."

c3c:
	@if [ ! -x "$(C3C)" ]; then \
		echo "Fetching c3c $(C3C_VER)..."; \
		cd /tmp && curl -sSL --max-time 300 -o c3.tar.gz "$(C3C_URL)" && tar xzf c3.tar.gz; \
		echo "c3c ready: $(C3C)"; \
	fi

# ── Convenience: compile a .pry file all the way to a native binary ───────────
# Usage: make run SRC=hello.pry OUT=hello
SRC  ?= main.pry
OUT  ?= a.out
OPTLEVEL ?= 2

%.ll: %.pry $(BINARY)
	./$(BINARY) --emit-llvm $@ $<

%.bc: %.ll
	$(LLVM_AS) $< -o $@

%.opt.bc: %.bc
	$(LLVM_OPT) -O$(OPTLEVEL) $< -o $@

%.o: %.opt.bc
	$(LLC) -filetype=obj -relocation-model=pic $< -o $@

compile: $(SRC:.pry=.o) runtime/compiler_rt.o
	$(LLD) \
	  $(CRT_DIR)/crt1.o $(CRT_DIR)/crti.o \
	  $< runtime/compiler_rt.o \
	  $(CRT_DIR)/crtn.o \
	  $(LIB_DIRS) -lc -lpthread -lm \
	  --dynamic-linker $(DYNLINKER) \
	  -o $(OUT)
	@echo "Built: $(OUT)"
