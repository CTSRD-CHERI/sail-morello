ASLI = asli
ASL2SAIL = $(realpath $(shell which asl_to_sail))
ASL2SAIL_DIR = $(dir $(ASL2SAIL))

ifeq ($(ASL2SAIL),)
$(warning Unable to find asl_to_sail)
endif

# Attempt to work with either sail from opam or built from repo in SAIL_DIR
ifneq ($(SAIL_DIR),)
# Use sail repo in SAIL_DIR
SAIL:=$(SAIL_DIR)/sail
export SAIL_DIR
else
# Use sail from opam package
SAIL_DIR:=$(shell opam config var sail:share)
SAIL:=sail
endif
SAIL_LIB_DIR:=$(SAIL_DIR)/lib
export SAIL_LIB_DIR

LEM = lem
SED = sed

ISLA_SAIL=isla-sail

ROOT_DIR = $(realpath .)
SAIL_SRC_DIR = $(ROOT_DIR)/src
LEM_OUT_DIR = $(ROOT_DIR)/lem
ISA_OUT_DIR = $(ROOT_DIR)/isabelle
HOL_OUT_DIR = $(ROOT_DIR)/hol4
C_OUT_DIR = $(ROOT_DIR)/c
IR_OUT_DIR = $(ROOT_DIR)/ir

SAIL_SRCS += v8_base.sail
SAIL_SRCS += config.sail
SAIL_SRCS += sysops.sail
SAIL_SRCS += instrs.sail

SAIL_SRC_PATHS = $(addprefix $(SAIL_SRC_DIR)/,$(SAIL_SRCS))

DEVICES = no_devices.sail

EXTRA_SAIL_SRCS += $(DEVICES)
EXTRA_SAIL_SRCS += mem.sail
EXTRA_SAIL_SRCS += impdefs.sail
EXTRA_SAIL_SRCS += interrupts.sail
EXTRA_SAIL_SRCS += fetch.sail
EXTRA_SAIL_SRCS += step.sail
EXTRA_SAIL_SRCS += map_clauses.sail
EXTRA_SAIL_SRCS += event_clauses.sail
EXTRA_SAIL_SRCS += stubs.sail
EXTRA_SAIL_SRC_PATHS = $(addprefix $(SAIL_SRC_DIR)/,$(EXTRA_SAIL_SRCS))

SAIL_PRELUDE = prelude.sail builtins.sail
DECODE_PRE = decode_start.sail
DECODE_POST = decode_end.sail

STANDARD_SAILS = prelude.sail decode_start.sail decode_end.sail
STANDARD_SAIL_PATHS = $(addprefix $(SAIL_SRC_DIR)/,$(STANDARD_SAILS))

ALL_SAILS = $(SAIL_PRELUDE) $(DECODE_PRE) $(SAIL_SRCS) $(EXTRA_SAIL_SRCS) $(EXTRA_GENERATED_SAIL_SRCS) $(DECODE_POST)

SAIL_FLAGS = -verbose 1 -memo_z3 -infer_effects -non_lexical_flow -no_warn
LEM_FLAGS = -undefined_gen -mono_rewrites -auto_mono -lem_mwords -grouped_regstate
SAIL_C_FLAGS = -O -Oconstant_fold
MUTREC_FLAGS = -const_prop_mutrec AArch64_TakeException -const_prop_mutrec AArch32_SecondStageTranslate -const_prop_mutrec AArch64_SecondStageTranslate

LEM_SAIL_EXTRA_FLAGS = -splice patches/translation_stubs.sail -splice patches/unknown_capability.sail -splice patches/write_tag.sail -lem_lib Morello_bindings

check_sail: $(SAIL_SRC_PATHS)
	cd $(SAIL_SRC_DIR); $(SAIL) $(SAIL_FLAGS) $(SAIL_EXTRA_FLAGS) $(ALL_SAILS)

isail: $(SAIL_SRC_PATHS)
	cd $(SAIL_SRC_DIR); $(SAIL) -i $(SAIL_FLAGS) $(ALL_SAILS)

$(LEM_OUT_DIR)/morello.lem: $(SAIL_SRC_PATHS)
	mkdir -p $(LEM_OUT_DIR)
	mkdir -p $(ISA_OUT_DIR)
	cd $(SAIL_SRC_DIR); $(SAIL) -lem -lem_lib Prelude -o morello -lem_output_dir $(LEM_OUT_DIR) -isa_output_dir $(ISA_OUT_DIR) $(SAIL_FLAGS) $(SAIL_EXTRA_FLAGS) $(LEM_SAIL_EXTRA_FLAGS) $(LEM_FLAGS) $(MUTREC_FLAGS) $(ALL_SAILS)
	# Add prelude import for bitvector size types
	sed -i '/open import Sail2_prompt_monad/a open import Prelude' $(LEM_OUT_DIR)/morello_types.lem

gen_lem: $(LEM_OUT_DIR)/morello.lem

$(ISA_OUT_DIR)/Morello.thy: $(LEM_OUT_DIR)/morello.lem $(SAIL_SRC_DIR)/lem/morello_bindings.lem $(ASL2SAIL_DIR)/prelude.lem
	mkdir -p $(ISA_OUT_DIR)
	cp $(ASL2SAIL_DIR)/prelude.lem $(LEM_OUT_DIR)
	$(LEM) -isa -outdir $(ISA_OUT_DIR) -lib Sail=$(SAIL_DIR)/src/gen_lib $(LEM_EXTRA_FLAGS) $(LEM_OUT_DIR)/prelude.lem $(LEM_OUT_DIR)/morello_types.lem $(SAIL_SRC_DIR)/lem/morello_bindings.lem $(LEM_OUT_DIR)/morello.lem

$(ISA_OUT_DIR)/ROOT: etc/ROOT
	mkdir -p $(ISA_OUT_DIR)
	cp etc/ROOT $(ISA_OUT_DIR)

gen_isa: $(ISA_OUT_DIR)/Morello.thy $(ISA_OUT_DIR)/ROOT

$(C_OUT_DIR)/morello.c: $(SAIL_SRC_PATHS) $(SAIL_SRC_DIR)/elfmain.sail
	mkdir -p $(C_OUT_DIR)
	cd $(SAIL_SRC_DIR); $(SAIL) -c $(SAIL_C_FLAGS) $(SAIL_FLAGS) $(SAIL_EXTRA_FLAGS) $(ALL_SAILS) elfmain.sail > $(C_OUT_DIR)/morello.c.temp
	mv $(C_OUT_DIR)/morello.c.temp $(C_OUT_DIR)/morello.c

$(C_OUT_DIR)/morello: $(C_OUT_DIR)/morello.c
	gcc -O2 -g -DHAVE_SETCONFIG $(C_OUT_DIR)/morello.c $(SAIL_DIR)/lib/*.c -lgmp -lz -I $(SAIL_DIR)/lib/ -o $(C_OUT_DIR)/morello

$(C_OUT_DIR)/morello_coverage.c: $(SAIL_SRC_PATHS) $(SAIL_SRC_DIR)/elfmain.sail
	mkdir -p $(C_OUT_DIR)
	cd $(SAIL_SRC_DIR); $(SAIL) -c -c_coverage $(C_OUT_DIR)/all_branches $(SAIL_C_FLAGS) $(SAIL_FLAGS) $(SAIL_EXTRA_FLAGS) $(ALL_SAILS) elfmain.sail > $(C_OUT_DIR)/morello_coverage.c.temp
	mv $(C_OUT_DIR)/morello_coverage.c.temp $(C_OUT_DIR)/morello_coverage.c

$(C_OUT_DIR)/morello_coverage: $(C_OUT_DIR)/morello_coverage.c
	gcc -O2 -DHAVE_SETCONFIG $(C_OUT_DIR)/morello_coverage.c $(SAIL_DIR)/lib/*.c -lgmp -lz -I $(SAIL_DIR)/lib/ -L ../sail/lib/coverage/ -lsail_coverage -lpthread -ldl -o $(C_OUT_DIR)/morello_coverage

gen_c: $(C_OUT_DIR)/morello
gen_c_coverage: $(C_OUT_DIR)/morello_coverage

$(IR_OUT_DIR)/morello.ir: $(SAIL_SRC_PATHS) $(SAIL_SRC_DIR)/elfmain.sail
	mkdir -p $(IR_OUT_DIR)
	cd $(SAIL_SRC_DIR); $(ISLA_SAIL) -v 1 -mono_rewrites $(ALL_SAILS) elfmain.sail -o $(IR_OUT_DIR)/morello

gen_ir: $(IR_OUT_DIR)/morello.ir

clean:
	rm -f $(LEM_OUT_DIR)/morello.lem $(LEM_OUT_DIR)/morello_types.lem
	rm -f $(ISA_OUT_DIR)/Morello_types.thy $(ISA_OUT_DIR)/Morello.thy $(ISA_OUT_DIR)/Morello_lemmas.thy $(ISA_OUT_DIR)/ROOT
	rm -f $(C_OUT_DIR)/morello.c $(C_OUT_DIR)/morello $(C_OUT_DIR)/morello_coverage.c $(C_OUT_DIR)/morello_coverage
	rm -f $(IR_OUT_DIR)/morello.ir
