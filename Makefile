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
COQ_OUT_DIR = $(ROOT_DIR)/coq
C_OUT_DIR = $(ROOT_DIR)/c
IR_OUT_DIR = $(ROOT_DIR)/ir
TESTGEN_DIR=$(ROOT_DIR)/test-generation
TESTGEN_SAIL_SRC_DIR = $(TESTGEN_DIR)/src
TESTGEN_PATCH_DIR = $(TESTGEN_DIR)/patches

SAIL_SRCS += v8_base.sail
SAIL_SRCS += config.sail
SAIL_SRCS += sysops.sail
SAIL_SRCS += instrs.sail

SAIL_SRC_PATHS = $(addprefix $(SAIL_SRC_DIR)/,$(SAIL_SRCS))
TESTGEN_SAIL_SRC_PATHS = $(addprefix $(TESTGEN_SAIL_SRC_DIR)/,$(SAIL_SRCS))

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
TESTGEN_EXTRA_SAIL_SRC_PATHS = $(addprefix $(TESTGEN_SAIL_SRC_DIR)/,$(EXTRA_SAIL_SRCS))

SAIL_PRELUDE = prelude.sail builtins.sail
DECODE_PRE = decode_start.sail
DECODE_POST = decode_end.sail

STANDARD_SAILS = prelude.sail decode_start.sail decode_end.sail
STANDARD_SAIL_PATHS = $(addprefix $(SAIL_SRC_DIR)/,$(STANDARD_SAILS))
TESTGEN_STANDARD_SAIL_PATHS = $(addprefix $(TESTGEN_SAIL_SRC_DIR)/,$(STANDARD_SAILS))

OTHER_SAILS = builtins.sail elfmain.sail
OTHER_SAIL_PATHS = $(addprefix $(SAIL_SRC_DIR)/,$(OTHER_SAILS))
TESTGEN_OTHER_SAIL_PATHS = $(addprefix $(TESTGEN_SAIL_SRC_DIR)/,$(OTHER_SAILS))

ALL_SAILS = $(SAIL_PRELUDE) $(DECODE_PRE) $(SAIL_SRCS) $(EXTRA_SAIL_SRCS) $(EXTRA_GENERATED_SAIL_SRCS) $(DECODE_POST)

SAIL_FLAGS = -verbose 1 -memo_z3 -infer_effects -non_lexical_flow -no_warn
LEM_FLAGS = -undefined_gen -mono_rewrites -auto_mono -lem_mwords -grouped_regstate
SAIL_C_FLAGS = -O -Oconstant_fold
MUTREC_FLAGS = -const_prop_mutrec AArch64_TakeException -const_prop_mutrec AArch32_SecondStageTranslate -const_prop_mutrec AArch64_SecondStageTranslate

LEM_SAIL_EXTRA_FLAGS = -splice patches/translation_stubs.sail -splice patches/unknown_capability.sail -splice patches/write_tag.sail -lem_lib Morello_bindings
COQ_SAIL_EXTRA_FLAGS = -splice patches/translation_stubs.sail -splice patches/unknown_capability.sail -splice patches/write_tag_coq.sail

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

$(COQ_OUT_DIR)/morello.v: $(SAIL_SRC_PATHS)
	mkdir -p $(COQ_OUT_DIR)
	cp $(ASL2SAIL_DIR)/arm_extras.v $(COQ_OUT_DIR)
	cd $(SAIL_SRC_DIR); $(SAIL) -coq -undefined_gen -coq_lib arm_extras -o morello -coq_output_dir $(COQ_OUT_DIR) $(SAIL_FLAGS) $(SAIL_EXTRA_FLAGS) $(COQ_SAIL_EXTRA_FLAGS) $(MUTREC_FLAGS) $(ALL_SAILS) coq_termination.sail

gen_coq: $(COQ_OUT_DIR)/morello.v

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

$(IR_OUT_DIR)/morello.ir: $(SAIL_SRC_PATHS) $(SAIL_SRC_DIR)/elfmain.sail $(SAIL_SRC_DIR)/isla-splice.sail
	mkdir -p $(IR_OUT_DIR)
	cd $(SAIL_SRC_DIR); $(ISLA_SAIL) -v 1 -mono_rewrites $(ALL_SAILS) elfmain.sail -splice $(SAIL_SRC_DIR)/isla-splice.sail -o $(IR_OUT_DIR)/morello

gen_ir: $(IR_OUT_DIR)/morello.ir

TESTGEN_ALL_SAIL=$(TESTGEN_SAIL_SRC_PATHS) $(TESTGEN_EXTRA_SAIL_SRC_PATHS) $(TESTGEN_STANDARD_SAIL_PATHS) $(TESTGEN_OTHER_SAIL_PATHS)
TESTGEN_PATCHES += mono_instr.patch post_instruction_PCC_check.patch no_high_vaddrs.patch exclusives.patch
TESTGEN_PATCH_PATHS = $(addprefix $(TESTGEN_PATCH_DIR)/,$(TESTGEN_PATCHES))

# Use a timestamp file to ensure that patch failure isn't ignored
$(TESTGEN_ALL_SAIL) $(TESTGEN_DIR)/src.stamp: $(SAIL_SRC_PATHS) $(EXTRA_SAIL_SRC_PATHS) $(STANDARD_SAIL_PATHS) $(TESTGEN_PATCH_PATHS) $(OTHER_SAIL_PATHS)
	mkdir -p $(TESTGEN_SAIL_SRC_DIR)
	cp $(SAIL_SRC_PATHS) $(TESTGEN_SAIL_SRC_DIR)
	cp $(EXTRA_SAIL_SRC_PATHS) $(TESTGEN_SAIL_SRC_DIR)
	cp $(STANDARD_SAIL_PATHS) $(TESTGEN_SAIL_SRC_DIR)
	cp $(OTHER_SAIL_PATHS) $(TESTGEN_SAIL_SRC_DIR)
	cd $(TESTGEN_SAIL_SRC_DIR); \
	for PATCH in $(TESTGEN_PATCH_PATHS); do \
	  patch -p1 < $$PATCH; \
	done
	touch $(TESTGEN_DIR)/src.stamp

$(TESTGEN_DIR)/morello-testgen.ir: $(TESTGEN_DIR)/src.stamp $(SAIL_SRC_DIR)/isla-splice.sail
	cd $(TESTGEN_SAIL_SRC_DIR); $(ISLA_SAIL) -v 1 -mono_rewrites $(ALL_SAILS) elfmain.sail -splice $(SAIL_SRC_DIR)/isla-splice.sail -o $(TESTGEN_DIR)/morello-testgen

gen_testgen: $(TESTGEN_DIR)/morello-testgen.ir

clean:
	rm -f $(LEM_OUT_DIR)/morello.lem $(LEM_OUT_DIR)/morello_types.lem
	rm -f $(ISA_OUT_DIR)/Morello_types.thy $(ISA_OUT_DIR)/Morello.thy $(ISA_OUT_DIR)/Morello_lemmas.thy $(ISA_OUT_DIR)/ROOT
	rm -f $(COQ_OUT_DIR)/morello.v $(COQ_OUT_DIR)/morello_types.v
	rm -f $(C_OUT_DIR)/morello.c $(C_OUT_DIR)/morello $(C_OUT_DIR)/morello_coverage.c $(C_OUT_DIR)/morello_coverage
	rm -f $(IR_OUT_DIR)/morello.ir
	rm -f $(TESTGEN_ALL_SAIL) $(TESTGEN_DIR)/morello-testgen.ir $(TESTGEN_DIR)/src.stamp
