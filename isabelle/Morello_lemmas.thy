theory Morello_lemmas
  imports
    Sail.Sail2_values_lemmas
    Sail.Sail2_state_lemmas
    Morello
begin

lemma registers_distinct:
  "distinct (map fst registers)"
  unfolding registers_def list.simps fst_conv
  by (distinct_string; simp)

lemma registers_eqs_setup:
  "!x : set registers. map_of registers (fst x) = Some (snd x)"
  using registers_distinct
  by simp

lemmas map_of_registers_eqs[simp] =
    registers_eqs_setup[simplified arg_cong[where f=set, OF registers_def]
        list.simps ball_simps fst_conv snd_conv]

lemmas get_regval_unfold = get_regval_def[THEN fun_cong,
    unfolded register_accessors_def mk_accessors_def fst_conv snd_conv]
lemmas set_regval_unfold = set_regval_def[THEN fun_cong,
    unfolded register_accessors_def mk_accessors_def fst_conv snd_conv]

abbreviation liftS ("\<lbrakk>_\<rbrakk>\<^sub>S") where "liftS \<equiv> liftState (get_regval, set_regval)"

lemmas register_defs = get_regval_unfold set_regval_unfold highest_el_aarch32_ref_def
  ThisInstrAbstract_ref_def ThisInstrEnc_ref_def CNTControlBase_ref_def EventRegister_ref_def
  saved_exception_level_ref_def SP_EL3_ref_def V_ref_def PMSWINC_EL0_ref_def OSLAR_EL1_ref_def
  ICC_SGI1R_EL1_ref_def ICC_SGI0R_EL1_ref_def ICV_EOIR1_EL1_ref_def ICC_EOIR1_EL1_ref_def
  ICV_EOIR0_EL1_ref_def ICC_EOIR0_EL1_ref_def ICV_DIR_EL1_ref_def ICC_DIR_EL1_ref_def
  ICC_ASGI1R_EL1_ref_def DBGDTRTX_EL0_ref_def RDDC_EL0_ref_def DDC_EL3_ref_def DDC_EL2_ref_def
  DDC_EL1_ref_def DDC_EL0_ref_def VTTBR_EL2_ref_def VTCR_EL2_ref_def VSESR_EL2_ref_def
  TTBR1_EL2_ref_def TTBR1_EL1_ref_def TTBR0_EL3_ref_def TTBR0_EL2_ref_def TTBR0_EL1_ref_def
  TPIDR_EL3_ref_def TPIDR_EL2_ref_def TPIDR_EL1_ref_def TPIDR_EL0_ref_def TPIDRRO_EL0_ref_def
  SP_EL2_ref_def SP_EL1_ref_def SP_EL0_ref_def SPSR_und_ref_def SPSR_irq_ref_def SPSR_fiq_ref_def
  SPSR_abt_ref_def SDER32_EL3_ref_def SCXTNUM_EL3_ref_def SCXTNUM_EL2_ref_def SCXTNUM_EL1_ref_def
  CID_EL0_ref_def S3_op1_Cn_Cm_op2_ref_def RVBAR_EL3_ref_def RVBAR_EL2_ref_def RVBAR_EL1_ref_def
  RTPIDR_EL0_ref_def RSP_EL0_ref_def RMR_EL3_ref_def RMR_EL2_ref_def RMR_EL1_ref_def
  REVIDR_EL1_ref_def PMXEVTYPER_EL0_ref_def PMXEVCNTR_EL0_ref_def PMSLATFR_EL1_ref_def
  PMSIRR_EL1_ref_def PMSIDR_EL1_ref_def PMSICR_EL1_ref_def PMSFCR_EL1_ref_def PMSEVFR_EL1_ref_def
  PMSELR_EL0_ref_def PMSCR_EL2_ref_def PMSCR_EL1_ref_def PMOVSSET_EL0_ref_def PMOVSCLR_EL0_ref_def
  PMINTENSET_EL1_ref_def PMINTENCLR_EL1_ref_def PMEVTYPER_EL0_ref_def PMEVCNTR_EL0_ref_def
  PMCR_EL0_ref_def PMCNTENSET_EL0_ref_def PMCNTENCLR_EL0_ref_def PMCEID1_EL0_ref_def
  PMCEID0_EL0_ref_def PMCCNTR_EL0_ref_def PMUSERENR_EL0_ref_def PMCCFILTR_EL0_ref_def
  PMBSR_EL1_ref_def PMBPTR_EL1_ref_def PMBLIMITR_EL1_ref_def PMBIDR_EL1_ref_def PAR_EL1_ref_def
  OSECCR_EL1_ref_def OSDTRTX_EL1_ref_def OSDTRRX_EL1_ref_def MVFR2_EL1_ref_def MVFR1_EL1_ref_def
  MVFR0_EL1_ref_def VMPIDR_EL2_ref_def MPIDR_EL1_ref_def MPAMVPMV_EL2_ref_def MPAMVPM7_EL2_ref_def
  MPAMVPM6_EL2_ref_def MPAMVPM5_EL2_ref_def MPAMVPM4_EL2_ref_def MPAMVPM3_EL2_ref_def
  MPAMVPM2_EL2_ref_def MPAMVPM1_EL2_ref_def MPAMVPM0_EL2_ref_def MPAMIDR_EL1_ref_def
  MPAMHCR_EL2_ref_def MPAM1_EL1_0_62_ref_def MPAM2_EL2_0_62_ref_def MPAM3_EL3_ref_def
  MPAM0_EL1_ref_def VPIDR_EL2_ref_def MIDR_EL1_ref_def MDRAR_EL1_ref_def MDCCSR_EL0_ref_def
  MDCCINT_EL1_ref_def MAIR_EL3_ref_def MAIR_EL2_ref_def MAIR_EL1_ref_def LORSA_EL1_ref_def
  LORN_EL1_ref_def LORID_EL1_ref_def LOREA_EL1_ref_def LORC_EL1_ref_def ISR_EL1_ref_def
  IFSR32_EL2_ref_def ID_PFR2_EL1_ref_def ID_PFR1_EL1_ref_def ID_PFR0_EL1_ref_def
  ID_MMFR5_EL1_ref_def ID_MMFR4_EL1_ref_def ID_MMFR3_EL1_ref_def ID_MMFR2_EL1_ref_def
  ID_MMFR1_EL1_ref_def ID_MMFR0_EL1_ref_def ID_ISAR6_EL1_ref_def ID_ISAR5_EL1_ref_def
  ID_ISAR4_EL1_ref_def ID_ISAR3_EL1_ref_def ID_ISAR2_EL1_ref_def ID_ISAR1_EL1_ref_def
  ID_ISAR0_EL1_ref_def ID_DFR0_EL1_ref_def ID_AFR0_EL1_ref_def ID_AA64ZFR0_EL1_ref_def
  ID_AA64PFR1_EL1_ref_def ID_AA64PFR0_EL1_ref_def ID_AA64MMFR2_EL1_ref_def ID_AA64MMFR1_EL1_ref_def
  ID_AA64MMFR0_EL1_ref_def ID_AA64ISAR1_EL1_ref_def ID_AA64ISAR0_EL1_ref_def ID_AA64DFR1_EL1_ref_def
  ID_AA64DFR0_EL1_ref_def ID_AA64AFR1_EL1_ref_def ID_AA64AFR0_EL1_ref_def ICH_VTR_EL2_ref_def
  ICH_VMCR_EL2_ref_def ICH_MISR_EL2_ref_def ICH_LR_EL2_ref_def ICH_ELRSR_EL2_ref_def
  ICH_EISR_EL2_ref_def ICH_AP1R_EL2_ref_def ICH_AP0R_EL2_ref_def ICV_RPR_EL1_ref_def
  ICC_RPR_EL1_ref_def ICV_PMR_EL1_ref_def ICC_PMR_EL1_ref_def ICC_IGRPEN1_EL3_ref_def
  ICV_IGRPEN1_EL1_ref_def ICC_IGRPEN1_EL1_S_ref_def ICC_IGRPEN1_EL1_NS_ref_def
  ICV_IGRPEN0_EL1_ref_def ICC_IGRPEN0_EL1_ref_def ICV_IAR1_EL1_ref_def ICC_IAR1_EL1_ref_def
  ICV_IAR0_EL1_ref_def ICC_IAR0_EL1_ref_def ICV_HPPIR1_EL1_ref_def ICC_HPPIR1_EL1_ref_def
  ICV_HPPIR0_EL1_ref_def ICC_HPPIR0_EL1_ref_def ICC_CTLR_EL3_ref_def ICV_CTLR_EL1_ref_def
  ICC_CTLR_EL1_S_ref_def ICC_CTLR_EL1_NS_ref_def ICV_BPR1_EL1_ref_def ICC_BPR1_EL1_S_ref_def
  ICC_BPR1_EL1_NS_ref_def ICV_BPR0_EL1_ref_def ICC_BPR0_EL1_ref_def ICV_AP1R_EL1_ref_def
  ICC_AP1R_EL1_S_ref_def ICC_AP1R_EL1_NS_ref_def ICC_AP1R_EL1_ref_def ICV_AP0R_EL1_ref_def
  ICH_HCR_EL2_ref_def ICC_SRE_EL3_ref_def ICC_SRE_EL2_ref_def ICC_SRE_EL1_S_ref_def
  ICC_SRE_EL1_NS_ref_def ICC_AP0R_EL1_ref_def HSTR_EL2_ref_def HACR_EL2_ref_def FPSR_ref_def
  FPEXC32_EL2_ref_def FPCR_ref_def ERXSTATUS_EL1_ref_def ERXMISC1_EL1_ref_def ERXMISC0_EL1_ref_def
  ERXFR_EL1_ref_def ERXCTLR_EL1_ref_def ERXADDR_EL1_ref_def ERRSELR_EL1_ref_def ERRIDR_EL1_ref_def
  VDISR_EL2_ref_def DISR_EL1_ref_def DCZID_EL0_ref_def DBGWVR_EL1_ref_def DBGWCR_EL1_ref_def
  DBGVCR32_EL2_ref_def CDBGDTR_EL0_ref_def MDSCR_EL1_ref_def DBGDTRRX_EL0_ref_def
  DBGCLAIMSET_EL1_ref_def DBGCLAIMCLR_EL1_ref_def DBGBVR_EL1_ref_def OSLSR_EL1_ref_def
  OSDLR_EL1_ref_def DBGPRCR_EL1_ref_def SPIDEN_ref_def DBGEN_ref_def DSPSR_EL0_ref_def
  CDLR_EL0_ref_def DBGBCR_EL1_ref_def MDCR_EL3_ref_def MDCR_EL2_ref_def DBGAUTHSTATUS_EL1_ref_def
  DACR32_EL2_ref_def CTR_EL0_ref_def CSSELR_EL1_ref_def CSCR_EL3_ref_def CONTEXTIDR_EL2_ref_def
  CONTEXTIDR_EL1_ref_def CNTV_TVAL_EL0_ref_def CNTV_CVAL_EL0_ref_def CNTV_CTL_EL0_ref_def
  CNTVOFF_EL2_ref_def CNTVCT_EL0_ref_def CNTP_TVAL_EL0_ref_def CNTP_CVAL_EL0_ref_def
  CNTP_CTL_EL0_ref_def CNTPS_TVAL_EL1_ref_def CNTPS_CVAL_EL1_ref_def CNTPS_CTL_EL1_ref_def
  CNTPCT_EL0_ref_def CNTHV_TVAL_EL2_ref_def CNTHV_CVAL_EL2_ref_def CNTHV_CTL_EL2_ref_def
  CNTHP_TVAL_EL2_ref_def CNTHP_CVAL_EL2_ref_def CNTHP_CTL_EL2_ref_def CNTKCTL_EL1_ref_def
  CNTHCTL_EL2_ref_def CNTFRQ_EL0_ref_def CLIDR_EL1_ref_def CHCR_EL2_ref_def CCSIDR_EL1_ref_def
  AMAIR_EL3_ref_def AMAIR_EL2_ref_def AMAIR_EL1_ref_def AIDR_EL1_ref_def AFSR1_EL3_ref_def
  AFSR1_EL2_ref_def AFSR1_EL1_ref_def AFSR0_EL3_ref_def AFSR0_EL2_ref_def AFSR0_EL1_ref_def
  ACTLR_EL3_ref_def ACTLR_EL2_ref_def ACTLR_EL1_ref_def SPSR_EL3_ref_def SPSR_EL2_ref_def
  SPSR_EL1_ref_def SCTLR_EL3_ref_def SCTLR_EL2_ref_def SCTLR_EL1_ref_def EDSCR_ref_def
  CPTR_EL3_ref_def CPTR_EL2_ref_def CPACR_EL1_ref_def VBAR_EL3_ref_def VBAR_EL2_ref_def
  VBAR_EL1_ref_def ELR_EL3_ref_def ELR_EL2_ref_def ELR_EL1_ref_def CCTLR_EL3_ref_def
  CCTLR_EL2_ref_def CCTLR_EL1_ref_def CCTLR_EL0_ref_def BranchTaken_ref_def PC_ref_def
  TCR_EL3_ref_def TCR_EL2_ref_def TCR_EL1_ref_def HPFAR_EL2_ref_def FAR_EL3_ref_def FAR_EL2_ref_def
  FAR_EL1_ref_def ESR_EL3_ref_def ESR_EL2_ref_def ESR_EL1_ref_def R30_ref_def R29_ref_def
  R28_ref_def R27_ref_def R26_ref_def R25_ref_def R24_ref_def R23_ref_def R22_ref_def R21_ref_def
  R20_ref_def R19_ref_def R18_ref_def R17_ref_def R16_ref_def R15_ref_def R14_ref_def R13_ref_def
  R12_ref_def R11_ref_def R10_ref_def R09_ref_def R08_ref_def R07_ref_def R06_ref_def R05_ref_def
  R04_ref_def R03_ref_def R02_ref_def R01_ref_def R00_ref_def ThisInstr_ref_def PSTATE_ref_def
  HCR_EL2_ref_def SCR_EL3_ref_def CNTHVS_TVAL_EL2_ref_def CNTHVS_CVAL_EL2_ref_def
  CNTHVS_CTL_EL2_ref_def CNTHPS_TVAL_EL2_ref_def CNTHPS_CVAL_EL2_ref_def CNTHPS_CTL_EL2_ref_def
  PCC_ref_def SEE_ref_def

lemma bool_of_register_value_eq_Some_iff[simp]:
  "bool_of_register_value rv = Some v \<longleftrightarrow> rv = Regval_bool v"
  by (cases rv; auto)

declare register_value_of_bool_def[simp]

lemma regval_bool[simp]:
  "bool_of_register_value (register_value_of_bool v) = Some v"
  by auto

lemma int_of_register_value_eq_Some_iff[simp]:
  "int_of_register_value rv = Some v \<longleftrightarrow> rv = Regval_int v"
  by (cases rv; auto)

declare register_value_of_int_def[simp]

lemma regval_int[simp]:
  "int_of_register_value (register_value_of_int v) = Some v"
  by auto

lemma real_of_register_value_eq_Some_iff[simp]:
  "real_of_register_value rv = Some v \<longleftrightarrow> rv = Regval_real v"
  by (cases rv; auto)

declare register_value_of_real_def[simp]

lemma regval_real[simp]:
  "real_of_register_value (register_value_of_real v) = Some v"
  by auto

lemma string_of_register_value_eq_Some_iff[simp]:
  "string_of_register_value rv = Some v \<longleftrightarrow> rv = Regval_string v"
  by (cases rv; auto)

declare register_value_of_string_def[simp]

lemma regval_string[simp]:
  "string_of_register_value (register_value_of_string v) = Some v"
  by auto

lemma ProcState_of_regval_eq_Some_iff[simp]:
  "ProcState_of_regval rv = Some v \<longleftrightarrow> rv = Regval_ProcState v"
  by (cases rv; auto)

declare regval_of_ProcState_def[simp]

lemma regval_ProcState[simp]:
  "ProcState_of_regval (regval_of_ProcState v) = Some v"
  by auto

lemma InstrEnc_of_regval_eq_Some_iff[simp]:
  "InstrEnc_of_regval rv = Some v \<longleftrightarrow> rv = Regval___InstrEnc v"
  by (cases rv; auto)

declare regval_of___InstrEnc_def[simp]

lemma regval___InstrEnc[simp]:
  "InstrEnc_of_regval (regval_of___InstrEnc v) = Some v"
  by auto

lemma bit_of_regval_eq_Some_iff[simp]:
  "bit_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bit v"
  by (cases rv; auto)

declare regval_of_bit_def[simp]

lemma regval_bit[simp]:
  "bit_of_regval (regval_of_bit v) = Some v"
  by auto

lemma bitvector_128_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_128_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_128_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_128_dec_def[simp]

lemma regval_bitvector_128_dec[simp]:
  "bitvector_128_dec_of_regval (regval_of_bitvector_128_dec v) = Some v"
  by auto

lemma bitvector_129_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_129_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_129_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_129_dec_def[simp]

lemma regval_bitvector_129_dec[simp]:
  "bitvector_129_dec_of_regval (regval_of_bitvector_129_dec v) = Some v"
  by auto

lemma bitvector_1_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_1_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_1_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_1_dec_def[simp]

lemma regval_bitvector_1_dec[simp]:
  "bitvector_1_dec_of_regval (regval_of_bitvector_1_dec v) = Some v"
  by auto

lemma bitvector_2_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_2_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_2_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_2_dec_def[simp]

lemma regval_bitvector_2_dec[simp]:
  "bitvector_2_dec_of_regval (regval_of_bitvector_2_dec v) = Some v"
  by auto

lemma bitvector_32_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_32_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_32_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_32_dec_def[simp]

lemma regval_bitvector_32_dec[simp]:
  "bitvector_32_dec_of_regval (regval_of_bitvector_32_dec v) = Some v"
  by auto

lemma bitvector_48_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_48_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_48_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_48_dec_def[simp]

lemma regval_bitvector_48_dec[simp]:
  "bitvector_48_dec_of_regval (regval_of_bitvector_48_dec v) = Some v"
  by auto

lemma bitvector_63_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_63_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_63_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_63_dec_def[simp]

lemma regval_bitvector_63_dec[simp]:
  "bitvector_63_dec_of_regval (regval_of_bitvector_63_dec v) = Some v"
  by auto

lemma bitvector_64_dec_of_regval_eq_Some_iff[simp]:
  "bitvector_64_dec_of_regval rv = Some v \<longleftrightarrow> rv = Regval_bitvector_64_dec v"
  by (cases rv; auto)

declare regval_of_bitvector_64_dec_def[simp]

lemma regval_bitvector_64_dec[simp]:
  "bitvector_64_dec_of_regval (regval_of_bitvector_64_dec v) = Some v"
  by auto

lemma instr_ast_of_regval_eq_Some_iff[simp]:
  "instr_ast_of_regval rv = Some v \<longleftrightarrow> rv = Regval_instr_ast v"
  by (cases rv; auto)

declare regval_of_instr_ast_def[simp]

lemma regval_instr_ast[simp]:
  "instr_ast_of_regval (regval_of_instr_ast v) = Some v"
  by auto

lemma signal_of_regval_eq_Some_iff[simp]:
  "signal_of_regval rv = Some v \<longleftrightarrow> rv = Regval_signal v"
  by (cases rv; auto)

declare regval_of_signal_def[simp]

lemma regval_signal[simp]:
  "signal_of_regval (regval_of_signal v) = Some v"
  by auto

lemma vector_of_rv_rv_of_vector[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "vector_of_regval of_rv (regval_of_vector rv_of v) = Some v"
proof -
  from assms have "of_rv \<circ> rv_of = Some" by auto
  then show ?thesis by (auto simp: regval_of_vector_def)
qed

lemma option_of_rv_rv_of_option[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "option_of_regval of_rv (regval_of_option rv_of v) = Some v"
  using assms by (cases v) (auto simp: regval_of_option_def)

lemma list_of_rv_rv_of_list[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "list_of_regval of_rv (regval_of_list rv_of v) = Some v"
proof -
  from assms have "of_rv \<circ> rv_of = Some" by auto
  with assms show ?thesis by (induction v) (auto simp: regval_of_list_def)
qed

lemma liftS_read_reg_highest_el_aarch32[liftState_simp]:
  "\<lbrakk>read_reg highest_el_aarch32_ref\<rbrakk>\<^sub>S = read_regS highest_el_aarch32_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_highest_el_aarch32[liftState_simp]:
  "\<lbrakk>write_reg highest_el_aarch32_ref v\<rbrakk>\<^sub>S = write_regS highest_el_aarch32_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ThisInstrAbstract[liftState_simp]:
  "\<lbrakk>read_reg ThisInstrAbstract_ref\<rbrakk>\<^sub>S = read_regS ThisInstrAbstract_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ThisInstrAbstract[liftState_simp]:
  "\<lbrakk>write_reg ThisInstrAbstract_ref v\<rbrakk>\<^sub>S = write_regS ThisInstrAbstract_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ThisInstrEnc[liftState_simp]:
  "\<lbrakk>read_reg ThisInstrEnc_ref\<rbrakk>\<^sub>S = read_regS ThisInstrEnc_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ThisInstrEnc[liftState_simp]:
  "\<lbrakk>write_reg ThisInstrEnc_ref v\<rbrakk>\<^sub>S = write_regS ThisInstrEnc_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTControlBase[liftState_simp]:
  "\<lbrakk>read_reg CNTControlBase_ref\<rbrakk>\<^sub>S = read_regS CNTControlBase_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTControlBase[liftState_simp]:
  "\<lbrakk>write_reg CNTControlBase_ref v\<rbrakk>\<^sub>S = write_regS CNTControlBase_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EventRegister[liftState_simp]:
  "\<lbrakk>read_reg EventRegister_ref\<rbrakk>\<^sub>S = read_regS EventRegister_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EventRegister[liftState_simp]:
  "\<lbrakk>write_reg EventRegister_ref v\<rbrakk>\<^sub>S = write_regS EventRegister_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_saved_exception_level[liftState_simp]:
  "\<lbrakk>read_reg saved_exception_level_ref\<rbrakk>\<^sub>S = read_regS saved_exception_level_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_saved_exception_level[liftState_simp]:
  "\<lbrakk>write_reg saved_exception_level_ref v\<rbrakk>\<^sub>S = write_regS saved_exception_level_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SP_EL3[liftState_simp]:
  "\<lbrakk>read_reg SP_EL3_ref\<rbrakk>\<^sub>S = read_regS SP_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SP_EL3[liftState_simp]:
  "\<lbrakk>write_reg SP_EL3_ref v\<rbrakk>\<^sub>S = write_regS SP_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_V[liftState_simp]:
  "\<lbrakk>read_reg V_ref\<rbrakk>\<^sub>S = read_regS V_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_V[liftState_simp]:
  "\<lbrakk>write_reg V_ref v\<rbrakk>\<^sub>S = write_regS V_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSWINC_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMSWINC_EL0_ref\<rbrakk>\<^sub>S = read_regS PMSWINC_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSWINC_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMSWINC_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMSWINC_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_OSLAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSLAR_EL1_ref\<rbrakk>\<^sub>S = read_regS OSLAR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_OSLAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSLAR_EL1_ref v\<rbrakk>\<^sub>S = write_regS OSLAR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_SGI1R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_SGI1R_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_SGI1R_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_SGI1R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_SGI1R_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_SGI1R_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_SGI0R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_SGI0R_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_SGI0R_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_SGI0R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_SGI0R_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_SGI0R_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_EOIR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_EOIR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_EOIR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_EOIR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_EOIR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_EOIR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_EOIR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_EOIR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_EOIR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_EOIR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_EOIR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_EOIR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_EOIR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_EOIR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_EOIR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_EOIR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_EOIR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_EOIR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_EOIR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_EOIR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_EOIR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_EOIR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_EOIR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_EOIR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_DIR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_DIR_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_DIR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_DIR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_DIR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_DIR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_DIR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_DIR_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_DIR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_DIR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_DIR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_DIR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_ASGI1R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_ASGI1R_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_ASGI1R_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_ASGI1R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_ASGI1R_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_ASGI1R_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGDTRTX_EL0[liftState_simp]:
  "\<lbrakk>read_reg DBGDTRTX_EL0_ref\<rbrakk>\<^sub>S = read_regS DBGDTRTX_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGDTRTX_EL0[liftState_simp]:
  "\<lbrakk>write_reg DBGDTRTX_EL0_ref v\<rbrakk>\<^sub>S = write_regS DBGDTRTX_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RDDC_EL0[liftState_simp]:
  "\<lbrakk>read_reg RDDC_EL0_ref\<rbrakk>\<^sub>S = read_regS RDDC_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RDDC_EL0[liftState_simp]:
  "\<lbrakk>write_reg RDDC_EL0_ref v\<rbrakk>\<^sub>S = write_regS RDDC_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DDC_EL3[liftState_simp]:
  "\<lbrakk>read_reg DDC_EL3_ref\<rbrakk>\<^sub>S = read_regS DDC_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DDC_EL3[liftState_simp]:
  "\<lbrakk>write_reg DDC_EL3_ref v\<rbrakk>\<^sub>S = write_regS DDC_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DDC_EL2[liftState_simp]:
  "\<lbrakk>read_reg DDC_EL2_ref\<rbrakk>\<^sub>S = read_regS DDC_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DDC_EL2[liftState_simp]:
  "\<lbrakk>write_reg DDC_EL2_ref v\<rbrakk>\<^sub>S = write_regS DDC_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DDC_EL1[liftState_simp]:
  "\<lbrakk>read_reg DDC_EL1_ref\<rbrakk>\<^sub>S = read_regS DDC_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DDC_EL1[liftState_simp]:
  "\<lbrakk>write_reg DDC_EL1_ref v\<rbrakk>\<^sub>S = write_regS DDC_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DDC_EL0[liftState_simp]:
  "\<lbrakk>read_reg DDC_EL0_ref\<rbrakk>\<^sub>S = read_regS DDC_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DDC_EL0[liftState_simp]:
  "\<lbrakk>write_reg DDC_EL0_ref v\<rbrakk>\<^sub>S = write_regS DDC_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VTTBR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VTTBR_EL2_ref\<rbrakk>\<^sub>S = read_regS VTTBR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VTTBR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VTTBR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VTTBR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VTCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VTCR_EL2_ref\<rbrakk>\<^sub>S = read_regS VTCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VTCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VTCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VTCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VSESR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VSESR_EL2_ref\<rbrakk>\<^sub>S = read_regS VSESR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VSESR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VSESR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VSESR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TTBR1_EL2[liftState_simp]:
  "\<lbrakk>read_reg TTBR1_EL2_ref\<rbrakk>\<^sub>S = read_regS TTBR1_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TTBR1_EL2[liftState_simp]:
  "\<lbrakk>write_reg TTBR1_EL2_ref v\<rbrakk>\<^sub>S = write_regS TTBR1_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TTBR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg TTBR1_EL1_ref\<rbrakk>\<^sub>S = read_regS TTBR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TTBR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg TTBR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS TTBR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TTBR0_EL3[liftState_simp]:
  "\<lbrakk>read_reg TTBR0_EL3_ref\<rbrakk>\<^sub>S = read_regS TTBR0_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TTBR0_EL3[liftState_simp]:
  "\<lbrakk>write_reg TTBR0_EL3_ref v\<rbrakk>\<^sub>S = write_regS TTBR0_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TTBR0_EL2[liftState_simp]:
  "\<lbrakk>read_reg TTBR0_EL2_ref\<rbrakk>\<^sub>S = read_regS TTBR0_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TTBR0_EL2[liftState_simp]:
  "\<lbrakk>write_reg TTBR0_EL2_ref v\<rbrakk>\<^sub>S = write_regS TTBR0_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TTBR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg TTBR0_EL1_ref\<rbrakk>\<^sub>S = read_regS TTBR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TTBR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg TTBR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS TTBR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TPIDR_EL3[liftState_simp]:
  "\<lbrakk>read_reg TPIDR_EL3_ref\<rbrakk>\<^sub>S = read_regS TPIDR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TPIDR_EL3[liftState_simp]:
  "\<lbrakk>write_reg TPIDR_EL3_ref v\<rbrakk>\<^sub>S = write_regS TPIDR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TPIDR_EL2[liftState_simp]:
  "\<lbrakk>read_reg TPIDR_EL2_ref\<rbrakk>\<^sub>S = read_regS TPIDR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TPIDR_EL2[liftState_simp]:
  "\<lbrakk>write_reg TPIDR_EL2_ref v\<rbrakk>\<^sub>S = write_regS TPIDR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TPIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg TPIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS TPIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TPIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg TPIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS TPIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TPIDR_EL0[liftState_simp]:
  "\<lbrakk>read_reg TPIDR_EL0_ref\<rbrakk>\<^sub>S = read_regS TPIDR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TPIDR_EL0[liftState_simp]:
  "\<lbrakk>write_reg TPIDR_EL0_ref v\<rbrakk>\<^sub>S = write_regS TPIDR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TPIDRRO_EL0[liftState_simp]:
  "\<lbrakk>read_reg TPIDRRO_EL0_ref\<rbrakk>\<^sub>S = read_regS TPIDRRO_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TPIDRRO_EL0[liftState_simp]:
  "\<lbrakk>write_reg TPIDRRO_EL0_ref v\<rbrakk>\<^sub>S = write_regS TPIDRRO_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SP_EL2[liftState_simp]:
  "\<lbrakk>read_reg SP_EL2_ref\<rbrakk>\<^sub>S = read_regS SP_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SP_EL2[liftState_simp]:
  "\<lbrakk>write_reg SP_EL2_ref v\<rbrakk>\<^sub>S = write_regS SP_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SP_EL1[liftState_simp]:
  "\<lbrakk>read_reg SP_EL1_ref\<rbrakk>\<^sub>S = read_regS SP_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SP_EL1[liftState_simp]:
  "\<lbrakk>write_reg SP_EL1_ref v\<rbrakk>\<^sub>S = write_regS SP_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SP_EL0[liftState_simp]:
  "\<lbrakk>read_reg SP_EL0_ref\<rbrakk>\<^sub>S = read_regS SP_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SP_EL0[liftState_simp]:
  "\<lbrakk>write_reg SP_EL0_ref v\<rbrakk>\<^sub>S = write_regS SP_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPSR_und[liftState_simp]:
  "\<lbrakk>read_reg SPSR_und_ref\<rbrakk>\<^sub>S = read_regS SPSR_und_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPSR_und[liftState_simp]:
  "\<lbrakk>write_reg SPSR_und_ref v\<rbrakk>\<^sub>S = write_regS SPSR_und_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPSR_irq[liftState_simp]:
  "\<lbrakk>read_reg SPSR_irq_ref\<rbrakk>\<^sub>S = read_regS SPSR_irq_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPSR_irq[liftState_simp]:
  "\<lbrakk>write_reg SPSR_irq_ref v\<rbrakk>\<^sub>S = write_regS SPSR_irq_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPSR_fiq[liftState_simp]:
  "\<lbrakk>read_reg SPSR_fiq_ref\<rbrakk>\<^sub>S = read_regS SPSR_fiq_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPSR_fiq[liftState_simp]:
  "\<lbrakk>write_reg SPSR_fiq_ref v\<rbrakk>\<^sub>S = write_regS SPSR_fiq_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPSR_abt[liftState_simp]:
  "\<lbrakk>read_reg SPSR_abt_ref\<rbrakk>\<^sub>S = read_regS SPSR_abt_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPSR_abt[liftState_simp]:
  "\<lbrakk>write_reg SPSR_abt_ref v\<rbrakk>\<^sub>S = write_regS SPSR_abt_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SDER32_EL3[liftState_simp]:
  "\<lbrakk>read_reg SDER32_EL3_ref\<rbrakk>\<^sub>S = read_regS SDER32_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SDER32_EL3[liftState_simp]:
  "\<lbrakk>write_reg SDER32_EL3_ref v\<rbrakk>\<^sub>S = write_regS SDER32_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCXTNUM_EL3[liftState_simp]:
  "\<lbrakk>read_reg SCXTNUM_EL3_ref\<rbrakk>\<^sub>S = read_regS SCXTNUM_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCXTNUM_EL3[liftState_simp]:
  "\<lbrakk>write_reg SCXTNUM_EL3_ref v\<rbrakk>\<^sub>S = write_regS SCXTNUM_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCXTNUM_EL2[liftState_simp]:
  "\<lbrakk>read_reg SCXTNUM_EL2_ref\<rbrakk>\<^sub>S = read_regS SCXTNUM_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCXTNUM_EL2[liftState_simp]:
  "\<lbrakk>write_reg SCXTNUM_EL2_ref v\<rbrakk>\<^sub>S = write_regS SCXTNUM_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCXTNUM_EL1[liftState_simp]:
  "\<lbrakk>read_reg SCXTNUM_EL1_ref\<rbrakk>\<^sub>S = read_regS SCXTNUM_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCXTNUM_EL1[liftState_simp]:
  "\<lbrakk>write_reg SCXTNUM_EL1_ref v\<rbrakk>\<^sub>S = write_regS SCXTNUM_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CID_EL0[liftState_simp]:
  "\<lbrakk>read_reg CID_EL0_ref\<rbrakk>\<^sub>S = read_regS CID_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CID_EL0[liftState_simp]:
  "\<lbrakk>write_reg CID_EL0_ref v\<rbrakk>\<^sub>S = write_regS CID_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_S3_op1_Cn_Cm_op2[liftState_simp]:
  "\<lbrakk>read_reg S3_op1_Cn_Cm_op2_ref\<rbrakk>\<^sub>S = read_regS S3_op1_Cn_Cm_op2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_S3_op1_Cn_Cm_op2[liftState_simp]:
  "\<lbrakk>write_reg S3_op1_Cn_Cm_op2_ref v\<rbrakk>\<^sub>S = write_regS S3_op1_Cn_Cm_op2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RVBAR_EL3[liftState_simp]:
  "\<lbrakk>read_reg RVBAR_EL3_ref\<rbrakk>\<^sub>S = read_regS RVBAR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RVBAR_EL3[liftState_simp]:
  "\<lbrakk>write_reg RVBAR_EL3_ref v\<rbrakk>\<^sub>S = write_regS RVBAR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RVBAR_EL2[liftState_simp]:
  "\<lbrakk>read_reg RVBAR_EL2_ref\<rbrakk>\<^sub>S = read_regS RVBAR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RVBAR_EL2[liftState_simp]:
  "\<lbrakk>write_reg RVBAR_EL2_ref v\<rbrakk>\<^sub>S = write_regS RVBAR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RVBAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg RVBAR_EL1_ref\<rbrakk>\<^sub>S = read_regS RVBAR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RVBAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg RVBAR_EL1_ref v\<rbrakk>\<^sub>S = write_regS RVBAR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RTPIDR_EL0[liftState_simp]:
  "\<lbrakk>read_reg RTPIDR_EL0_ref\<rbrakk>\<^sub>S = read_regS RTPIDR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RTPIDR_EL0[liftState_simp]:
  "\<lbrakk>write_reg RTPIDR_EL0_ref v\<rbrakk>\<^sub>S = write_regS RTPIDR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RSP_EL0[liftState_simp]:
  "\<lbrakk>read_reg RSP_EL0_ref\<rbrakk>\<^sub>S = read_regS RSP_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RSP_EL0[liftState_simp]:
  "\<lbrakk>write_reg RSP_EL0_ref v\<rbrakk>\<^sub>S = write_regS RSP_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RMR_EL3[liftState_simp]:
  "\<lbrakk>read_reg RMR_EL3_ref\<rbrakk>\<^sub>S = read_regS RMR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RMR_EL3[liftState_simp]:
  "\<lbrakk>write_reg RMR_EL3_ref v\<rbrakk>\<^sub>S = write_regS RMR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RMR_EL2[liftState_simp]:
  "\<lbrakk>read_reg RMR_EL2_ref\<rbrakk>\<^sub>S = read_regS RMR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RMR_EL2[liftState_simp]:
  "\<lbrakk>write_reg RMR_EL2_ref v\<rbrakk>\<^sub>S = write_regS RMR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_RMR_EL1[liftState_simp]:
  "\<lbrakk>read_reg RMR_EL1_ref\<rbrakk>\<^sub>S = read_regS RMR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_RMR_EL1[liftState_simp]:
  "\<lbrakk>write_reg RMR_EL1_ref v\<rbrakk>\<^sub>S = write_regS RMR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_REVIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg REVIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS REVIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_REVIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg REVIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS REVIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMXEVTYPER_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMXEVTYPER_EL0_ref\<rbrakk>\<^sub>S = read_regS PMXEVTYPER_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMXEVTYPER_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMXEVTYPER_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMXEVTYPER_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMXEVCNTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMXEVCNTR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMXEVCNTR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMXEVCNTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMXEVCNTR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMXEVCNTR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSLATFR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMSLATFR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMSLATFR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSLATFR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMSLATFR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMSLATFR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSIRR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMSIRR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMSIRR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSIRR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMSIRR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMSIRR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMSIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMSIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMSIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMSIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSICR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMSICR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMSICR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSICR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMSICR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMSICR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSFCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMSFCR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMSFCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSFCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMSFCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMSFCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSEVFR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMSEVFR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMSEVFR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSEVFR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMSEVFR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMSEVFR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSELR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMSELR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMSELR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSELR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMSELR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMSELR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg PMSCR_EL2_ref\<rbrakk>\<^sub>S = read_regS PMSCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg PMSCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS PMSCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMSCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMSCR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMSCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMSCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMSCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMSCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMOVSSET_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMOVSSET_EL0_ref\<rbrakk>\<^sub>S = read_regS PMOVSSET_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMOVSSET_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMOVSSET_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMOVSSET_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMOVSCLR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMOVSCLR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMOVSCLR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMOVSCLR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMOVSCLR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMOVSCLR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMINTENSET_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMINTENSET_EL1_ref\<rbrakk>\<^sub>S = read_regS PMINTENSET_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMINTENSET_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMINTENSET_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMINTENSET_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMINTENCLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMINTENCLR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMINTENCLR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMINTENCLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMINTENCLR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMINTENCLR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMEVTYPER_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMEVTYPER_EL0_ref\<rbrakk>\<^sub>S = read_regS PMEVTYPER_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMEVTYPER_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMEVTYPER_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMEVTYPER_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMEVCNTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMEVCNTR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMEVCNTR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMEVCNTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMEVCNTR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMEVCNTR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMCR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMCR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCNTENSET_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCNTENSET_EL0_ref\<rbrakk>\<^sub>S = read_regS PMCNTENSET_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCNTENSET_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCNTENSET_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMCNTENSET_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCNTENCLR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCNTENCLR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMCNTENCLR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCNTENCLR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCNTENCLR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMCNTENCLR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCEID1_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCEID1_EL0_ref\<rbrakk>\<^sub>S = read_regS PMCEID1_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCEID1_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCEID1_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMCEID1_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCEID0_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCEID0_EL0_ref\<rbrakk>\<^sub>S = read_regS PMCEID0_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCEID0_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCEID0_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMCEID0_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCCNTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCCNTR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMCCNTR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCCNTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCCNTR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMCCNTR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMUSERENR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMUSERENR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMUSERENR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMUSERENR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMUSERENR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMUSERENR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMCCFILTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg PMCCFILTR_EL0_ref\<rbrakk>\<^sub>S = read_regS PMCCFILTR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMCCFILTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg PMCCFILTR_EL0_ref v\<rbrakk>\<^sub>S = write_regS PMCCFILTR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMBSR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMBSR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMBSR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMBSR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMBSR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMBSR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMBPTR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMBPTR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMBPTR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMBPTR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMBPTR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMBPTR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMBLIMITR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMBLIMITR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMBLIMITR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMBLIMITR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMBLIMITR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMBLIMITR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PMBIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PMBIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS PMBIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PMBIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PMBIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PMBIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg PAR_EL1_ref\<rbrakk>\<^sub>S = read_regS PAR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg PAR_EL1_ref v\<rbrakk>\<^sub>S = write_regS PAR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_OSECCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSECCR_EL1_ref\<rbrakk>\<^sub>S = read_regS OSECCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_OSECCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSECCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS OSECCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_OSDTRTX_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSDTRTX_EL1_ref\<rbrakk>\<^sub>S = read_regS OSDTRTX_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_OSDTRTX_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSDTRTX_EL1_ref v\<rbrakk>\<^sub>S = write_regS OSDTRTX_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_OSDTRRX_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSDTRRX_EL1_ref\<rbrakk>\<^sub>S = read_regS OSDTRRX_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_OSDTRRX_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSDTRRX_EL1_ref v\<rbrakk>\<^sub>S = write_regS OSDTRRX_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MVFR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg MVFR2_EL1_ref\<rbrakk>\<^sub>S = read_regS MVFR2_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MVFR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg MVFR2_EL1_ref v\<rbrakk>\<^sub>S = write_regS MVFR2_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MVFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg MVFR1_EL1_ref\<rbrakk>\<^sub>S = read_regS MVFR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MVFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg MVFR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS MVFR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MVFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg MVFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS MVFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MVFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg MVFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS MVFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VMPIDR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VMPIDR_EL2_ref\<rbrakk>\<^sub>S = read_regS VMPIDR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VMPIDR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VMPIDR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VMPIDR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MPIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS MPIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MPIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS MPIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPMV_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPMV_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPMV_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPMV_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPMV_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPMV_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPM7_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM7_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPM7_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPM7_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM7_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPM7_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPM6_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM6_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPM6_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPM6_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM6_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPM6_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPM5_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM5_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPM5_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPM5_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM5_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPM5_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPM4_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM4_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPM4_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPM4_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM4_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPM4_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPM3_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM3_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPM3_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPM3_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM3_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPM3_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPM2_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM2_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPM2_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPM2_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM2_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPM2_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPM1_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM1_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPM1_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPM1_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM1_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPM1_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMVPM0_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMVPM0_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMVPM0_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMVPM0_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMVPM0_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMVPM0_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MPAMIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS MPAMIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MPAMIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS MPAMIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAMHCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg MPAMHCR_EL2_ref\<rbrakk>\<^sub>S = read_regS MPAMHCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAMHCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg MPAMHCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS MPAMHCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAM1_EL1_0_62[liftState_simp]:
  "\<lbrakk>read_reg MPAM1_EL1_0_62_ref\<rbrakk>\<^sub>S = read_regS MPAM1_EL1_0_62_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAM1_EL1_0_62[liftState_simp]:
  "\<lbrakk>write_reg MPAM1_EL1_0_62_ref v\<rbrakk>\<^sub>S = write_regS MPAM1_EL1_0_62_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAM2_EL2_0_62[liftState_simp]:
  "\<lbrakk>read_reg MPAM2_EL2_0_62_ref\<rbrakk>\<^sub>S = read_regS MPAM2_EL2_0_62_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAM2_EL2_0_62[liftState_simp]:
  "\<lbrakk>write_reg MPAM2_EL2_0_62_ref v\<rbrakk>\<^sub>S = write_regS MPAM2_EL2_0_62_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAM3_EL3[liftState_simp]:
  "\<lbrakk>read_reg MPAM3_EL3_ref\<rbrakk>\<^sub>S = read_regS MPAM3_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAM3_EL3[liftState_simp]:
  "\<lbrakk>write_reg MPAM3_EL3_ref v\<rbrakk>\<^sub>S = write_regS MPAM3_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MPAM0_EL1[liftState_simp]:
  "\<lbrakk>read_reg MPAM0_EL1_ref\<rbrakk>\<^sub>S = read_regS MPAM0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MPAM0_EL1[liftState_simp]:
  "\<lbrakk>write_reg MPAM0_EL1_ref v\<rbrakk>\<^sub>S = write_regS MPAM0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VPIDR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VPIDR_EL2_ref\<rbrakk>\<^sub>S = read_regS VPIDR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VPIDR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VPIDR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VPIDR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS MIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS MIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MDRAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MDRAR_EL1_ref\<rbrakk>\<^sub>S = read_regS MDRAR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MDRAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MDRAR_EL1_ref v\<rbrakk>\<^sub>S = write_regS MDRAR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MDCCSR_EL0[liftState_simp]:
  "\<lbrakk>read_reg MDCCSR_EL0_ref\<rbrakk>\<^sub>S = read_regS MDCCSR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MDCCSR_EL0[liftState_simp]:
  "\<lbrakk>write_reg MDCCSR_EL0_ref v\<rbrakk>\<^sub>S = write_regS MDCCSR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MDCCINT_EL1[liftState_simp]:
  "\<lbrakk>read_reg MDCCINT_EL1_ref\<rbrakk>\<^sub>S = read_regS MDCCINT_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MDCCINT_EL1[liftState_simp]:
  "\<lbrakk>write_reg MDCCINT_EL1_ref v\<rbrakk>\<^sub>S = write_regS MDCCINT_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MAIR_EL3[liftState_simp]:
  "\<lbrakk>read_reg MAIR_EL3_ref\<rbrakk>\<^sub>S = read_regS MAIR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MAIR_EL3[liftState_simp]:
  "\<lbrakk>write_reg MAIR_EL3_ref v\<rbrakk>\<^sub>S = write_regS MAIR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MAIR_EL2[liftState_simp]:
  "\<lbrakk>read_reg MAIR_EL2_ref\<rbrakk>\<^sub>S = read_regS MAIR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MAIR_EL2[liftState_simp]:
  "\<lbrakk>write_reg MAIR_EL2_ref v\<rbrakk>\<^sub>S = write_regS MAIR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MAIR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MAIR_EL1_ref\<rbrakk>\<^sub>S = read_regS MAIR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MAIR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MAIR_EL1_ref v\<rbrakk>\<^sub>S = write_regS MAIR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_LORSA_EL1[liftState_simp]:
  "\<lbrakk>read_reg LORSA_EL1_ref\<rbrakk>\<^sub>S = read_regS LORSA_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_LORSA_EL1[liftState_simp]:
  "\<lbrakk>write_reg LORSA_EL1_ref v\<rbrakk>\<^sub>S = write_regS LORSA_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_LORN_EL1[liftState_simp]:
  "\<lbrakk>read_reg LORN_EL1_ref\<rbrakk>\<^sub>S = read_regS LORN_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_LORN_EL1[liftState_simp]:
  "\<lbrakk>write_reg LORN_EL1_ref v\<rbrakk>\<^sub>S = write_regS LORN_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_LORID_EL1[liftState_simp]:
  "\<lbrakk>read_reg LORID_EL1_ref\<rbrakk>\<^sub>S = read_regS LORID_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_LORID_EL1[liftState_simp]:
  "\<lbrakk>write_reg LORID_EL1_ref v\<rbrakk>\<^sub>S = write_regS LORID_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_LOREA_EL1[liftState_simp]:
  "\<lbrakk>read_reg LOREA_EL1_ref\<rbrakk>\<^sub>S = read_regS LOREA_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_LOREA_EL1[liftState_simp]:
  "\<lbrakk>write_reg LOREA_EL1_ref v\<rbrakk>\<^sub>S = write_regS LOREA_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_LORC_EL1[liftState_simp]:
  "\<lbrakk>read_reg LORC_EL1_ref\<rbrakk>\<^sub>S = read_regS LORC_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_LORC_EL1[liftState_simp]:
  "\<lbrakk>write_reg LORC_EL1_ref v\<rbrakk>\<^sub>S = write_regS LORC_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ISR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ISR_EL1_ref\<rbrakk>\<^sub>S = read_regS ISR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ISR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ISR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ISR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_IFSR32_EL2[liftState_simp]:
  "\<lbrakk>read_reg IFSR32_EL2_ref\<rbrakk>\<^sub>S = read_regS IFSR32_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_IFSR32_EL2[liftState_simp]:
  "\<lbrakk>write_reg IFSR32_EL2_ref v\<rbrakk>\<^sub>S = write_regS IFSR32_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_PFR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_PFR2_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_PFR2_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_PFR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_PFR2_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_PFR2_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_PFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_PFR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_PFR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_PFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_PFR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_PFR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_PFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_PFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_PFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_PFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_PFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_PFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_MMFR5_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR5_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_MMFR5_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_MMFR5_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR5_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_MMFR5_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_MMFR4_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR4_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_MMFR4_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_MMFR4_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR4_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_MMFR4_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_MMFR3_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR3_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_MMFR3_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_MMFR3_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR3_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_MMFR3_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_MMFR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR2_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_MMFR2_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_MMFR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR2_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_MMFR2_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_MMFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_MMFR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_MMFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_MMFR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_MMFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_MMFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_MMFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_MMFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_MMFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_MMFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_ISAR6_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR6_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_ISAR6_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_ISAR6_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR6_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_ISAR6_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_ISAR5_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR5_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_ISAR5_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_ISAR5_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR5_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_ISAR5_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_ISAR4_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR4_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_ISAR4_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_ISAR4_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR4_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_ISAR4_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_ISAR3_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR3_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_ISAR3_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_ISAR3_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR3_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_ISAR3_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_ISAR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR2_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_ISAR2_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_ISAR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR2_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_ISAR2_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_ISAR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_ISAR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_ISAR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_ISAR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_ISAR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_ISAR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_ISAR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_ISAR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_ISAR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_ISAR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_DFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_DFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_DFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_DFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_DFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_DFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64ZFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64ZFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64ZFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64ZFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64ZFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64ZFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64PFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64PFR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64PFR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64PFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64PFR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64PFR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64PFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64PFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64PFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64PFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64PFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64PFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64MMFR2_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64MMFR2_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64MMFR2_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64MMFR2_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64MMFR2_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64MMFR2_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64MMFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64MMFR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64MMFR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64MMFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64MMFR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64MMFR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64MMFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64MMFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64MMFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64MMFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64MMFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64MMFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64ISAR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64ISAR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64ISAR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64ISAR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64ISAR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64ISAR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64ISAR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64ISAR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64ISAR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64ISAR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64ISAR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64ISAR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64DFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64DFR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64DFR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64DFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64DFR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64DFR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64DFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64DFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64DFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64DFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64DFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64DFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64AFR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64AFR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64AFR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64AFR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64AFR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64AFR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ID_AA64AFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64AFR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ID_AA64AFR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ID_AA64AFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64AFR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ID_AA64AFR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_VTR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_VTR_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_VTR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_VTR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_VTR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_VTR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_VMCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_VMCR_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_VMCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_VMCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_VMCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_VMCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_MISR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_MISR_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_MISR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_MISR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_MISR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_MISR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_LR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_LR_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_LR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_LR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_LR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_LR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_ELRSR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_ELRSR_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_ELRSR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_ELRSR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_ELRSR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_ELRSR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_EISR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_EISR_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_EISR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_EISR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_EISR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_EISR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_AP1R_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_AP1R_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_AP1R_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_AP1R_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_AP1R_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_AP1R_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_AP0R_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_AP0R_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_AP0R_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_AP0R_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_AP0R_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_AP0R_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_RPR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_RPR_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_RPR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_RPR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_RPR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_RPR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_RPR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_RPR_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_RPR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_RPR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_RPR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_RPR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_PMR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_PMR_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_PMR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_PMR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_PMR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_PMR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_PMR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_PMR_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_PMR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_PMR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_PMR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_PMR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_IGRPEN1_EL3[liftState_simp]:
  "\<lbrakk>read_reg ICC_IGRPEN1_EL3_ref\<rbrakk>\<^sub>S = read_regS ICC_IGRPEN1_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_IGRPEN1_EL3[liftState_simp]:
  "\<lbrakk>write_reg ICC_IGRPEN1_EL3_ref v\<rbrakk>\<^sub>S = write_regS ICC_IGRPEN1_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_IGRPEN1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_IGRPEN1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_IGRPEN1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_IGRPEN1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_IGRPEN1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_IGRPEN1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_IGRPEN1_EL1_S[liftState_simp]:
  "\<lbrakk>read_reg ICC_IGRPEN1_EL1_S_ref\<rbrakk>\<^sub>S = read_regS ICC_IGRPEN1_EL1_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_IGRPEN1_EL1_S[liftState_simp]:
  "\<lbrakk>write_reg ICC_IGRPEN1_EL1_S_ref v\<rbrakk>\<^sub>S = write_regS ICC_IGRPEN1_EL1_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_IGRPEN1_EL1_NS[liftState_simp]:
  "\<lbrakk>read_reg ICC_IGRPEN1_EL1_NS_ref\<rbrakk>\<^sub>S = read_regS ICC_IGRPEN1_EL1_NS_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_IGRPEN1_EL1_NS[liftState_simp]:
  "\<lbrakk>write_reg ICC_IGRPEN1_EL1_NS_ref v\<rbrakk>\<^sub>S = write_regS ICC_IGRPEN1_EL1_NS_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_IGRPEN0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_IGRPEN0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_IGRPEN0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_IGRPEN0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_IGRPEN0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_IGRPEN0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_IGRPEN0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_IGRPEN0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_IGRPEN0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_IGRPEN0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_IGRPEN0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_IGRPEN0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_IAR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_IAR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_IAR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_IAR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_IAR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_IAR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_IAR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_IAR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_IAR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_IAR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_IAR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_IAR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_IAR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_IAR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_IAR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_IAR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_IAR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_IAR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_IAR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_IAR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_IAR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_IAR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_IAR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_IAR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_HPPIR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_HPPIR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_HPPIR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_HPPIR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_HPPIR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_HPPIR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_HPPIR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_HPPIR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_HPPIR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_HPPIR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_HPPIR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_HPPIR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_HPPIR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_HPPIR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_HPPIR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_HPPIR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_HPPIR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_HPPIR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_HPPIR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_HPPIR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_HPPIR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_HPPIR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_HPPIR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_HPPIR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_CTLR_EL3[liftState_simp]:
  "\<lbrakk>read_reg ICC_CTLR_EL3_ref\<rbrakk>\<^sub>S = read_regS ICC_CTLR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_CTLR_EL3[liftState_simp]:
  "\<lbrakk>write_reg ICC_CTLR_EL3_ref v\<rbrakk>\<^sub>S = write_regS ICC_CTLR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_CTLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_CTLR_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_CTLR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_CTLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_CTLR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_CTLR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_CTLR_EL1_S[liftState_simp]:
  "\<lbrakk>read_reg ICC_CTLR_EL1_S_ref\<rbrakk>\<^sub>S = read_regS ICC_CTLR_EL1_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_CTLR_EL1_S[liftState_simp]:
  "\<lbrakk>write_reg ICC_CTLR_EL1_S_ref v\<rbrakk>\<^sub>S = write_regS ICC_CTLR_EL1_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_CTLR_EL1_NS[liftState_simp]:
  "\<lbrakk>read_reg ICC_CTLR_EL1_NS_ref\<rbrakk>\<^sub>S = read_regS ICC_CTLR_EL1_NS_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_CTLR_EL1_NS[liftState_simp]:
  "\<lbrakk>write_reg ICC_CTLR_EL1_NS_ref v\<rbrakk>\<^sub>S = write_regS ICC_CTLR_EL1_NS_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_BPR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_BPR1_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_BPR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_BPR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_BPR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_BPR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_BPR1_EL1_S[liftState_simp]:
  "\<lbrakk>read_reg ICC_BPR1_EL1_S_ref\<rbrakk>\<^sub>S = read_regS ICC_BPR1_EL1_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_BPR1_EL1_S[liftState_simp]:
  "\<lbrakk>write_reg ICC_BPR1_EL1_S_ref v\<rbrakk>\<^sub>S = write_regS ICC_BPR1_EL1_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_BPR1_EL1_NS[liftState_simp]:
  "\<lbrakk>read_reg ICC_BPR1_EL1_NS_ref\<rbrakk>\<^sub>S = read_regS ICC_BPR1_EL1_NS_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_BPR1_EL1_NS[liftState_simp]:
  "\<lbrakk>write_reg ICC_BPR1_EL1_NS_ref v\<rbrakk>\<^sub>S = write_regS ICC_BPR1_EL1_NS_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_BPR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_BPR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_BPR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_BPR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_BPR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_BPR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_BPR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_BPR0_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_BPR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_BPR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_BPR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_BPR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_AP1R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_AP1R_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_AP1R_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_AP1R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_AP1R_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_AP1R_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_AP1R_EL1_S[liftState_simp]:
  "\<lbrakk>read_reg ICC_AP1R_EL1_S_ref\<rbrakk>\<^sub>S = read_regS ICC_AP1R_EL1_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_AP1R_EL1_S[liftState_simp]:
  "\<lbrakk>write_reg ICC_AP1R_EL1_S_ref v\<rbrakk>\<^sub>S = write_regS ICC_AP1R_EL1_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_AP1R_EL1_NS[liftState_simp]:
  "\<lbrakk>read_reg ICC_AP1R_EL1_NS_ref\<rbrakk>\<^sub>S = read_regS ICC_AP1R_EL1_NS_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_AP1R_EL1_NS[liftState_simp]:
  "\<lbrakk>write_reg ICC_AP1R_EL1_NS_ref v\<rbrakk>\<^sub>S = write_regS ICC_AP1R_EL1_NS_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_AP1R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_AP1R_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_AP1R_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_AP1R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_AP1R_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_AP1R_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICV_AP0R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICV_AP0R_EL1_ref\<rbrakk>\<^sub>S = read_regS ICV_AP0R_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICV_AP0R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICV_AP0R_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICV_AP0R_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICH_HCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICH_HCR_EL2_ref\<rbrakk>\<^sub>S = read_regS ICH_HCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICH_HCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICH_HCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICH_HCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_SRE_EL3[liftState_simp]:
  "\<lbrakk>read_reg ICC_SRE_EL3_ref\<rbrakk>\<^sub>S = read_regS ICC_SRE_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_SRE_EL3[liftState_simp]:
  "\<lbrakk>write_reg ICC_SRE_EL3_ref v\<rbrakk>\<^sub>S = write_regS ICC_SRE_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_SRE_EL2[liftState_simp]:
  "\<lbrakk>read_reg ICC_SRE_EL2_ref\<rbrakk>\<^sub>S = read_regS ICC_SRE_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_SRE_EL2[liftState_simp]:
  "\<lbrakk>write_reg ICC_SRE_EL2_ref v\<rbrakk>\<^sub>S = write_regS ICC_SRE_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_SRE_EL1_S[liftState_simp]:
  "\<lbrakk>read_reg ICC_SRE_EL1_S_ref\<rbrakk>\<^sub>S = read_regS ICC_SRE_EL1_S_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_SRE_EL1_S[liftState_simp]:
  "\<lbrakk>write_reg ICC_SRE_EL1_S_ref v\<rbrakk>\<^sub>S = write_regS ICC_SRE_EL1_S_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_SRE_EL1_NS[liftState_simp]:
  "\<lbrakk>read_reg ICC_SRE_EL1_NS_ref\<rbrakk>\<^sub>S = read_regS ICC_SRE_EL1_NS_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_SRE_EL1_NS[liftState_simp]:
  "\<lbrakk>write_reg ICC_SRE_EL1_NS_ref v\<rbrakk>\<^sub>S = write_regS ICC_SRE_EL1_NS_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ICC_AP0R_EL1[liftState_simp]:
  "\<lbrakk>read_reg ICC_AP0R_EL1_ref\<rbrakk>\<^sub>S = read_regS ICC_AP0R_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ICC_AP0R_EL1[liftState_simp]:
  "\<lbrakk>write_reg ICC_AP0R_EL1_ref v\<rbrakk>\<^sub>S = write_regS ICC_AP0R_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HSTR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HSTR_EL2_ref\<rbrakk>\<^sub>S = read_regS HSTR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HSTR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HSTR_EL2_ref v\<rbrakk>\<^sub>S = write_regS HSTR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HACR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HACR_EL2_ref\<rbrakk>\<^sub>S = read_regS HACR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HACR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HACR_EL2_ref v\<rbrakk>\<^sub>S = write_regS HACR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_FPSR[liftState_simp]:
  "\<lbrakk>read_reg FPSR_ref\<rbrakk>\<^sub>S = read_regS FPSR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_FPSR[liftState_simp]:
  "\<lbrakk>write_reg FPSR_ref v\<rbrakk>\<^sub>S = write_regS FPSR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_FPEXC32_EL2[liftState_simp]:
  "\<lbrakk>read_reg FPEXC32_EL2_ref\<rbrakk>\<^sub>S = read_regS FPEXC32_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_FPEXC32_EL2[liftState_simp]:
  "\<lbrakk>write_reg FPEXC32_EL2_ref v\<rbrakk>\<^sub>S = write_regS FPEXC32_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_FPCR[liftState_simp]:
  "\<lbrakk>read_reg FPCR_ref\<rbrakk>\<^sub>S = read_regS FPCR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_FPCR[liftState_simp]:
  "\<lbrakk>write_reg FPCR_ref v\<rbrakk>\<^sub>S = write_regS FPCR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXSTATUS_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXSTATUS_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXSTATUS_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXSTATUS_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXSTATUS_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXSTATUS_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXMISC1_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXMISC1_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXMISC1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXMISC1_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXMISC1_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXMISC1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXMISC0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXMISC0_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXMISC0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXMISC0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXMISC0_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXMISC0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXFR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXFR_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXFR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXFR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXFR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXFR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXCTLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXCTLR_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXCTLR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXCTLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXCTLR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXCTLR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERXADDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERXADDR_EL1_ref\<rbrakk>\<^sub>S = read_regS ERXADDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERXADDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERXADDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERXADDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERRSELR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERRSELR_EL1_ref\<rbrakk>\<^sub>S = read_regS ERRSELR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERRSELR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERRSELR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERRSELR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ERRIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ERRIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS ERRIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ERRIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ERRIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ERRIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VDISR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VDISR_EL2_ref\<rbrakk>\<^sub>S = read_regS VDISR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VDISR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VDISR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VDISR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DISR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DISR_EL1_ref\<rbrakk>\<^sub>S = read_regS DISR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DISR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DISR_EL1_ref v\<rbrakk>\<^sub>S = write_regS DISR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DCZID_EL0[liftState_simp]:
  "\<lbrakk>read_reg DCZID_EL0_ref\<rbrakk>\<^sub>S = read_regS DCZID_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DCZID_EL0[liftState_simp]:
  "\<lbrakk>write_reg DCZID_EL0_ref v\<rbrakk>\<^sub>S = write_regS DCZID_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGWVR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGWVR_EL1_ref\<rbrakk>\<^sub>S = read_regS DBGWVR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGWVR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGWVR_EL1_ref v\<rbrakk>\<^sub>S = write_regS DBGWVR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGWCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGWCR_EL1_ref\<rbrakk>\<^sub>S = read_regS DBGWCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGWCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGWCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS DBGWCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGVCR32_EL2[liftState_simp]:
  "\<lbrakk>read_reg DBGVCR32_EL2_ref\<rbrakk>\<^sub>S = read_regS DBGVCR32_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGVCR32_EL2[liftState_simp]:
  "\<lbrakk>write_reg DBGVCR32_EL2_ref v\<rbrakk>\<^sub>S = write_regS DBGVCR32_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CDBGDTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg CDBGDTR_EL0_ref\<rbrakk>\<^sub>S = read_regS CDBGDTR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CDBGDTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg CDBGDTR_EL0_ref v\<rbrakk>\<^sub>S = write_regS CDBGDTR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MDSCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MDSCR_EL1_ref\<rbrakk>\<^sub>S = read_regS MDSCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MDSCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MDSCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS MDSCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGDTRRX_EL0[liftState_simp]:
  "\<lbrakk>read_reg DBGDTRRX_EL0_ref\<rbrakk>\<^sub>S = read_regS DBGDTRRX_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGDTRRX_EL0[liftState_simp]:
  "\<lbrakk>write_reg DBGDTRRX_EL0_ref v\<rbrakk>\<^sub>S = write_regS DBGDTRRX_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGCLAIMSET_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGCLAIMSET_EL1_ref\<rbrakk>\<^sub>S = read_regS DBGCLAIMSET_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGCLAIMSET_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGCLAIMSET_EL1_ref v\<rbrakk>\<^sub>S = write_regS DBGCLAIMSET_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGCLAIMCLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGCLAIMCLR_EL1_ref\<rbrakk>\<^sub>S = read_regS DBGCLAIMCLR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGCLAIMCLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGCLAIMCLR_EL1_ref v\<rbrakk>\<^sub>S = write_regS DBGCLAIMCLR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGBVR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGBVR_EL1_ref\<rbrakk>\<^sub>S = read_regS DBGBVR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGBVR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGBVR_EL1_ref v\<rbrakk>\<^sub>S = write_regS DBGBVR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_OSLSR_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSLSR_EL1_ref\<rbrakk>\<^sub>S = read_regS OSLSR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_OSLSR_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSLSR_EL1_ref v\<rbrakk>\<^sub>S = write_regS OSLSR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_OSDLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSDLR_EL1_ref\<rbrakk>\<^sub>S = read_regS OSDLR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_OSDLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSDLR_EL1_ref v\<rbrakk>\<^sub>S = write_regS OSDLR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGPRCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGPRCR_EL1_ref\<rbrakk>\<^sub>S = read_regS DBGPRCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGPRCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGPRCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS DBGPRCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPIDEN[liftState_simp]:
  "\<lbrakk>read_reg SPIDEN_ref\<rbrakk>\<^sub>S = read_regS SPIDEN_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPIDEN[liftState_simp]:
  "\<lbrakk>write_reg SPIDEN_ref v\<rbrakk>\<^sub>S = write_regS SPIDEN_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGEN[liftState_simp]:
  "\<lbrakk>read_reg DBGEN_ref\<rbrakk>\<^sub>S = read_regS DBGEN_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGEN[liftState_simp]:
  "\<lbrakk>write_reg DBGEN_ref v\<rbrakk>\<^sub>S = write_regS DBGEN_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DSPSR_EL0[liftState_simp]:
  "\<lbrakk>read_reg DSPSR_EL0_ref\<rbrakk>\<^sub>S = read_regS DSPSR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DSPSR_EL0[liftState_simp]:
  "\<lbrakk>write_reg DSPSR_EL0_ref v\<rbrakk>\<^sub>S = write_regS DSPSR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CDLR_EL0[liftState_simp]:
  "\<lbrakk>read_reg CDLR_EL0_ref\<rbrakk>\<^sub>S = read_regS CDLR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CDLR_EL0[liftState_simp]:
  "\<lbrakk>write_reg CDLR_EL0_ref v\<rbrakk>\<^sub>S = write_regS CDLR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGBCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGBCR_EL1_ref\<rbrakk>\<^sub>S = read_regS DBGBCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGBCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGBCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS DBGBCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MDCR_EL3[liftState_simp]:
  "\<lbrakk>read_reg MDCR_EL3_ref\<rbrakk>\<^sub>S = read_regS MDCR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MDCR_EL3[liftState_simp]:
  "\<lbrakk>write_reg MDCR_EL3_ref v\<rbrakk>\<^sub>S = write_regS MDCR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_MDCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg MDCR_EL2_ref\<rbrakk>\<^sub>S = read_regS MDCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_MDCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg MDCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS MDCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DBGAUTHSTATUS_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGAUTHSTATUS_EL1_ref\<rbrakk>\<^sub>S = read_regS DBGAUTHSTATUS_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DBGAUTHSTATUS_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGAUTHSTATUS_EL1_ref v\<rbrakk>\<^sub>S = write_regS DBGAUTHSTATUS_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DACR32_EL2[liftState_simp]:
  "\<lbrakk>read_reg DACR32_EL2_ref\<rbrakk>\<^sub>S = read_regS DACR32_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DACR32_EL2[liftState_simp]:
  "\<lbrakk>write_reg DACR32_EL2_ref v\<rbrakk>\<^sub>S = write_regS DACR32_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CTR_EL0[liftState_simp]:
  "\<lbrakk>read_reg CTR_EL0_ref\<rbrakk>\<^sub>S = read_regS CTR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CTR_EL0[liftState_simp]:
  "\<lbrakk>write_reg CTR_EL0_ref v\<rbrakk>\<^sub>S = write_regS CTR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CSSELR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CSSELR_EL1_ref\<rbrakk>\<^sub>S = read_regS CSSELR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CSSELR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CSSELR_EL1_ref v\<rbrakk>\<^sub>S = write_regS CSSELR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CSCR_EL3[liftState_simp]:
  "\<lbrakk>read_reg CSCR_EL3_ref\<rbrakk>\<^sub>S = read_regS CSCR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CSCR_EL3[liftState_simp]:
  "\<lbrakk>write_reg CSCR_EL3_ref v\<rbrakk>\<^sub>S = write_regS CSCR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CONTEXTIDR_EL2[liftState_simp]:
  "\<lbrakk>read_reg CONTEXTIDR_EL2_ref\<rbrakk>\<^sub>S = read_regS CONTEXTIDR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CONTEXTIDR_EL2[liftState_simp]:
  "\<lbrakk>write_reg CONTEXTIDR_EL2_ref v\<rbrakk>\<^sub>S = write_regS CONTEXTIDR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CONTEXTIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CONTEXTIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS CONTEXTIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CONTEXTIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CONTEXTIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS CONTEXTIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTV_TVAL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTV_TVAL_EL0_ref\<rbrakk>\<^sub>S = read_regS CNTV_TVAL_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTV_TVAL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTV_TVAL_EL0_ref v\<rbrakk>\<^sub>S = write_regS CNTV_TVAL_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTV_CVAL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTV_CVAL_EL0_ref\<rbrakk>\<^sub>S = read_regS CNTV_CVAL_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTV_CVAL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTV_CVAL_EL0_ref v\<rbrakk>\<^sub>S = write_regS CNTV_CVAL_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTV_CTL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTV_CTL_EL0_ref\<rbrakk>\<^sub>S = read_regS CNTV_CTL_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTV_CTL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTV_CTL_EL0_ref v\<rbrakk>\<^sub>S = write_regS CNTV_CTL_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTVOFF_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTVOFF_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTVOFF_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTVOFF_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTVOFF_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTVOFF_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTVCT_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTVCT_EL0_ref\<rbrakk>\<^sub>S = read_regS CNTVCT_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTVCT_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTVCT_EL0_ref v\<rbrakk>\<^sub>S = write_regS CNTVCT_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTP_TVAL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTP_TVAL_EL0_ref\<rbrakk>\<^sub>S = read_regS CNTP_TVAL_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTP_TVAL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTP_TVAL_EL0_ref v\<rbrakk>\<^sub>S = write_regS CNTP_TVAL_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTP_CVAL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTP_CVAL_EL0_ref\<rbrakk>\<^sub>S = read_regS CNTP_CVAL_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTP_CVAL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTP_CVAL_EL0_ref v\<rbrakk>\<^sub>S = write_regS CNTP_CVAL_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTP_CTL_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTP_CTL_EL0_ref\<rbrakk>\<^sub>S = read_regS CNTP_CTL_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTP_CTL_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTP_CTL_EL0_ref v\<rbrakk>\<^sub>S = write_regS CNTP_CTL_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTPS_TVAL_EL1[liftState_simp]:
  "\<lbrakk>read_reg CNTPS_TVAL_EL1_ref\<rbrakk>\<^sub>S = read_regS CNTPS_TVAL_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTPS_TVAL_EL1[liftState_simp]:
  "\<lbrakk>write_reg CNTPS_TVAL_EL1_ref v\<rbrakk>\<^sub>S = write_regS CNTPS_TVAL_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTPS_CVAL_EL1[liftState_simp]:
  "\<lbrakk>read_reg CNTPS_CVAL_EL1_ref\<rbrakk>\<^sub>S = read_regS CNTPS_CVAL_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTPS_CVAL_EL1[liftState_simp]:
  "\<lbrakk>write_reg CNTPS_CVAL_EL1_ref v\<rbrakk>\<^sub>S = write_regS CNTPS_CVAL_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTPS_CTL_EL1[liftState_simp]:
  "\<lbrakk>read_reg CNTPS_CTL_EL1_ref\<rbrakk>\<^sub>S = read_regS CNTPS_CTL_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTPS_CTL_EL1[liftState_simp]:
  "\<lbrakk>write_reg CNTPS_CTL_EL1_ref v\<rbrakk>\<^sub>S = write_regS CNTPS_CTL_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTPCT_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTPCT_EL0_ref\<rbrakk>\<^sub>S = read_regS CNTPCT_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTPCT_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTPCT_EL0_ref v\<rbrakk>\<^sub>S = write_regS CNTPCT_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHV_TVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHV_TVAL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHV_TVAL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHV_TVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHV_TVAL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHV_TVAL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHV_CVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHV_CVAL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHV_CVAL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHV_CVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHV_CVAL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHV_CVAL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHV_CTL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHV_CTL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHV_CTL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHV_CTL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHV_CTL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHV_CTL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHP_TVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHP_TVAL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHP_TVAL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHP_TVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHP_TVAL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHP_TVAL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHP_CVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHP_CVAL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHP_CVAL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHP_CVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHP_CVAL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHP_CVAL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHP_CTL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHP_CTL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHP_CTL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHP_CTL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHP_CTL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHP_CTL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTKCTL_EL1[liftState_simp]:
  "\<lbrakk>read_reg CNTKCTL_EL1_ref\<rbrakk>\<^sub>S = read_regS CNTKCTL_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTKCTL_EL1[liftState_simp]:
  "\<lbrakk>write_reg CNTKCTL_EL1_ref v\<rbrakk>\<^sub>S = write_regS CNTKCTL_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHCTL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHCTL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHCTL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHCTL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHCTL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHCTL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTFRQ_EL0[liftState_simp]:
  "\<lbrakk>read_reg CNTFRQ_EL0_ref\<rbrakk>\<^sub>S = read_regS CNTFRQ_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTFRQ_EL0[liftState_simp]:
  "\<lbrakk>write_reg CNTFRQ_EL0_ref v\<rbrakk>\<^sub>S = write_regS CNTFRQ_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CLIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CLIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS CLIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CLIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CLIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS CLIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CHCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg CHCR_EL2_ref\<rbrakk>\<^sub>S = read_regS CHCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CHCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg CHCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS CHCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CCSIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CCSIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS CCSIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CCSIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CCSIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS CCSIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMAIR_EL3[liftState_simp]:
  "\<lbrakk>read_reg AMAIR_EL3_ref\<rbrakk>\<^sub>S = read_regS AMAIR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMAIR_EL3[liftState_simp]:
  "\<lbrakk>write_reg AMAIR_EL3_ref v\<rbrakk>\<^sub>S = write_regS AMAIR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMAIR_EL2[liftState_simp]:
  "\<lbrakk>read_reg AMAIR_EL2_ref\<rbrakk>\<^sub>S = read_regS AMAIR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMAIR_EL2[liftState_simp]:
  "\<lbrakk>write_reg AMAIR_EL2_ref v\<rbrakk>\<^sub>S = write_regS AMAIR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AMAIR_EL1[liftState_simp]:
  "\<lbrakk>read_reg AMAIR_EL1_ref\<rbrakk>\<^sub>S = read_regS AMAIR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AMAIR_EL1[liftState_simp]:
  "\<lbrakk>write_reg AMAIR_EL1_ref v\<rbrakk>\<^sub>S = write_regS AMAIR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg AIDR_EL1_ref\<rbrakk>\<^sub>S = read_regS AIDR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg AIDR_EL1_ref v\<rbrakk>\<^sub>S = write_regS AIDR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AFSR1_EL3[liftState_simp]:
  "\<lbrakk>read_reg AFSR1_EL3_ref\<rbrakk>\<^sub>S = read_regS AFSR1_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AFSR1_EL3[liftState_simp]:
  "\<lbrakk>write_reg AFSR1_EL3_ref v\<rbrakk>\<^sub>S = write_regS AFSR1_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AFSR1_EL2[liftState_simp]:
  "\<lbrakk>read_reg AFSR1_EL2_ref\<rbrakk>\<^sub>S = read_regS AFSR1_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AFSR1_EL2[liftState_simp]:
  "\<lbrakk>write_reg AFSR1_EL2_ref v\<rbrakk>\<^sub>S = write_regS AFSR1_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AFSR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg AFSR1_EL1_ref\<rbrakk>\<^sub>S = read_regS AFSR1_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AFSR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg AFSR1_EL1_ref v\<rbrakk>\<^sub>S = write_regS AFSR1_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AFSR0_EL3[liftState_simp]:
  "\<lbrakk>read_reg AFSR0_EL3_ref\<rbrakk>\<^sub>S = read_regS AFSR0_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AFSR0_EL3[liftState_simp]:
  "\<lbrakk>write_reg AFSR0_EL3_ref v\<rbrakk>\<^sub>S = write_regS AFSR0_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AFSR0_EL2[liftState_simp]:
  "\<lbrakk>read_reg AFSR0_EL2_ref\<rbrakk>\<^sub>S = read_regS AFSR0_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AFSR0_EL2[liftState_simp]:
  "\<lbrakk>write_reg AFSR0_EL2_ref v\<rbrakk>\<^sub>S = write_regS AFSR0_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_AFSR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg AFSR0_EL1_ref\<rbrakk>\<^sub>S = read_regS AFSR0_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_AFSR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg AFSR0_EL1_ref v\<rbrakk>\<^sub>S = write_regS AFSR0_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ACTLR_EL3[liftState_simp]:
  "\<lbrakk>read_reg ACTLR_EL3_ref\<rbrakk>\<^sub>S = read_regS ACTLR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ACTLR_EL3[liftState_simp]:
  "\<lbrakk>write_reg ACTLR_EL3_ref v\<rbrakk>\<^sub>S = write_regS ACTLR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ACTLR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ACTLR_EL2_ref\<rbrakk>\<^sub>S = read_regS ACTLR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ACTLR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ACTLR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ACTLR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ACTLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ACTLR_EL1_ref\<rbrakk>\<^sub>S = read_regS ACTLR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ACTLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ACTLR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ACTLR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPSR_EL3[liftState_simp]:
  "\<lbrakk>read_reg SPSR_EL3_ref\<rbrakk>\<^sub>S = read_regS SPSR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPSR_EL3[liftState_simp]:
  "\<lbrakk>write_reg SPSR_EL3_ref v\<rbrakk>\<^sub>S = write_regS SPSR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPSR_EL2[liftState_simp]:
  "\<lbrakk>read_reg SPSR_EL2_ref\<rbrakk>\<^sub>S = read_regS SPSR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPSR_EL2[liftState_simp]:
  "\<lbrakk>write_reg SPSR_EL2_ref v\<rbrakk>\<^sub>S = write_regS SPSR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SPSR_EL1[liftState_simp]:
  "\<lbrakk>read_reg SPSR_EL1_ref\<rbrakk>\<^sub>S = read_regS SPSR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SPSR_EL1[liftState_simp]:
  "\<lbrakk>write_reg SPSR_EL1_ref v\<rbrakk>\<^sub>S = write_regS SPSR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCTLR_EL3[liftState_simp]:
  "\<lbrakk>read_reg SCTLR_EL3_ref\<rbrakk>\<^sub>S = read_regS SCTLR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCTLR_EL3[liftState_simp]:
  "\<lbrakk>write_reg SCTLR_EL3_ref v\<rbrakk>\<^sub>S = write_regS SCTLR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCTLR_EL2[liftState_simp]:
  "\<lbrakk>read_reg SCTLR_EL2_ref\<rbrakk>\<^sub>S = read_regS SCTLR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCTLR_EL2[liftState_simp]:
  "\<lbrakk>write_reg SCTLR_EL2_ref v\<rbrakk>\<^sub>S = write_regS SCTLR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCTLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg SCTLR_EL1_ref\<rbrakk>\<^sub>S = read_regS SCTLR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCTLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg SCTLR_EL1_ref v\<rbrakk>\<^sub>S = write_regS SCTLR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EDSCR[liftState_simp]:
  "\<lbrakk>read_reg EDSCR_ref\<rbrakk>\<^sub>S = read_regS EDSCR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EDSCR[liftState_simp]:
  "\<lbrakk>write_reg EDSCR_ref v\<rbrakk>\<^sub>S = write_regS EDSCR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CPTR_EL3[liftState_simp]:
  "\<lbrakk>read_reg CPTR_EL3_ref\<rbrakk>\<^sub>S = read_regS CPTR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CPTR_EL3[liftState_simp]:
  "\<lbrakk>write_reg CPTR_EL3_ref v\<rbrakk>\<^sub>S = write_regS CPTR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CPTR_EL2[liftState_simp]:
  "\<lbrakk>read_reg CPTR_EL2_ref\<rbrakk>\<^sub>S = read_regS CPTR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CPTR_EL2[liftState_simp]:
  "\<lbrakk>write_reg CPTR_EL2_ref v\<rbrakk>\<^sub>S = write_regS CPTR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CPACR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CPACR_EL1_ref\<rbrakk>\<^sub>S = read_regS CPACR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CPACR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CPACR_EL1_ref v\<rbrakk>\<^sub>S = write_regS CPACR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VBAR_EL3[liftState_simp]:
  "\<lbrakk>read_reg VBAR_EL3_ref\<rbrakk>\<^sub>S = read_regS VBAR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VBAR_EL3[liftState_simp]:
  "\<lbrakk>write_reg VBAR_EL3_ref v\<rbrakk>\<^sub>S = write_regS VBAR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VBAR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VBAR_EL2_ref\<rbrakk>\<^sub>S = read_regS VBAR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VBAR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VBAR_EL2_ref v\<rbrakk>\<^sub>S = write_regS VBAR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_VBAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg VBAR_EL1_ref\<rbrakk>\<^sub>S = read_regS VBAR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_VBAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg VBAR_EL1_ref v\<rbrakk>\<^sub>S = write_regS VBAR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ELR_EL3[liftState_simp]:
  "\<lbrakk>read_reg ELR_EL3_ref\<rbrakk>\<^sub>S = read_regS ELR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ELR_EL3[liftState_simp]:
  "\<lbrakk>write_reg ELR_EL3_ref v\<rbrakk>\<^sub>S = write_regS ELR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ELR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ELR_EL2_ref\<rbrakk>\<^sub>S = read_regS ELR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ELR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ELR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ELR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ELR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ELR_EL1_ref\<rbrakk>\<^sub>S = read_regS ELR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ELR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ELR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ELR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CCTLR_EL3[liftState_simp]:
  "\<lbrakk>read_reg CCTLR_EL3_ref\<rbrakk>\<^sub>S = read_regS CCTLR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CCTLR_EL3[liftState_simp]:
  "\<lbrakk>write_reg CCTLR_EL3_ref v\<rbrakk>\<^sub>S = write_regS CCTLR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CCTLR_EL2[liftState_simp]:
  "\<lbrakk>read_reg CCTLR_EL2_ref\<rbrakk>\<^sub>S = read_regS CCTLR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CCTLR_EL2[liftState_simp]:
  "\<lbrakk>write_reg CCTLR_EL2_ref v\<rbrakk>\<^sub>S = write_regS CCTLR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CCTLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CCTLR_EL1_ref\<rbrakk>\<^sub>S = read_regS CCTLR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CCTLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CCTLR_EL1_ref v\<rbrakk>\<^sub>S = write_regS CCTLR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CCTLR_EL0[liftState_simp]:
  "\<lbrakk>read_reg CCTLR_EL0_ref\<rbrakk>\<^sub>S = read_regS CCTLR_EL0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CCTLR_EL0[liftState_simp]:
  "\<lbrakk>write_reg CCTLR_EL0_ref v\<rbrakk>\<^sub>S = write_regS CCTLR_EL0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_BranchTaken[liftState_simp]:
  "\<lbrakk>read_reg BranchTaken_ref\<rbrakk>\<^sub>S = read_regS BranchTaken_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_BranchTaken[liftState_simp]:
  "\<lbrakk>write_reg BranchTaken_ref v\<rbrakk>\<^sub>S = write_regS BranchTaken_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PC[liftState_simp]:
  "\<lbrakk>read_reg PC_ref\<rbrakk>\<^sub>S = read_regS PC_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PC[liftState_simp]:
  "\<lbrakk>write_reg PC_ref v\<rbrakk>\<^sub>S = write_regS PC_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TCR_EL3[liftState_simp]:
  "\<lbrakk>read_reg TCR_EL3_ref\<rbrakk>\<^sub>S = read_regS TCR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TCR_EL3[liftState_simp]:
  "\<lbrakk>write_reg TCR_EL3_ref v\<rbrakk>\<^sub>S = write_regS TCR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg TCR_EL2_ref\<rbrakk>\<^sub>S = read_regS TCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg TCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS TCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg TCR_EL1_ref\<rbrakk>\<^sub>S = read_regS TCR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg TCR_EL1_ref v\<rbrakk>\<^sub>S = write_regS TCR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HPFAR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HPFAR_EL2_ref\<rbrakk>\<^sub>S = read_regS HPFAR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HPFAR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HPFAR_EL2_ref v\<rbrakk>\<^sub>S = write_regS HPFAR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_FAR_EL3[liftState_simp]:
  "\<lbrakk>read_reg FAR_EL3_ref\<rbrakk>\<^sub>S = read_regS FAR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_FAR_EL3[liftState_simp]:
  "\<lbrakk>write_reg FAR_EL3_ref v\<rbrakk>\<^sub>S = write_regS FAR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_FAR_EL2[liftState_simp]:
  "\<lbrakk>read_reg FAR_EL2_ref\<rbrakk>\<^sub>S = read_regS FAR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_FAR_EL2[liftState_simp]:
  "\<lbrakk>write_reg FAR_EL2_ref v\<rbrakk>\<^sub>S = write_regS FAR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_FAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg FAR_EL1_ref\<rbrakk>\<^sub>S = read_regS FAR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_FAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg FAR_EL1_ref v\<rbrakk>\<^sub>S = write_regS FAR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ESR_EL3[liftState_simp]:
  "\<lbrakk>read_reg ESR_EL3_ref\<rbrakk>\<^sub>S = read_regS ESR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ESR_EL3[liftState_simp]:
  "\<lbrakk>write_reg ESR_EL3_ref v\<rbrakk>\<^sub>S = write_regS ESR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ESR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ESR_EL2_ref\<rbrakk>\<^sub>S = read_regS ESR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ESR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ESR_EL2_ref v\<rbrakk>\<^sub>S = write_regS ESR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ESR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ESR_EL1_ref\<rbrakk>\<^sub>S = read_regS ESR_EL1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ESR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ESR_EL1_ref v\<rbrakk>\<^sub>S = write_regS ESR_EL1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R30[liftState_simp]:
  "\<lbrakk>read_reg R30_ref\<rbrakk>\<^sub>S = read_regS R30_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R30[liftState_simp]:
  "\<lbrakk>write_reg R30_ref v\<rbrakk>\<^sub>S = write_regS R30_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R29[liftState_simp]:
  "\<lbrakk>read_reg R29_ref\<rbrakk>\<^sub>S = read_regS R29_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R29[liftState_simp]:
  "\<lbrakk>write_reg R29_ref v\<rbrakk>\<^sub>S = write_regS R29_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R28[liftState_simp]:
  "\<lbrakk>read_reg R28_ref\<rbrakk>\<^sub>S = read_regS R28_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R28[liftState_simp]:
  "\<lbrakk>write_reg R28_ref v\<rbrakk>\<^sub>S = write_regS R28_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R27[liftState_simp]:
  "\<lbrakk>read_reg R27_ref\<rbrakk>\<^sub>S = read_regS R27_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R27[liftState_simp]:
  "\<lbrakk>write_reg R27_ref v\<rbrakk>\<^sub>S = write_regS R27_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R26[liftState_simp]:
  "\<lbrakk>read_reg R26_ref\<rbrakk>\<^sub>S = read_regS R26_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R26[liftState_simp]:
  "\<lbrakk>write_reg R26_ref v\<rbrakk>\<^sub>S = write_regS R26_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R25[liftState_simp]:
  "\<lbrakk>read_reg R25_ref\<rbrakk>\<^sub>S = read_regS R25_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R25[liftState_simp]:
  "\<lbrakk>write_reg R25_ref v\<rbrakk>\<^sub>S = write_regS R25_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R24[liftState_simp]:
  "\<lbrakk>read_reg R24_ref\<rbrakk>\<^sub>S = read_regS R24_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R24[liftState_simp]:
  "\<lbrakk>write_reg R24_ref v\<rbrakk>\<^sub>S = write_regS R24_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R23[liftState_simp]:
  "\<lbrakk>read_reg R23_ref\<rbrakk>\<^sub>S = read_regS R23_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R23[liftState_simp]:
  "\<lbrakk>write_reg R23_ref v\<rbrakk>\<^sub>S = write_regS R23_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R22[liftState_simp]:
  "\<lbrakk>read_reg R22_ref\<rbrakk>\<^sub>S = read_regS R22_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R22[liftState_simp]:
  "\<lbrakk>write_reg R22_ref v\<rbrakk>\<^sub>S = write_regS R22_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R21[liftState_simp]:
  "\<lbrakk>read_reg R21_ref\<rbrakk>\<^sub>S = read_regS R21_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R21[liftState_simp]:
  "\<lbrakk>write_reg R21_ref v\<rbrakk>\<^sub>S = write_regS R21_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R20[liftState_simp]:
  "\<lbrakk>read_reg R20_ref\<rbrakk>\<^sub>S = read_regS R20_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R20[liftState_simp]:
  "\<lbrakk>write_reg R20_ref v\<rbrakk>\<^sub>S = write_regS R20_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R19[liftState_simp]:
  "\<lbrakk>read_reg R19_ref\<rbrakk>\<^sub>S = read_regS R19_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R19[liftState_simp]:
  "\<lbrakk>write_reg R19_ref v\<rbrakk>\<^sub>S = write_regS R19_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R18[liftState_simp]:
  "\<lbrakk>read_reg R18_ref\<rbrakk>\<^sub>S = read_regS R18_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R18[liftState_simp]:
  "\<lbrakk>write_reg R18_ref v\<rbrakk>\<^sub>S = write_regS R18_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R17[liftState_simp]:
  "\<lbrakk>read_reg R17_ref\<rbrakk>\<^sub>S = read_regS R17_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R17[liftState_simp]:
  "\<lbrakk>write_reg R17_ref v\<rbrakk>\<^sub>S = write_regS R17_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R16[liftState_simp]:
  "\<lbrakk>read_reg R16_ref\<rbrakk>\<^sub>S = read_regS R16_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R16[liftState_simp]:
  "\<lbrakk>write_reg R16_ref v\<rbrakk>\<^sub>S = write_regS R16_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R15[liftState_simp]:
  "\<lbrakk>read_reg R15_ref\<rbrakk>\<^sub>S = read_regS R15_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R15[liftState_simp]:
  "\<lbrakk>write_reg R15_ref v\<rbrakk>\<^sub>S = write_regS R15_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R14[liftState_simp]:
  "\<lbrakk>read_reg R14_ref\<rbrakk>\<^sub>S = read_regS R14_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R14[liftState_simp]:
  "\<lbrakk>write_reg R14_ref v\<rbrakk>\<^sub>S = write_regS R14_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R13[liftState_simp]:
  "\<lbrakk>read_reg R13_ref\<rbrakk>\<^sub>S = read_regS R13_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R13[liftState_simp]:
  "\<lbrakk>write_reg R13_ref v\<rbrakk>\<^sub>S = write_regS R13_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R12[liftState_simp]:
  "\<lbrakk>read_reg R12_ref\<rbrakk>\<^sub>S = read_regS R12_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R12[liftState_simp]:
  "\<lbrakk>write_reg R12_ref v\<rbrakk>\<^sub>S = write_regS R12_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R11[liftState_simp]:
  "\<lbrakk>read_reg R11_ref\<rbrakk>\<^sub>S = read_regS R11_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R11[liftState_simp]:
  "\<lbrakk>write_reg R11_ref v\<rbrakk>\<^sub>S = write_regS R11_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R10[liftState_simp]:
  "\<lbrakk>read_reg R10_ref\<rbrakk>\<^sub>S = read_regS R10_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R10[liftState_simp]:
  "\<lbrakk>write_reg R10_ref v\<rbrakk>\<^sub>S = write_regS R10_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R09[liftState_simp]:
  "\<lbrakk>read_reg R09_ref\<rbrakk>\<^sub>S = read_regS R09_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R09[liftState_simp]:
  "\<lbrakk>write_reg R09_ref v\<rbrakk>\<^sub>S = write_regS R09_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R08[liftState_simp]:
  "\<lbrakk>read_reg R08_ref\<rbrakk>\<^sub>S = read_regS R08_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R08[liftState_simp]:
  "\<lbrakk>write_reg R08_ref v\<rbrakk>\<^sub>S = write_regS R08_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R07[liftState_simp]:
  "\<lbrakk>read_reg R07_ref\<rbrakk>\<^sub>S = read_regS R07_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R07[liftState_simp]:
  "\<lbrakk>write_reg R07_ref v\<rbrakk>\<^sub>S = write_regS R07_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R06[liftState_simp]:
  "\<lbrakk>read_reg R06_ref\<rbrakk>\<^sub>S = read_regS R06_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R06[liftState_simp]:
  "\<lbrakk>write_reg R06_ref v\<rbrakk>\<^sub>S = write_regS R06_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R05[liftState_simp]:
  "\<lbrakk>read_reg R05_ref\<rbrakk>\<^sub>S = read_regS R05_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R05[liftState_simp]:
  "\<lbrakk>write_reg R05_ref v\<rbrakk>\<^sub>S = write_regS R05_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R04[liftState_simp]:
  "\<lbrakk>read_reg R04_ref\<rbrakk>\<^sub>S = read_regS R04_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R04[liftState_simp]:
  "\<lbrakk>write_reg R04_ref v\<rbrakk>\<^sub>S = write_regS R04_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R03[liftState_simp]:
  "\<lbrakk>read_reg R03_ref\<rbrakk>\<^sub>S = read_regS R03_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R03[liftState_simp]:
  "\<lbrakk>write_reg R03_ref v\<rbrakk>\<^sub>S = write_regS R03_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R02[liftState_simp]:
  "\<lbrakk>read_reg R02_ref\<rbrakk>\<^sub>S = read_regS R02_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R02[liftState_simp]:
  "\<lbrakk>write_reg R02_ref v\<rbrakk>\<^sub>S = write_regS R02_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R01[liftState_simp]:
  "\<lbrakk>read_reg R01_ref\<rbrakk>\<^sub>S = read_regS R01_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R01[liftState_simp]:
  "\<lbrakk>write_reg R01_ref v\<rbrakk>\<^sub>S = write_regS R01_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_R00[liftState_simp]:
  "\<lbrakk>read_reg R00_ref\<rbrakk>\<^sub>S = read_regS R00_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_R00[liftState_simp]:
  "\<lbrakk>write_reg R00_ref v\<rbrakk>\<^sub>S = write_regS R00_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ThisInstr[liftState_simp]:
  "\<lbrakk>read_reg ThisInstr_ref\<rbrakk>\<^sub>S = read_regS ThisInstr_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ThisInstr[liftState_simp]:
  "\<lbrakk>write_reg ThisInstr_ref v\<rbrakk>\<^sub>S = write_regS ThisInstr_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PSTATE[liftState_simp]:
  "\<lbrakk>read_reg PSTATE_ref\<rbrakk>\<^sub>S = read_regS PSTATE_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PSTATE[liftState_simp]:
  "\<lbrakk>write_reg PSTATE_ref v\<rbrakk>\<^sub>S = write_regS PSTATE_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HCR_EL2_ref\<rbrakk>\<^sub>S = read_regS HCR_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HCR_EL2_ref v\<rbrakk>\<^sub>S = write_regS HCR_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SCR_EL3[liftState_simp]:
  "\<lbrakk>read_reg SCR_EL3_ref\<rbrakk>\<^sub>S = read_regS SCR_EL3_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SCR_EL3[liftState_simp]:
  "\<lbrakk>write_reg SCR_EL3_ref v\<rbrakk>\<^sub>S = write_regS SCR_EL3_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHVS_TVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHVS_TVAL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHVS_TVAL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHVS_TVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHVS_TVAL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHVS_TVAL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHVS_CVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHVS_CVAL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHVS_CVAL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHVS_CVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHVS_CVAL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHVS_CVAL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHVS_CTL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHVS_CTL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHVS_CTL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHVS_CTL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHVS_CTL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHVS_CTL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHPS_TVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHPS_TVAL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHPS_TVAL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHPS_TVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHPS_TVAL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHPS_TVAL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHPS_CVAL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHPS_CVAL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHPS_CVAL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHPS_CVAL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHPS_CVAL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHPS_CVAL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CNTHPS_CTL_EL2[liftState_simp]:
  "\<lbrakk>read_reg CNTHPS_CTL_EL2_ref\<rbrakk>\<^sub>S = read_regS CNTHPS_CTL_EL2_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CNTHPS_CTL_EL2[liftState_simp]:
  "\<lbrakk>write_reg CNTHPS_CTL_EL2_ref v\<rbrakk>\<^sub>S = write_regS CNTHPS_CTL_EL2_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PCC[liftState_simp]:
  "\<lbrakk>read_reg PCC_ref\<rbrakk>\<^sub>S = read_regS PCC_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PCC[liftState_simp]:
  "\<lbrakk>write_reg PCC_ref v\<rbrakk>\<^sub>S = write_regS PCC_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_SEE[liftState_simp]:
  "\<lbrakk>read_reg SEE_ref\<rbrakk>\<^sub>S = read_regS SEE_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_SEE[liftState_simp]:
  "\<lbrakk>write_reg SEE_ref v\<rbrakk>\<^sub>S = write_regS SEE_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma set_regval_Some_type_cases:
  assumes "set_regval r rv s = Some s'"
  obtains (InstrEnc) v where "InstrEnc_of_regval rv = Some v" and "s' = s\<lparr>InstrEnc_reg := (InstrEnc_reg s)(r := v)\<rparr>"
  | (ProcState) v where "ProcState_of_regval rv = Some v" and "s' = s\<lparr>ProcState_reg := (ProcState_reg s)(r := v)\<rparr>"
  | (bitvector_129_dec) v where "bitvector_129_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_129_dec_reg := (bitvector_129_dec_reg s)(r := v)\<rparr>"
  | (bitvector_1_dec) v where "bitvector_1_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_1_dec_reg := (bitvector_1_dec_reg s)(r := v)\<rparr>"
  | (bitvector_2_dec) v where "bitvector_2_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_2_dec_reg := (bitvector_2_dec_reg s)(r := v)\<rparr>"
  | (bitvector_32_dec) v where "bitvector_32_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_32_dec_reg := (bitvector_32_dec_reg s)(r := v)\<rparr>"
  | (bitvector_48_dec) v where "bitvector_48_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_48_dec_reg := (bitvector_48_dec_reg s)(r := v)\<rparr>"
  | (bitvector_63_dec) v where "bitvector_63_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_63_dec_reg := (bitvector_63_dec_reg s)(r := v)\<rparr>"
  | (bitvector_64_dec) v where "bitvector_64_dec_of_regval rv = Some v" and "s' = s\<lparr>bitvector_64_dec_reg := (bitvector_64_dec_reg s)(r := v)\<rparr>"
  | (bool) v where "bool_of_register_value rv = Some v" and "s' = s\<lparr>bool_reg := (bool_reg s)(r := v)\<rparr>"
  | (instr_ast) v where "instr_ast_of_regval rv = Some v" and "s' = s\<lparr>instr_ast_reg := (instr_ast_reg s)(r := v)\<rparr>"
  | (int) v where "int_of_register_value rv = Some v" and "s' = s\<lparr>int_reg := (int_reg s)(r := v)\<rparr>"
  | (signal) v where "signal_of_regval rv = Some v" and "s' = s\<lparr>signal_reg := (signal_reg s)(r := v)\<rparr>"
  | (vector_16_inc_bitvector_32_dec) v where "vector_of_regval (\<lambda>v. bitvector_32_dec_of_regval v) rv = Some v" and "s' = s\<lparr>vector_16_inc_bitvector_32_dec_reg := (vector_16_inc_bitvector_32_dec_reg s)(r := v)\<rparr>"
  | (vector_16_inc_bitvector_64_dec) v where "vector_of_regval (\<lambda>v. bitvector_64_dec_of_regval v) rv = Some v" and "s' = s\<lparr>vector_16_inc_bitvector_64_dec_reg := (vector_16_inc_bitvector_64_dec_reg s)(r := v)\<rparr>"
  | (vector_31_inc_bitvector_32_dec) v where "vector_of_regval (\<lambda>v. bitvector_32_dec_of_regval v) rv = Some v" and "s' = s\<lparr>vector_31_inc_bitvector_32_dec_reg := (vector_31_inc_bitvector_32_dec_reg s)(r := v)\<rparr>"
  | (vector_32_inc_bitvector_128_dec) v where "vector_of_regval (\<lambda>v. bitvector_128_dec_of_regval v) rv = Some v" and "s' = s\<lparr>vector_32_inc_bitvector_128_dec_reg := (vector_32_inc_bitvector_128_dec_reg s)(r := v)\<rparr>"
  | (vector_4_inc_bitvector_32_dec) v where "vector_of_regval (\<lambda>v. bitvector_32_dec_of_regval v) rv = Some v" and "s' = s\<lparr>vector_4_inc_bitvector_32_dec_reg := (vector_4_inc_bitvector_32_dec_reg s)(r := v)\<rparr>"
proof -
  from assms show ?thesis
    unfolding set_regval_unfold registers_def
    apply (elim option_bind_SomeE map_of_Cons_SomeE)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using instr_ast by (auto simp: register_defs fun_upd_def)
    subgoal using InstrEnc by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_48_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_1_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_2_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_32_inc_bitvector_128_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_31_inc_bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_31_inc_bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_63_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_63_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_4_inc_bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_16_inc_bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using signal by (auto simp: register_defs fun_upd_def)
    subgoal using signal by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using vector_16_inc_bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bool by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using ProcState by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_64_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_32_dec by (auto simp: register_defs fun_upd_def)
    subgoal using bitvector_129_dec by (auto simp: register_defs fun_upd_def)
    subgoal using int by (auto simp: register_defs fun_upd_def)
    by auto
qed

lemma get_regval_type_cases:
  fixes r :: string
  obtains (InstrEnc) "get_regval r = (\<lambda>s. Some (regval_of___InstrEnc (InstrEnc_reg s r)))"
  | (ProcState) "get_regval r = (\<lambda>s. Some (regval_of_ProcState (ProcState_reg s r)))"
  | (bitvector_129_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_129_dec (bitvector_129_dec_reg s r)))"
  | (bitvector_1_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_1_dec (bitvector_1_dec_reg s r)))"
  | (bitvector_2_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_2_dec (bitvector_2_dec_reg s r)))"
  | (bitvector_32_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_32_dec (bitvector_32_dec_reg s r)))"
  | (bitvector_48_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_48_dec (bitvector_48_dec_reg s r)))"
  | (bitvector_63_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_63_dec (bitvector_63_dec_reg s r)))"
  | (bitvector_64_dec) "get_regval r = (\<lambda>s. Some (regval_of_bitvector_64_dec (bitvector_64_dec_reg s r)))"
  | (bool) "get_regval r = (\<lambda>s. Some (register_value_of_bool (bool_reg s r)))"
  | (instr_ast) "get_regval r = (\<lambda>s. Some (regval_of_instr_ast (instr_ast_reg s r)))"
  | (int) "get_regval r = (\<lambda>s. Some (register_value_of_int (int_reg s r)))"
  | (signal) "get_regval r = (\<lambda>s. Some (regval_of_signal (signal_reg s r)))"
  | (vector_16_inc_bitvector_32_dec) "get_regval r = (\<lambda>s. Some (regval_of_vector (\<lambda>v. regval_of_bitvector_32_dec v) (vector_16_inc_bitvector_32_dec_reg s r)))"
  | (vector_16_inc_bitvector_64_dec) "get_regval r = (\<lambda>s. Some (regval_of_vector (\<lambda>v. regval_of_bitvector_64_dec v) (vector_16_inc_bitvector_64_dec_reg s r)))"
  | (vector_31_inc_bitvector_32_dec) "get_regval r = (\<lambda>s. Some (regval_of_vector (\<lambda>v. regval_of_bitvector_32_dec v) (vector_31_inc_bitvector_32_dec_reg s r)))"
  | (vector_32_inc_bitvector_128_dec) "get_regval r = (\<lambda>s. Some (regval_of_vector (\<lambda>v. regval_of_bitvector_128_dec v) (vector_32_inc_bitvector_128_dec_reg s r)))"
  | (vector_4_inc_bitvector_32_dec) "get_regval r = (\<lambda>s. Some (regval_of_vector (\<lambda>v. regval_of_bitvector_32_dec v) (vector_4_inc_bitvector_32_dec_reg s r)))"
  | (None) "get_regval r = (\<lambda>s. None)"
proof (cases "map_of registers r")
  case (Some ops)
  then show ?thesis
    unfolding registers_def
    apply (elim map_of_Cons_SomeE)
    subgoal using bool by (auto simp: register_defs)
    subgoal using instr_ast by (auto simp: register_defs)
    subgoal using InstrEnc by (auto simp: register_defs)
    subgoal using bitvector_48_dec by (auto simp: register_defs)
    subgoal using bitvector_1_dec by (auto simp: register_defs)
    subgoal using bitvector_2_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using vector_32_inc_bitvector_128_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using vector_31_inc_bitvector_32_dec by (auto simp: register_defs)
    subgoal using vector_31_inc_bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_63_dec by (auto simp: register_defs)
    subgoal using bitvector_63_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_32_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_32_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_32_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_32_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_32_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using vector_4_inc_bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using vector_16_inc_bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using vector_16_inc_bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using signal by (auto simp: register_defs)
    subgoal using signal by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using vector_16_inc_bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bool by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using ProcState by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_64_dec by (auto simp: register_defs)
    subgoal using bitvector_32_dec by (auto simp: register_defs)
    subgoal using bitvector_129_dec by (auto simp: register_defs)
    subgoal using int by (auto simp: register_defs)
    by auto
qed (auto simp: get_regval_unfold)

end
