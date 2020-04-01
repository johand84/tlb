theory ARM_MnemonicProofs
  imports ARM_Mnemonic
          MMU_DEFS.MMU_Instants_TLB_PDC
begin

definition
  arm_preconditions :: "'a state_scheme \<Rightarrow> bool"
where
  "arm_preconditions s = (
    Aligned1 (Addr (state.REG s RName_PC), 4) \<and>
    Architecture s = ARMv7_A \<and>
    \<not>E (CPSR s) \<and>
    Encoding s = Encoding_ARM \<and>
    Extensions s = {} \<and>
    PSR.M (CPSR s) = 0x13 \<and>
    \<not>J (CPSR s) \<and>
    \<not>T (CPSR s)
  )"

definition
  reg_to_bin :: "RName \<Rightarrow> 4 word"
where
  "reg_to_bin r = (
    if r = RName_0usr then 0
    else if r = RName_1usr then 1
    else if r = RName_2usr then 2
    else if r = RName_3usr then 3
    else if r = RName_4usr then 4
    else if r = RName_5usr then 5
    else if r = RName_6usr then 6
    else if r = RName_7usr then 7
    else if r = RName_8usr then 8
    else if r = RName_9usr then 9
    else if r = RName_10usr then 10
    else if r = RName_11usr then 11
    else if r = RName_12usr then 12
    else if r = RName_SPusr then 13
    else if r = RName_LRusr then 14
    else if r = RName_PC then 15
    else HOL.undefined
  )"

lemmas arithm_instr_lemmas =
  BranchTo_def
  DataProcessing_def
  DataProcessingALU_def
  HaveSecurityExt_def
  IncPC_def
  IsSecure_def
  LookUpRName_def
  R_def
  Rmode_def
  Run_def
  Shift_C_def
  ThisInstrLength_def
  dfn'Register_def
  doRegister_def
  word_bits_def
  word_extract_def
  write'R_def
  write'Rmode_def

lemma Fetch_state_eq: "\<lbrakk>
  Fetch s = (m,s1);
  arm_preconditions s
\<rbrakk> \<Longrightarrow> s = s1"
  apply(clarsimp simp: arm_preconditions_def)
  apply(clarsimp simp: CurrentInstrSet_def Fetch_def ISETSTATE_def word_cat_def)
  apply(clarsimp simp: BadMode_def CurrentModeIsNotUser_def MemA_def split: prod.splits)
  apply(clarsimp simp: BigEndianReverse_def MemA_with_priv_def split: prod.splits)
  sorry

lemma Decode_state_eq:
  "\<lbrakk>Decode m s1 = (i,s2);
    arm_preconditions s1\<rbrakk> \<Longrightarrow> s1 = s2"
  apply (clarsimp simp: arm_preconditions_def)
  apply (clarsimp simp: Decode_def)
  sorry

lemma word_extract_cond: "word_extract 31 28 (word_cat (cond::4 word) (add_reg1 0 0 1)::32 word) = (cond::4 word)"
  sorry

lemma word_extract_instr: "word_extract 27 0 (word_cat (cond::4 word) (instr::28 word)::32 word) = (instr::28 word)"
  sorry

(*declare [[show_types]]*)

lemma Decode_add_reg:
  "\<lbrakk>Decode (add_reg 0 0 1) s = (i,s')\<rbrakk> \<Longrightarrow> 
    i = Data (Register (0x4, False, 0, 0, 1, SRType_LSL, 0))"
  apply(clarsimp simp: Decode_def add_reg_def always_def)

  apply(clarsimp simp: DecodeARM_def)
  apply(clarsimp simp: word_extract_cond)
  apply(clarsimp simp: word_extract_instr)
  apply(clarsimp simp: Let_def)
  apply(clarsimp simp: add_reg1_def data_register_def split: if_split_asm)
  sorry
  
lemma add_reg_proof: "\<lbrakk>
    Decode m s1 = (i,s2);
    Fetch s = (m,s1);
    ITAdvance () s3 = ((),s');
    REG s RName_0usr = x;
    REG s RName_1usr = y;
    Run i s2 = ((),s3);
    arm_preconditions s;
    m = add_reg 0 0 1
  \<rbrakk> \<Longrightarrow>
    s\<lparr>REG := (REG s)(RName_0usr := x+y, RName_PC := REG s RName_PC + 4)\<rparr> = s'
"
  apply (clarsimp)
  apply (drule_tac Fetch_state_eq; simp+)
  apply (frule_tac Decode_state_eq; simp+)
  apply (drule_tac Decode_add_reg; simp+)
  apply (clarsimp simp: Run_def Shift_C_def dfn'Register_def doRegister_def split: prod.splits)
  apply (clarsimp simp: HaveSecurityExt_def IsSecure_def LookUpRName_def R_def Rmode_def arm_preconditions_def split: if_split_asm prod.splits)
  apply (clarsimp simp: DataProcessing_def mask_def word_bits_def word_extract_def split: if_split_asm prod.splits)
  apply (clarsimp simp: DataProcessingALU_def AddWithCarry_def Let_def)
  apply (clarsimp simp: HaveSecurityExt_def IsSecure_def Let_def LookUpRName_def R_def Rmode_def split: prod.splits)
  apply (clarsimp simp: HaveSecurityExt_def IsSecure_def LookUpRName_def write'R_def write'Rmode_def split: prod.splits)
  apply (clarsimp simp: BranchTo_def IncPC_def ThisInstrLength_def)
  apply (clarsimp simp: HaveThumb2_def ITAdvance_def)
  apply (clarsimp simp: wi_hom_syms)
  done

lemma Decode_and_reg:
  "\<lbrakk>Decode (and_reg 0 0 1) s = (i,s')\<rbrakk> \<Longrightarrow> 
    i = Data (Register (0x0, False, 0, 0, 1, SRType_LSL, 0))"
  sorry

lemma and_reg_proof: "\<lbrakk>
    Decode m s1 = (i,s2);
    Fetch s = (m,s1);
    ITAdvance () s3 = ((),s');
    REG s RName_0usr = x;
    REG s RName_1usr = y;
    Run i s = (u,s');
    arm_preconditions s;
    m = and_reg 0 0 1
  \<rbrakk> \<Longrightarrow>
    s\<lparr>REG := (REG s)(RName_0usr := x && y, RName_PC := REG s RName_PC + 4)\<rparr> = s'
"
  apply (clarsimp)
  apply (drule_tac Fetch_state_eq; simp+)
  apply (frule_tac Decode_state_eq; simp+)
  apply (drule_tac Decode_and_reg; simp+)
  apply (clarsimp simp: Run_def Shift_C_def dfn'Register_def doRegister_def split: prod.splits)
  apply (clarsimp simp: HaveSecurityExt_def IsSecure_def LookUpRName_def R_def Rmode_def arm_preconditions_def split: if_split_asm prod.splits)
  apply (clarsimp simp: DataProcessing_def mask_def word_bits_def word_extract_def split: if_split_asm prod.splits)
  apply (clarsimp simp: DataProcessingALU_def AddWithCarry_def Let_def)
  apply (clarsimp simp: HaveSecurityExt_def IsSecure_def Let_def LookUpRName_def R_def Rmode_def split: prod.splits)
  apply (clarsimp simp: HaveSecurityExt_def IsSecure_def LookUpRName_def write'R_def write'Rmode_def split: prod.splits)
  apply (clarsimp simp: BranchTo_def IncPC_def ThisInstrLength_def)
  done

lemma branch:
  "(word_of_int (bin_cat (uint (word_extract 31 2 (state.REG s RName_PC + 8 + offset))) 2 0)) = (REG s RName_PC + 8 + offset)"
  sorry

lemma Decode_b_imm:
  "\<lbrakk>Decode (b_imm (ucast offset)) s = (i,s')\<rbrakk> \<Longrightarrow>
    i = Branch (BranchTarget offset)"
  sorry

lemma b_imm_proof: "\<lbrakk>
    Decode m s1 = (i,s2);
    Fetch s = (m,s1);
    ITAdvance () s3 = ((),s');
    Run i s2 = ((),s3);
    arm_preconditions s;
    m = b_imm (ucast offset)
  \<rbrakk> \<Longrightarrow>
    s\<lparr>REG := (REG s)(RName_PC := REG s RName_PC + 8 + offset)\<rparr> = s'
"
  apply (drule Fetch_state_eq; safe)
  apply (frule Decode_state_eq; safe)
  apply (drule Decode_b_imm; safe)
  apply (clarsimp simp: arm_preconditions_def)
  apply (clarsimp simp: Run_def b_imm_def)
  apply (clarsimp simp: dfn'BranchTarget_def split: prod.splits)
  apply (clarsimp simp: CurrentInstrSet_def ISETSTATE_def PC_def R_def word_cat_def)
  apply (clarsimp simp: ArchVersion_def CurrentInstrSet_def ISETSTATE_def BranchWritePC_def word_cat_def)
  apply (clarsimp simp: BranchTo_def)
  apply (clarsimp simp: branch)
  apply (clarsimp simp: HaveThumb2_def ITAdvance_def)
  done

lemma carry:
  "(nat (uint (word_of_int (uint (state.REG s RName_0usr) + uint max_word + 1))) \<noteq>
    Suc (nat (uint (state.REG s RName_0usr)) + nat (uint max_word))) = (REG s RName_0usr = 0)"
  sorry

lemma negative:
  "(bin_nth (uint (state.REG s RName_0usr) + uint max_word + 1) 31) =
   (sint (REG s RName_0usr) < 0)"
  sorry

lemma overflow:
  "(sint (word_of_int (uint (state.REG s RName_0usr) + uint max_word + 1)) \<noteq>
    sint (state.REG s RName_0usr) + sint max_word + 1) = False"
  sorry

lemma zero:
  "(word_of_int (uint (state.REG s RName_0usr) + uint max_word + 1) = 0) = (REG s RName_0usr = 0)"
  sorry

lemma Decode_cmp_imm:
  "\<lbrakk>Decode (cmp_imm 0 imm) s = (i,s')\<rbrakk> \<Longrightarrow>
    i = Data (ArithLogicImmediate (0xa, True, 0, 0, imm))"
  sorry

lemma cmp_imm_proof: "\<lbrakk>
    Decode m s1 = (i,s2);
    Fetch s = (m,s1);
    ITAdvance () s3 = ((),s');
    Run i s2 = (u,s');
    arm_preconditions s;
    imm = 0;
    m = cmp_imm 0 imm
  \<rbrakk> \<Longrightarrow>
    s\<lparr>
      CPSR := (CPSR s)\<lparr>
        PSR.C := REG s RName_0usr = 0,
        PSR.N := sint (REG s RName_0usr) < 0,
        PSR.V := False,
        PSR.Z := REG s RName_0usr = 0
      \<rparr>,
      REG := (REG s)(RName_PC := REG s RName_PC + 4)
    \<rparr> = s'
"
  apply (drule Fetch_state_eq; safe)
  apply (frule Decode_state_eq; safe)
  apply (drule Decode_cmp_imm; safe)
  apply (clarsimp simp: Run_def dfn'ArithLogicImmediate_def split: prod.splits)
  apply (clarsimp simp: ExpandImm_C_def ThumbExpandImm_C_def arm_preconditions_def split: if_split_asm)
  apply (clarsimp simp: ARMExpandImm_C_def Shift_C_def mask_def word_bits_def word_extract_def split: if_split_asm)
  apply (clarsimp simp: ArithmeticOpcode_def DataProcessing_def mask_def word_bits_def word_extract_def split: if_split_asm prod.splits)
  apply (clarsimp simp: HaveSecurityExt_def IsSecure_def LookUpRName_def R_def Rmode_def)
  apply (clarsimp simp: AddWithCarry_def DataProcessingALU_def Let_def)
  apply (clarsimp simp: IncPC_def ThisInstrLength_def BranchTo_def)
  apply (clarsimp simp: carry negative overflow zero)

  done

lemma mov_imm_proof: "\<lbrakk>
    Decode m s1 = (i,s2);
    Fetch s = (m,s1);
    ITAdvance () s3 = ((),s');
    Run i s2 = (u,s3);
    arm_preconditions s;
    m = mov_imm 0 v;
    word_bits 31 12 v = 0
  \<rbrakk> \<Longrightarrow>
    s\<lparr>REG := (REG s)(RName_0usr := (ucast v), RName_PC := REG s RName_PC + 4)\<rparr> = s'
"
  sorry

lemma mov_reg_proof: "\<lbrakk>
    Decode m s1 = (i,s2);
    Fetch s = (m,s1);
    ITAdvance () s3 = ((),s');
    Run i s2 = (u,s');
    arm_preconditions s;
    m = mov_reg 0 1
  \<rbrakk> \<Longrightarrow>
    s\<lparr>REG := (REG s)(RName_0usr := REG s RName_1usr, RName_PC := REG s RName_PC + 4)\<rparr> = s'
"
  sorry

lemma Decode_msr_reg:
  "\<lbrakk>Decode (msr_reg 0 0x1 0) s = (i,s')\<rbrakk> \<Longrightarrow>
    i = System (MoveToSpecialFromRegister (False, 0, 0x1))"
  sorry

lemma CPSRWriteByInstr_proof:
  "(CPSRWriteByInstr (value, 1, False) s = ((), s1)) \<Longrightarrow>  (s\<lparr>
        CPSR := (CPSR s)\<lparr>PSR.M := ucast value\<rparr>\<rparr> = s1)"
  sorry

lemma msr_imm_proof:
  "\<lbrakk>Decode m s1 = (i,s2);
    Fetch s = (m,s1);
    ITAdvance () s3 = ((),s');
    REG s RName_0usr = 0x10;
    Run i s2 = ((),s3);
    arm_preconditions s;
    m = msr_reg 0 0x1 0\<rbrakk> \<Longrightarrow>
      s\<lparr>
        CPSR := (CPSR s)\<lparr>PSR.M := 0x10 \<rparr>,
        REG := (REG s)(RName_PC := REG s RName_PC + 4)
      \<rparr> = s'"
  apply (drule Fetch_state_eq; safe)
  apply (frule Decode_state_eq; safe)
  apply (drule Decode_msr_reg; safe)
  apply (clarsimp simp: Run_def arm_preconditions_def dfn'MoveToSpecialFromRegister_def split: if_split_asm prod.splits)
    apply (clarsimp simp: R_def Rmode_def split: if_split_asm prod.splits)
  apply(clarsimp simp: HaveSecurityExt_def IsSecure_def)
    apply(clarsimp simp: LookUpRName_def)
    apply(drule CPSRWriteByInstr_proof; simp)
    apply(clarsimp simp: CurrentInstrSet_def)
   apply (clarsimp simp: R_def Rmode_def split: if_split_asm prod.splits)
   apply(clarsimp simp: HaveSecurityExt_def IsSecure_def)
   apply(clarsimp simp: LookUpRName_def)
   apply(drule CPSRWriteByInstr_proof; clarsimp)
  apply (clarsimp simp: R_def Rmode_def split: if_split_asm prod.splits)
  apply(clarsimp simp: HaveSecurityExt_def IsSecure_def)
  apply(clarsimp simp: LookUpRName_def)
  apply(drule CPSRWriteByInstr_proof; clarsimp)
  (*apply(clarsimp simp: BadMode_def CurrentModeIsNotUser_def CPSRWriteByInstr_def HaveSecurityExt_def IsSecure_def mask_def word_bits_def word_extract_def)*)
  apply(clarsimp simp: BranchTo_def IncPC_def ThisInstrLength_def)
  apply(clarsimp simp: HaveThumb2_def ITAdvance_def)
  done

lemma neg_proof: "\<lbrakk>
    Decode m s1 = (i,s2);
    Fetch s = (m,s1);
    ITAdvance () s3 = ((),s');
    REG s RName_0usr = v;
    Run i s2 = ((),s3);
    arm_preconditions s;
    m = neg 0 0
  \<rbrakk> \<Longrightarrow>
    s\<lparr>REG := (REG s)(RName_0usr := -v, RName_PC := REG s RName_PC + 4)\<rparr> = s'
"
  sorry

lemma sub_reg_proof: "\<lbrakk>
    Decode m s1 = (i,s2);
    Fetch s = (m,s1);
    ITAdvance () s3 = ((),s');
    REG s RName_0usr = x;
    REG s RName_1usr = y;
    Run i s2 = ((),s3);
    arm_preconditions s;
    m = sub_reg 0 0 1
  \<rbrakk> \<Longrightarrow>
    s\<lparr>REG := (REG s)(RName_0usr := x-y, RName_PC := REG s RName_PC + 4)\<rparr> = s'
"
  sorry

end
