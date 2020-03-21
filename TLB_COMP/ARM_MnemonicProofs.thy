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

lemma add_reg_proof: "\<lbrakk>
    Decode m s1 = (i,s2);
    Fetch s = (m,s1);
    ITAdvance () s3 = ((),s');
    REG s RName_0usr = x;
    REG s RName_1usr = y;
    Run i s2 = ((),s3);
    arm_preconditions s;
    i = add_reg 0 0 1
  \<rbrakk> \<Longrightarrow>
    s\<lparr>REG := (REG s)(RName_0usr := x+y, RName_PC := REG s RName_PC + 4)\<rparr> = s'
"
  apply (
    clarsimp
      simp:
        AddWithCarry_def
        HaveThumb2_def
        ITAdvance_def
        Let_def
        add_reg_def
        arithm_instr_lemmas
        arm_preconditions_def
        mask_def
        reg_to_bin_def
        wi_hom_syms
  )
  sorry

lemma and_reg_proof: "\<lbrakk>
    REG s r0 = x;
    REG s r1 = y;
    Run (and_reg (reg_to_bin r0) (reg_to_bin r0) (reg_to_bin r1)) s = (u,s');
    arm_preconditions s;
    r0 = RName_0usr;
    r1 = RName_1usr
  \<rbrakk> \<Longrightarrow>
    s\<lparr>REG := (REG s)(r0 := x && y, RName_PC := REG s RName_PC + 4)\<rparr> = s'
"
  apply (
    clarsimp
      simp:
        and_reg_def
        arithm_instr_lemmas
        arm_preconditions_def
        reg_to_bin_def
  )
  done

lemma branch:
  "(word_of_int (bin_cat (uint (word_extract 31 2 (state.REG s RName_PC + 8 + offset))) 2 0)) = (REG s RName_PC + 8 + offset)"
  sorry

lemma b_imm_proof: "\<lbrakk>
    Decode m s1 = (i,s2);
    Fetch s = (m,s1);
    ITAdvance () s3 = ((),s');
    Run (b_imm offset) s2 = ((),s3);
    arm_preconditions s
  \<rbrakk> \<Longrightarrow>
    s\<lparr>REG := (REG s)(RName_PC := REG s RName_PC + 8 + offset)\<rparr> = s'
"
  apply (drule Fetch_state_eq; safe)
  apply (drule Decode_state_eq; safe)
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

lemma cmp_imm_proof: "\<lbrakk>
    imm = 0;
    Run (cmp_imm 0 0) s = (u,s');
    arm_preconditions s
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
  apply (clarsimp simp: arm_preconditions_def)
  apply (clarsimp simp: Run_def cmp_imm_def dfn'ArithLogicImmediate_def)
  apply (clarsimp simp: ARMExpandImm_C_def ExpandImm_C_def Shift_C_def mask_def word_bits_def word_extract_def split: if_split_asm)

  apply (clarsimp simp: ArithmeticOpcode_def DataProcessing_def mask_def word_bits_def word_extract_def split: if_split_asm)
  apply (clarsimp simp: HaveSecurityExt_def IsSecure_def LookUpRName_def R_def Rmode_def)
  apply (clarsimp simp: AddWithCarry_def DataProcessingALU_def Let_def)
  apply (clarsimp simp: IncPC_def ThisInstrLength_def BranchTo_def)
  apply (clarsimp simp: carry negative overflow zero)

  done

lemma mov_imm_proof: "\<lbrakk>
    Decode m s1 = (i,s2);
    Fetch s = (m,s1);
    ITAdvance () s3 = ((),s');
    Run (mov_imm 0 v) s2 = (u,s3);
    arm_preconditions s;
    word_bits 31 12 v = 0
  \<rbrakk> \<Longrightarrow>
    s\<lparr>REG := (REG s)(RName_0usr := (ucast v), RName_PC := REG s RName_PC + 4)\<rparr> = s'
"
  sorry

lemma mov_reg_proof: "\<lbrakk>
    Decode m s1 = (i,s2);
    Fetch s = (m,s1);
    ITAdvance () s3 = ((),s');
    Run (mov_reg 0 1) s2 = (u,s');
    arm_preconditions s
  \<rbrakk> \<Longrightarrow>
    s\<lparr>REG := (REG s)(RName_0usr := REG s RName_1usr, RName_PC := REG s RName_PC + 4)\<rparr> = s'
"
  sorry

lemma neg_proof: "\<lbrakk>
    Decode m s1 = (i,s2);
    Fetch s = (m,s1);
    ITAdvance () s3 = ((),s');
    REG s RName_0usr = v;
    Run i s2 = ((),s3);
    arm_preconditions s;
    i = (neg 0 0)
  \<rbrakk> \<Longrightarrow>
    s\<lparr>REG := (REG s)(RName_0usr := -v, RName_PC := REG s RName_PC + 4)\<rparr> = s'
"
  apply(
    clarsimp
      simp:
        AddWithCarry_def
        ARMExpandImm_C_def
        BranchTo_def
        DataProcessing_def
        DataProcessingALU_def
        ExpandImm_C_def
        HaveSecurityExt_def
        HaveThumb2_def
        ITAdvance_def
        IncPC_def
        IsSecure_def
        Let_def
        LookUpRName_def
        NOT_eq
        R_def
        Rmode_def
        Run_def
        Shift_C_def
        ThisInstrLength_def
        arm_preconditions_def
        dfn'ArithLogicImmediate_def
        neg_def
        rsb_imm_def
        wi_hom_syms
        write'R_def
        write'Rmode_def
        word_bits_def
        word_extract_def
  )
  sorry

lemma sub_reg_proof: "\<lbrakk>
    Decode m s1 = (i,s2);
    Fetch s = (m,s1);
    ITAdvance () s3 = ((),s');
    REG s RName_0usr = x;
    REG s RName_1usr = y;
    Run i s2 = ((),s3);
    arm_preconditions s;
    i = sub_reg 0 0 1
  \<rbrakk> \<Longrightarrow>
    s\<lparr>REG := (REG s)(RName_0usr := x-y, RName_PC := REG s RName_PC + 4)\<rparr> = s'
"
  apply (
    clarsimp
      simp:
        AddWithCarry_def
        HaveThumb2_def
        ITAdvance_def
        If_def
        Let_def
        sub_reg_def
        arithm_instr_lemmas
        arm_preconditions_def
        mask_def
        reg_to_bin_def
        wi_hom_syms
  )
  sorry

end
