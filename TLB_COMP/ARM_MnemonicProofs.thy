theory ARM_MnemonicProofs
  imports ARM_Mnemonic
          MMU_DEFS.MMU_Instants_TLB_PDC
begin

definition
  arm_preconditions :: "'a state_scheme \<Rightarrow> bool"
where
  "arm_preconditions s = (
    Architecture s = ARMv7_A \<and>
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

lemma b_imm_proof: "\<lbrakk>
    Decode m s1 = (i,s2);
    Fetch s = (m,s1);
    ITAdvance () s3 = ((),s');
    Run (b_imm offset) s2 = (u,s');
    arm_preconditions s
  \<rbrakk> \<Longrightarrow>
    s\<lparr>REG := (REG s)(RName_PC := REG s RName_PC + 8 + offset * 4)\<rparr> = s'
"
  apply(
    clarsimp
      simp:
        ArchVersion_def
        Bit_def
        BranchTo_def
        BranchWritePC_def
        CurrentInstrSet_def
        ISETSTATE_def
        If_def
        PC_def
        R_def
        Run_def
        arm_preconditions_def
        b_imm_def
        bin_cat_def
        dfn'BranchTarget_def
        mask_def
        ucast_def
        word_bits_def
        word_cat_def
        word_extract_def
  )
  sorry

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

end
