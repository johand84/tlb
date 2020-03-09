theory ARM_MnemonicProofs
  imports ARM_Mnemonic
          MMU_DEFS.MMU_Instants_TLB_PDC
begin

definition
  arm_memory_related :: "(paddr \<rightharpoonup> byte) \<Rightarrow> (paddr \<rightharpoonup> byte) \<Rightarrow> bool"
where
  "arm_memory_related m m' = (
    \<forall>x. m x = m' x
  )"

definition
  arm_pc_related :: "32 word \<Rightarrow> 32 word \<Rightarrow> (RName \<rightharpoonup> 32 word) \<Rightarrow> bool"
where
  "arm_pc_related pc pc' rf = (
    case rf RName_PC of Some x \<Rightarrow> x = pc' |
                        None \<Rightarrow> (pc+4) = pc'
  )"

definition
  arm_register_related :: "(RName \<Rightarrow> 32 word) \<Rightarrow> (RName \<Rightarrow> 32 word) \<Rightarrow> (RName \<rightharpoonup> 32 word) \<Rightarrow> RName \<Rightarrow> bool"
where
  "arm_register_related rs rs' rf r = (
    let y = rs' r
    in (
      case rf r of Some x \<Rightarrow> x = y |
                   None \<Rightarrow> rs r = y
    )
  )"

definition
  arm_registers_related :: "(RName \<Rightarrow> 32 word) \<Rightarrow> (RName \<Rightarrow> 32 word) \<Rightarrow> (RName \<rightharpoonup> 32 word) \<Rightarrow> bool"
where
  "arm_registers_related rs rs' rf = (
    arm_register_related rs rs' rf RName_0usr \<and>
    arm_register_related rs rs' rf RName_1usr \<and>
    arm_register_related rs rs' rf RName_2usr \<and>
    arm_register_related rs rs' rf RName_3usr \<and>
    arm_register_related rs rs' rf RName_4usr \<and>
    arm_register_related rs rs' rf RName_5usr \<and>
    arm_register_related rs rs' rf RName_6usr \<and>
    arm_register_related rs rs' rf RName_7usr \<and>
    arm_register_related rs rs' rf RName_8usr \<and>
    arm_register_related rs rs' rf RName_9usr \<and>
    arm_register_related rs rs' rf RName_10usr \<and>
    arm_register_related rs rs' rf RName_11usr \<and>
    arm_register_related rs rs' rf RName_12usr \<and>
    arm_register_related rs rs' rf RName_SPusr \<and>
    arm_register_related rs rs' rf RName_LRusr \<and>
    arm_pc_related (rs RName_PC) (rs' RName_PC) rf
  )"

definition
  arm_state_related :: "'a state_scheme \<Rightarrow> 'a state_scheme \<Rightarrow> (RName \<rightharpoonup> 32 word) \<Rightarrow> bool"
where
  "arm_state_related s s' rf = (
    arm_memory_related (MEM s) (MEM s') \<and>
    arm_registers_related (REG s) (REG s') rf
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

lemma add_reg_proof: "\<lbrakk>
    Encoding s = Encoding_ARM;
    Extensions s = {};
    snd (Run (add_reg (reg_to_bin RName_0usr) (reg_to_bin RName_0usr) (reg_to_bin RName_1usr)) s) = s';
    ((REG s) RName_0usr) = 0;
    ((REG s) RName_1usr) = 1
  \<rbrakk> \<Longrightarrow> arm_state_related s s' (\<lambda>x. (if x = RName_0usr then Some 1 else None))
"
  apply (
    clarsimp
      simp:
        AddWithCarry_def
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
        add_reg_def
        arm_memory_related_def
        arm_pc_related_def
        arm_register_related_def
        arm_registers_related_def
        arm_state_related_def
        dfn'Register_def
        doRegister_def
        mask_def
        reg_to_bin_def
        snd_def
        word_bits_def
        word_extract_def
        write'R_def
        write'Rmode_def
      split:
        option.splits
  )
  done

lemma mov_imm_proof: "\<lbrakk>
    Encoding s = Encoding_ARM;
    Extensions s = {};
    snd (Run (mov_imm (reg_to_bin RName_0usr) 0) s) = s'
  \<rbrakk> \<Longrightarrow> arm_state_related s s' (\<lambda>x. (if x = RName_0usr then Some 0 else None))
"
  apply (
    clarsimp
      simp:
        ARMExpandImm_C_def
        BranchTo_def
        DataProcessing_def
        DataProcessingALU_def
        ExpandImm_C_def
        HaveSecurityExt_def
        IncPC_def
        IsSecure_def
        LookUpRName_def
        Run_def
        Shift_C_def
        ThisInstrLength_def
        arm_memory_related_def
        arm_pc_related_def
        arm_register_related_def
        arm_registers_related_def
        arm_state_related_def
        dfn'ArithLogicImmediate_def
        mask_def
        mov_imm_def
        reg_to_bin_def
        snd_def
        ucast_def
        word_extract_def
        word_bits_def
        write'R_def
        write'Rmode_def
      split:
        option.splits
  )
  done

end
