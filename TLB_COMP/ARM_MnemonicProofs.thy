theory ARM_MnemonicProofs
  imports ARM_Mnemonic
          MMU_DEFS.MMU_Instants_TLB_PDC
begin

fun
  memory_related :: "(paddr \<rightharpoonup> byte) \<Rightarrow> (paddr \<rightharpoonup> byte) \<Rightarrow> bool"
where
  "memory_related m m' = (
    \<forall>x. m x = m' x
  )"

fun
  register_related :: "(RName \<Rightarrow> 32 word) \<Rightarrow> (RName \<Rightarrow> 32 word) \<Rightarrow> (RName \<rightharpoonup> 32 word) \<Rightarrow> RName \<Rightarrow> bool"
where
  "register_related rs rs' rf r = (
    let y = rs' r
    in (
      case rf r of Some x \<Rightarrow> x = y |
                   None \<Rightarrow> rs r = y
    )
  )"

fun
  registers_related :: "(RName \<Rightarrow> 32 word) \<Rightarrow> (RName \<Rightarrow> 32 word) \<Rightarrow> (RName \<rightharpoonup> 32 word) \<Rightarrow> bool"
where
  "registers_related rs rs' rf = (
    register_related rs rs' rf RName_0usr \<and>
    register_related rs rs' rf RName_1usr \<and>
    register_related rs rs' rf RName_2usr \<and>
    register_related rs rs' rf RName_3usr \<and>
    register_related rs rs' rf RName_4usr \<and>
    register_related rs rs' rf RName_5usr \<and>
    register_related rs rs' rf RName_6usr \<and>
    register_related rs rs' rf RName_7usr \<and>
    register_related rs rs' rf RName_8usr \<and>
    register_related rs rs' rf RName_9usr \<and>
    register_related rs rs' rf RName_10usr \<and>
    register_related rs rs' rf RName_11usr \<and>
    register_related rs rs' rf RName_12usr \<and>
    register_related rs rs' rf RName_SPusr \<and>
    register_related rs rs' rf RName_LRusr
  )"

fun
  state_related :: "'a state_scheme \<Rightarrow> 'a state_scheme \<Rightarrow> (RName \<rightharpoonup> 32 word) \<Rightarrow> bool"
where
  "state_related s s' rf = (
    memory_related (MEM s) (MEM s') \<and>
    registers_related (REG s) (REG s') rf
  )"

lemma "\<lbrakk>
    Encoding s = Encoding_ARM;
    Extensions s = {};
    snd (Run (mov_imm 0 0) s) = s'
  \<rbrakk> \<Longrightarrow> state_related s s' (\<lambda>x. (if x = RName_0usr then Some 0 else None))
"
  apply (
    simp add:
      Run_def
      dfn'ArithLogicImmediate_def
      DataProcessing_def
      DataProcessingALU_def
      ExpandImm_C_def
      ARMExpandImm_C_def
      Shift_C_def
      snd_def
      word_extract_def
      word_bits_def
      mask_def
      write'R_def
      write'Rmode_def
      IsSecure_def
      HaveSecurityExt_def
      LookUpRName_def
      IncPC_def
      ThisInstrLength_def
      BranchTo_def
  )
  apply (auto)
  done

end
