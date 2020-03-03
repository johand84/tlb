theory ARM_MnemonicProofs
  imports ARM_Mnemonic
          TLB_COMP.MMU_Instants_TLB_PDC
begin

lemma "\<lbrakk>
    Encoding s = Encoding_ARM;
    Extensions s = {}
  \<rbrakk> \<Longrightarrow> ((REG (snd (Run (mov_imm 0 0) s))) RName_0usr) = 0
"
  apply (simp add: Run_def)
  apply (simp add: dfn'ArithLogicImmediate_def)
  apply (simp add: DataProcessing_def)
  apply (simp add: DataProcessingALU_def)
  apply (simp add: ExpandImm_C_def)
  apply (simp add: ARMExpandImm_C_def)
  apply (simp add: Shift_C_def)
  apply (simp add: write'R_def)
  apply (simp add: write'Rmode_def)
  apply (simp add: IsSecure_def)
  apply (simp add: HaveSecurityExt_def)
  apply (simp add: LookUpRName_def)
  apply (simp add: IncPC_def)
  apply (simp add: ThisInstrLength_def)
  apply (simp add: BranchTo_def)
  apply (simp add: L3_Lib.word_extract_def)
  apply (simp add: L3_Lib.word_bits_def)
  apply (simp add: mask_def)
  done

end