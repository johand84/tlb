theory ARM_ConditionalMnemonicProofs
  imports ARM_ConditionalMnemonic
          ARM_MnemonicProofs
begin

lemma Decode_test_true:
"\<lbrakk>
  Decode (ARM 0x0A000000) s = (i,s2);
  PSR.Z (CPSR s)
   \<rbrakk> \<Longrightarrow> i = Branch (BranchTarget 0)"
  apply (clarsimp simp: Decode_def)
  apply (clarsimp simp: DecodeARM_def mask_def word_bits_def word_extract_def split: if_split_asm prod.splits)
   apply (clarsimp simp: Do_def word_cat_def split: prod.splits)
  apply(clarsimp simp: ConditionPassed_def CurrentCond_def Do_def word_bits_def word_extract_def split: if_split_asm prod.splits)
  done

lemma Decode_test_false:
"\<lbrakk>
  Decode (ARM 0x0A000000) s = (i,s2);
  \<not>PSR.Z (CPSR s)
   \<rbrakk> \<Longrightarrow> i = NoOperation"
  apply (clarsimp simp: Decode_def)
  apply (clarsimp simp: DecodeARM_def mask_def word_bits_def word_extract_def split: if_split_asm prod.splits)
   apply (clarsimp simp: Do_def word_cat_def split: prod.splits)
   apply(clarsimp simp: ConditionPassed_def CurrentCond_def mask_def word_bits_def word_extract_def split: if_split_asm prod.splits)
  apply (clarsimp simp: Do_def word_cat_def split: prod.splits)
  apply(clarsimp simp: ConditionPassed_def CurrentCond_def mask_def word_bits_def word_extract_def split: if_split_asm prod.splits)
  apply(clarsimp simp: Skip_def)

  done

lemma eq_proof:
"\<lbrakk>arm_preconditions s; Run eq s = s'\<rbrakk> \<Longrightarrow> True"
  sorry

end
