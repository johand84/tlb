theory Source_to_MachineAssumptions

imports Source_to_Machine

begin

lemma Decode_add_reg_correct:
  "machine_config s \<Longrightarrow> Decode (add_reg rd rn rm) s = (Data (Register (0x4, False, rd, rn, rm, SRType_LSL, 0)),s)"
  sorry

lemma Decode_and_reg_correct:
  "machine_config s \<Longrightarrow> Decode (and_reg rd rn rm) s = (Data (Register (0x0, False, rd, rn, rm, SRType_LSL, 0)),s)"
  sorry

lemma Decode_b_imm_correct:
  "Decode (b_imm imm24) s = (i,t) \<Longrightarrow> t = s \<and> i = Branch (BranchTarget (ucast imm24))"
  sorry

lemma Decode_cmp_imm_correct:
  "machine_config s \<Longrightarrow> Decode (cmp_imm rn imm12) s = (Data (ArithLogicImmediate (0xa, True, 0, rn, imm12)),s)"
  sorry

lemma Decode_ldr_imm_correct:
  "Decode (ldr_imm rt rn imm12) t = (i,t') \<Longrightarrow>
    i = Load (LoadWord (False, False, False, rt, rn, immediate_form1 (ucast imm12)))"
  sorry

lemma Decode_ldr_lit_correct:
  "Decode (ldr_lit u rt imm12) s = (i,t) \<Longrightarrow>
    s = t \<and>
    i = Load (LoadLiteral ((imm12 < 0), rt, (ucast imm12)))"
  sorry

lemma Decode_mov_imm_correct:
  "machine_config s \<Longrightarrow> Decode (mov_imm rd imm12) s = (Data (ArithLogicImmediate (0xd, False, rd, 0, imm12)),s)"
  sorry

lemma Decode_mov_reg_correct:
  "machine_config s \<Longrightarrow> Decode (mov_reg rd rm) t = (Data (Register (0xd, False, rd, 0, rm, SRType_LSL, 0)),s)"
  sorry

lemma Decode_moveq_imm_correct:
  "machine_config s \<Longrightarrow>
    Decode (moveq_imm rd imm12) s = ((if PSR.Z (CPSR s) then Data (ArithLogicImmediate (0xd, False, rd, 0, imm12)) else NoOperation),s)"
  sorry

lemma Decode_movne_imm_correct:
  "machine_config s \<Longrightarrow>
    Decode (movne_imm rd imm12) s = ((if PSR.Z (CPSR s) then NoOperation else Data (ArithLogicImmediate (0xd, False, rd, 0, imm12))),s)"
  sorry

lemma Decode_msr_reg_correct:
  "machine_config s \<Longrightarrow>
    Decode (msr_reg 0 m rn) s = (System (MoveToSpecialFromRegister (False, rn, m)),s)"
  sorry

lemma Decode_neg_correct:
  "machine_config s \<Longrightarrow> Decode (neg rd rm) s = (Data (ArithLogicImmediate (0x3, False, rd, rm, 0)),s)"
  sorry

lemma Decode_or_reg_correct:
  "machine_config s \<Longrightarrow> Decode (or_reg rd rn rm) t = (Data (Register (0xc, False, rd, rn, rm, SRType_LSL, 0)),s)"
  sorry

lemma Decode_str_imm_correct:
  "Decode (str_imm rt rn imm12) t = (i,t') \<Longrightarrow>
    i = Store (StoreWord (False, False, False, rt, rn, immediate_form1 (ucast imm12)))"
  sorry

lemma Decode_sub_reg_correct:
  "machine_config s \<Longrightarrow>
    Decode (sub_reg rd rn rm) s = (Data (Register (0x2, False, rd, rn, rm, SRType_LSL, 0)),s)"
  sorry

lemma Decode_tlbiall_correct:
  "machine_config s \<Longrightarrow> Decode tlbiall s = (CoprocessorInstruction (MoveToCoprocessorFromRegister (0,8,0,15,0,7)), s)"
  sorry

end