theory Source_to_MachineAssumptions

imports Source_to_Machine

begin

lemma Decode_add_reg_correct:
  "\<lbrakk>machine_config s;
    Decode (add_reg rd rn rm) s = (i,t)\<rbrakk> \<Longrightarrow>
      t = s \<and> i = Data (Register (0x4, False, rd, rn, rm, SRType_LSL, 0))"
  sorry

lemma Decode_and_reg_correct:
  "Decode (and_reg rd rn rm) t = (i,t') \<Longrightarrow> i = Data (Register (0x0, False, rd, rn, rm, SRType_LSL, 0))"
  sorry

lemma Decode_b_imm_correct:
  "Decode (b_imm imm24) s = (i,t) \<Longrightarrow> t = s \<and> i = Branch (BranchTarget (ucast imm24))"
  sorry

lemma Decode_cmp_imm_correct:
  "Decode (cmp_imm rn imm12) s = (i,t) \<Longrightarrow> t = s \<and> i = Data (ArithLogicImmediate (0xa, True, 0, rn, imm12))"
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
  "\<lbrakk>Decode (mov_imm rd imm12) s = (i,t);
    machine_config s\<rbrakk> \<Longrightarrow>
      s = t \<and>
      i = Data (ArithLogicImmediate (0xd, False, rd, 0, imm12))"
  sorry

lemma Decode_mov_reg_correct:
  "Decode (mov_reg rd rm) t = (i,t') \<Longrightarrow> i = Data (Register (0xd, False, rd, 0, rm, SRType_LSL, 0))"
  sorry

lemma Decode_moveq_imm_correct:
  "Decode (moveq_imm rd imm12) t = (i,t') \<Longrightarrow>
    i = (if PSR.Z (CPSR t) then Data (ArithLogicImmediate (0xd, False, rd, 0, imm12)) else NoOperation)"
  sorry

lemma Decode_movne_imm_correct:
  "Decode (movne_imm rd imm12) t = (i,t') \<Longrightarrow>
    i = (if PSR.Z (CPSR t) then NoOperation else Data (ArithLogicImmediate (0xd, False, rd, 0, imm12)))"
  sorry

lemma Decode_neg_correct:
  "Decode (neg rd rm) t = (i,t') \<Longrightarrow> i = Data (ArithLogicImmediate (0x3, False, rd, rm, imm12))"
  sorry

lemma Decode_or_reg_correct:
  "Decode (or_reg rd rn rm) t = (i,t') \<Longrightarrow> i = Data (Register (0xc, False, rd, rn, rm, SRType_LSL, 0))"
  sorry

lemma Decode_str_imm_correct:
  "Decode (str_imm rt rn imm12) t = (i,t') \<Longrightarrow>
    i = Store (StoreWord (False, False, False, rt, rn, immediate_form1 (ucast imm12)))"
  sorry

lemma Decode_sub_reg_correct:
  "Decode (sub_reg rd rn rm) t = (i,t') \<Longrightarrow> i = Data (Register (0x2, False, rd, rn, rm, SRType_LSL, 0))"
  sorry

end