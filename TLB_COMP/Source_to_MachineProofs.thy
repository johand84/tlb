theory Source_to_MachineProofs

imports Source_to_Machine

begin

fun
  code_installed :: "'a set_tlb_state_scheme \<Rightarrow> MachineCode list \<Rightarrow>  bool"
where
  "code_installed s [] = True" |
  "code_installed s (x#xs) = (
    case Fetch s of (m,t) \<Rightarrow> m = x \<and> code_installed (
        t\<lparr>REG := (REG s)(RName_PC := REG s RName_PC + 4)\<rparr>
      )
      xs
  )"

definition
  heap_rel :: "p_state \<Rightarrow> 'a set_tlb_state_scheme \<Rightarrow> bool"
where
  "heap_rel s t = HOL.undefined"

definition
  machine_config :: "'a set_tlb_state_scheme \<Rightarrow> bool"
where
  "machine_config s = (
    Architecture s = ARMv7_A \<and>
    Encoding s = Encoding_ARM \<and>
    Extensions s = {} \<and>
    \<not>J (CPSR s) \<and>
    (PSR.M (CPSR s) = 0x10 \<or> PSR.M (CPSR s) = 0x13) \<and>
    \<not>T (CPSR s)
  )"

definition
  mode_rel :: "mode_t \<Rightarrow> 5 word \<Rightarrow> _"
where
  "mode_rel m cpsrm \<equiv>
   case m of
      Kernel => cpsrm = 0b10011
    | User   => cpsrm = 0b10000"

definition
  state_rel :: "p_state \<Rightarrow> 'a set_tlb_state_scheme \<Rightarrow> bool"
where
  "state_rel s t \<equiv>
     (asid s = ASID t) \<and>
     (root s = TTBR0 t) \<and>
     (p_state.incon_set s = set_tlb.iset (set_tlb t)) \<and>
     (p_state.global_set s = set_tlb.global_set (set_tlb t)) \<and>
     (HOL.undefined s = set_tlb.snapshot (set_tlb t)) \<and>
     mode_rel (mode s) (PSR.M (CPSR t)) \<and>
     heap_rel s t \<and>
     machine_config t"

fun
  steps :: "'a set_tlb_state_scheme \<Rightarrow> nat \<Rightarrow> 'a set_tlb_state_scheme"
where
  "steps s 0 = s" |
  "steps s (Suc i) = steps (snd (Next s)) i"

(* Proofs *)

lemma code_installed_append:
  "\<lbrakk>code_installed t (ca @ cb)\<rbrakk> \<Longrightarrow> code_installed t ca"
  by (induction ca arbitrary: t, clarsimp+)

lemma code_installed_prepend:
  "\<lbrakk>code_installed t (ca @ cb)\<rbrakk> \<Longrightarrow> code_installed (steps t (length ca)) cb"
  sorry

lemma steps_add:
  "(steps (steps t l1) l2) = (steps t (l1 + l2))"
  sorry

lemma steps_inc:
  "(snd (Next (steps t l))) = (steps (snd (Next t)) l)"
  sorry

lemma Decode_add_reg_correct:
  "Decode (add_reg rd rn rm) t = (i,t') \<Longrightarrow> i = Data (Register (0x4, False, rd, rn, rm, SRType_LSL, 0))"
  sorry

lemma Decode_and_reg_correct:
  "Decode (and_reg rd rn rm) t = (i,t') \<Longrightarrow> i = Data (Register (0x0, False, rd, rn, rm, SRType_LSL, 0))"
  sorry

lemma Decode_b_imm_correct:
  "Decode (b_imm imm24) t = (i,t') \<Longrightarrow> i = Branch (BranchTarget (ucast imm24))"
  sorry

lemma Decode_cmp_imm_correct:
  "Decode (cmp_imm rn imm12) t = (i,t') \<Longrightarrow> i = Data (ArithLogicImmediate (0xa, True, 0, rn, imm12))"
  sorry

lemma Decode_ldr_imm_correct:
  "Decode (ldr_imm rt rn imm12) t = (i,t') \<Longrightarrow>
    i = Load (LoadWord (False, False, False, rt, rn, immediate_form1 (ucast imm12)))"
  sorry

lemma Decode_ldr_lit_correct:
  "Decode (ldr_lit u rt imm12) t = (i,t') \<Longrightarrow> i = Load (LoadLiteral ((imm12 < 0), rt, (ucast imm12)))"
  sorry

lemma Decode_mov_imm_correct:
  "Decode (mov_imm rd imm12) t = (i,t') \<Longrightarrow> i = Data (ArithLogicImmediate (0xd, False, rd, 0, imm12))"
  sorry

end
