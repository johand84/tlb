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

lemma add_reg_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (add_reg 0 0 1 # ins);
    REG t RName_0usr = val1;
    REG t RName_1usr = val2\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = val1 + val2 \<and>
        REG t' RName_2usr = REG t RName_2usr"
  sorry

lemma and_reg_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (and_reg 0 0 1 # ins);
    REG t RName_0usr = val1;
    REG t RName_1usr = val2\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = val1 && val2"
  sorry

lemma b_imm_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (b_imm offset # ins1 @ ins2) \<rbrakk> \<Longrightarrow> True"
  sorry

lemma cmp_imm_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (cmp_imm 0 0 # ins);
    REG t RName_0usr = (if val then 1 else 0)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        (if val then \<not>PSR.Z (CPSR t') else PSR.Z (CPSR t'))"
  sorry

lemma ldr_imm_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (ldr_imm 0 0 0 # ins);
    mem_read_hp' (incon_set s) (heap s) (root s) (mode s) (Addr (REG t RName_0usr)) = Some val\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = val \<and>
        REG t' RName_2usr = REG t RName_2usr"
  sorry

lemma mov_imm_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (mov_imm reg (ucast val) # ins)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = (if reg = 0 then val else REG t RName_0usr) \<and>
        REG t' RName_1usr = (if reg = 1 then val else REG t RName_1usr) \<and>
        REG t' RName_2usr = REG t RName_2usr"
  sorry

lemma mov_reg_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (mov_reg 2 0 # ins);
    REG t' RName_0usr = val\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_2usr  = val"
  sorry

lemma moveq_imm_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (moveq_imm 0 (ucast val) # ins)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        PSR.Z (CPSR t') = PSR.Z (CPSR t) \<and>
        REG t' RName_0usr = (if PSR.Z (CPSR t) then val else REG t RName_0usr)"
  sorry

lemma movne_imm_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (movne_imm 0 (ucast val) # ins)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        PSR.Z (CPSR t') = PSR.Z (CPSR t) \<and>
        REG t' RName_0usr = (if PSR.Z (CPSR t) then REG t RName_0usr else val)"
  sorry

lemma neg_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (neg 0 0 # ins);
    REG t RName_0usr = val\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = -val \<and>
        REG t' RName_2usr = REG t RName_2usr"
  sorry

lemma or_reg_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (or_reg 0 0 1 # ins);
    REG t RName_0usr = val1;
    REG t RName_1usr = val2\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = val1 || val2"
  sorry

lemma str_imm_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (str_imm 0 2 0 # ins);
    REG t RName_0usr = val;
    addr_trans s (Addr (REG t RName_2usr)) = Some pp\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel (s\<lparr>heap := heap s(pp \<mapsto> val),
          p_state.incon_set := iset_upd s pp val,
          p_state.global_set := gset_upd s pp val\<rparr>) t'"
  sorry

end
