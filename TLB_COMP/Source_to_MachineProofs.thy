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

lemma sub_reg_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (sub_reg 0 0 1 # ins);
    REG t RName_0usr = val1;
    REG t RName_1usr = val2\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = val1 - val2 \<and>
        REG t' RName_2usr = REG t RName_2usr"
  sorry

lemma comp_aexp_mov_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (comp_aexp_mov reg val @ ins)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t (length (comp_aexp_mov reg val)) = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = (if reg = 0 then val else REG t RName_0usr) \<and>
        REG t' RName_1usr = (if reg = 1 then val else REG t RName_1usr) \<and>
        REG t' RName_2usr = REG t RName_2usr"
  apply (simp only: comp_aexp_mov_def split: if_split_asm)
   apply (drule mov_imm_correct, simp, safe, simp)
   apply (drule_tac insa = "[ARM val]" and insb = "ldr_lit 0 reg 0xC # ins" in b_imm_correct)
   apply (simp add: code_size_def word_arith_wis word_of_int_def, safe)
  apply (drule_tac ins = "ins" and reg = "reg" and val = "val" in ldr_lit_correct, simp)
  sorry

lemma comp_aexp_Const_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some val; code_installed t (comp_aexp e @ ins); state_rel s t; e = Const x1\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = val \<and>
      REG t' RName_2usr = REG t RName_2usr"
  apply (simp)
  apply (drule comp_aexp_mov_correct, simp+)
  done

lemma comp_aexp_UnOp_Neg_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some val'; code_installed t (comp_aexp e @ ins); state_rel s t; e = UnOp op val; op = Neg\<rbrakk> \<Longrightarrow> 
    \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = val' \<and>
      REG t' RName_2usr = REG t RName_2usr"
  apply (frule comp_aexp_mov_correct, simp, safe)
  apply (drule neg_correct, simp, simp, safe)
  apply (simp add: steps_inc)
  done

lemma comp_aexp_UnOp_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some val'; code_installed t (comp_aexp e @ ins); state_rel s t; e = UnOp op val\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = val' \<and>
      REG t' RName_2usr = REG t RName_2usr"
  apply (cases op)
  apply (rule comp_aexp_UnOp_Neg_correct, force+)
  done

lemma comp_aexp_BinOp_Plus_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some val; code_installed t (comp_aexp e @ ins); state_rel s t; e = BinOp op val1 val2; op = Plus\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = val \<and>
      REG t' RName_2usr = REG t RName_2usr"
  apply (drule comp_aexp_mov_correct, simp, safe)
  apply (drule comp_aexp_mov_correct, simp, safe)
  apply (drule add_reg_correct, simp, simp, simp, safe)
  apply (simp add: steps_add steps_inc)
  done

lemma comp_aexp_BinOp_Minus_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some val; code_installed t (comp_aexp e @ ins); state_rel s t; e = BinOp op val1 val2; op = Minus\<rbrakk>
    \<Longrightarrow> \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = val \<and>
      REG t' RName_2usr = REG t RName_2usr"
  apply (drule comp_aexp_mov_correct, simp, safe)
  apply (drule comp_aexp_mov_correct, simp, safe)
  apply (drule sub_reg_correct, simp, simp, simp, safe)
  apply (simp add: steps_add steps_inc)
  done

lemma comp_aexp_BinOp_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some val; code_installed t (comp_aexp e @ ins); state_rel s t; e = BinOp op val1 val2\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = val \<and>
      REG t' RName_2usr = REG t RName_2usr"
  apply (cases op)
   apply (rule comp_aexp_BinOp_Plus_correct, force+)
  apply (rule comp_aexp_BinOp_Minus_correct, force+)
  done

lemma comp_aexp_HeapLookup_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some val; code_installed t (comp_aexp e @ ins); state_rel s t; e = HeapLookup x4\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = val \<and>
      REG t' RName_2usr = REG t RName_2usr"
  apply (drule comp_aexp_mov_correct, simp, safe)
  apply (drule ldr_imm_correct, simp, simp, safe)
  apply (simp add: steps_add steps_inc)
  done

lemma comp_aexp_correct:
  "\<lbrakk>aval e s = Some val;
    code_installed t (comp_aexp e @ ins);
    state_rel s t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = val \<and>
        REG t' RName_2usr = REG t RName_2usr"
  apply (cases e)
     apply (rule comp_aexp_Const_correct, force+)
    apply (rule comp_aexp_UnOp_correct, force+)
   apply (rule comp_aexp_BinOp_correct, force+)
  apply (rule comp_aexp_HeapLookup_correct, force+)
  done

lemma comp_bexp_mov_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (comp_bexp_mov reg val @ ins)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t (length (comp_bexp_mov reg val)) = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = (if reg = 0 then (if val then 1 else 0) else REG t RName_0usr) \<and>
        REG t' RName_1usr = (if reg = 1 then (if val then 1 else 0) else REG t RName_1usr)"
  apply (cases val)
   apply (simp only: comp_bexp_mov_def)
   apply (drule_tac val = "1" in mov_imm_correct, simp, safe, simp)
  apply (simp only: comp_bexp_mov_def)
  apply (drule_tac val = "0" in mov_imm_correct, simp, safe, simp)
  done

lemma comp_bexp_BConst_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val; code_installed t (comp_bexp b @ ins); state_rel s t; b = BConst x\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_bexp b)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = (if val then 1 else 0)"
  apply (drule comp_bexp_mov_correct, simp, simp)
  done

lemma comp_bexp_BComp_Less_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val; code_installed t (comp_bexp b @ ins); state_rel s t; b = BComp op a1 a2; op = Less\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_bexp b)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = (if val then 1 else 0)"
  sorry

lemma comp_bexp_BComp_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val; code_installed t (comp_bexp b @ ins); state_rel s t; b = BComp op a1 a2\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_bexp b)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = (if val then 1 else 0)"
  apply (cases op)
  apply (rule comp_bexp_BComp_Less_correct, force+)
  done

lemma comp_bexp_BBinOp_And_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val; code_installed t (comp_bexp b @ ins); state_rel s t; b = BBinOp op b1 b2; op = And\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_bexp b)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = (if val then 1 else 0)"
  apply (drule comp_bexp_mov_correct, simp, safe)
  apply (drule comp_bexp_mov_correct, simp, safe)
  apply (drule and_reg_correct, simp, simp, simp, safe)
  apply (simp add: steps_add steps_inc, safe)
  done

lemma comp_bexp_BBinOp_Or_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val; code_installed t (comp_bexp b @ ins); state_rel s t; b = BBinOp op b1 b2; op = Or\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_bexp b)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = (if val then 1 else 0)"
  apply (drule comp_bexp_mov_correct, simp, safe)
  apply (drule comp_bexp_mov_correct, simp, safe)
  apply (drule or_reg_correct, simp, simp, simp, safe)
  apply (simp add: steps_add steps_inc, safe)
  done

lemma comp_bexp_BBinOp_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val; code_installed t (comp_bexp b @ ins); state_rel s t; b = BBinOp op b1 b2\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_bexp b)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = (if val then 1 else 0)"
  apply (cases op)
   apply (rule comp_bexp_BBinOp_And_correct, force+)
  apply (rule comp_bexp_BBinOp_Or_correct, force+)
  done

lemma comp_bexp_BUnOp_Not_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val; code_installed t (comp_bexp b @ ins); state_rel s t; b = BUnOp op a; op = bunop.Not\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_bexp b)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = (if val then 1 else 0)"
  apply (cases val)
   apply (drule_tac ins = "cmp_imm 0 0 # moveq_imm 0 1 # movne_imm 0 0 # ins" in comp_bexp_mov_correct, simp, safe)
   apply (drule_tac ins = "moveq_imm 0 1 # movne_imm 0 0 # ins" in cmp_imm_correct, simp, simp, safe)
   apply (drule_tac ins = "movne_imm 0 0 # ins" and val = "1" in moveq_imm_correct, simp, safe)
    apply (drule_tac ins = "ins" and val = "0" in movne_imm_correct, simp, safe)
    apply (simp add: comp_bexp_mov_def)
   apply (drule_tac ins = "ins" and val = "0" in movne_imm_correct, simp, safe)
   apply (simp add: comp_bexp_mov_def)
  apply (drule_tac ins = "cmp_imm 0 0 # moveq_imm 0 1 # movne_imm 0 0 # ins" in comp_bexp_mov_correct, simp, safe)
  apply (drule_tac ins = "moveq_imm 0 1 # movne_imm 0 0 # ins" in cmp_imm_correct, simp, simp, safe)
  apply (drule_tac ins = "movne_imm 0 0 # ins" and val = "1" in moveq_imm_correct, simp, safe)
   apply (drule_tac ins = "ins" and val = "0" in movne_imm_correct, simp, safe)
   apply (simp add: comp_bexp_mov_def)
  apply (drule_tac ins = "ins" and val = "0" in movne_imm_correct, simp, safe)
  apply (simp add: comp_bexp_mov_def)
  done

lemma comp_bexp_BUnOp_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val; code_installed t (comp_bexp b @ ins); state_rel s t; b = BUnOp op a\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_bexp b)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = (if val then 1 else 0)"
  apply (cases op)
  apply (rule comp_bexp_BUnOp_Not_correct, force+)
  done

lemma comp_bexp_correct:
  "\<lbrakk>bval e s = Some value;
    code_installed t (comp_bexp e @ ins);
    state_rel s t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t (length (comp_bexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      REG t' RName_0usr = (if value then 1 else 0)"
  apply (cases e)
     apply (rule comp_bexp_BConst_correct, force+)
    apply (rule comp_bexp_BComp_correct, force+)
   apply (rule comp_bexp_BBinOp_correct, force+)
  apply (rule comp_bexp_BUnOp_correct, force+)
  done

lemma comp_Assign_correct:
  "\<lbrakk>\<lbrakk>lval\<rbrakk> s = Some vp;
    \<lbrakk>rval\<rbrakk> s = Some v;
    Addr vp \<notin> incon_set s;
    addr_trans s (Addr vp) = Some pp;
    code_installed t (comp_aexp lval @ mov_reg 2 0 # comp_aexp rval @ str_imm 0 2 0 # ins);
    state_rel s t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps (snd (Next (snd (Next t)))) (length (comp_aexp lval) + length (comp_aexp rval)) = t' \<and>
        code_installed t' ins \<and>
        state_rel (s\<lparr>heap := heap s(pp \<mapsto> v), incon_set := iset_upd s pp v, p_state.global_set := gset_upd s pp v\<rparr>) t'"
  apply (drule_tac ins = "mov_reg 2 0 # comp_aexp rval @ str_imm 0 2 0 # ins" in comp_aexp_correct, simp, simp, safe)
  apply (drule_tac ins = "comp_aexp rval @ str_imm 0 2 0 # ins" and val = "vp" in mov_reg_correct, simp, simp, safe)
  apply (drule_tac ins = "str_imm 0 2 0 # ins" in comp_aexp_correct, simp, simp, safe)
  apply (drule_tac ins = "ins" and pp = "pp" in str_imm_correct, simp, simp, simp, safe)
  apply (simp add: steps_add steps_inc)
  done

lemma comp_Seq_correct:
  "\<lbrakk>\<forall>t::'a set_tlb_state_scheme. code_installed t (comp_com c1) \<and> state_rel s1 t \<longrightarrow> state_rel s2 (steps t (length (comp_com c1)));
    \<forall>t::'a set_tlb_state_scheme. code_installed t (comp_com c2) \<and> state_rel s2 t \<longrightarrow> state_rel y (steps t (length (comp_com c2)));
    code_installed (t::'a set_tlb_state_scheme) (comp_com c1 @ comp_com c2);
    state_rel s1 t\<rbrakk>
       \<Longrightarrow> state_rel y (steps t (length (comp_com c1) + length (comp_com c2)))"
  apply (frule code_installed_append)
  apply (subgoal_tac "state_rel s2 (steps t (length (comp_com c1)))")
   apply (drule code_installed_prepend)
   apply (subgoal_tac "state_rel y (steps (steps t (length (comp_com c1))) (length (comp_com c2)))")
    apply (clarsimp simp: steps_add)
  by (force+)

lemma comp_IfTrue_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some True; (c1, s) \<Rightarrow> Some y;
   \<And>t. \<lbrakk>code_installed t (comp_com c1); state_rel s t\<rbrakk> \<Longrightarrow> state_rel y (steps t (length (comp_com c1)));
   code_installed ta (comp_com (IF b THEN c1 ELSE c2)); state_rel s ta\<rbrakk> \<Longrightarrow>
    state_rel y (steps ta (length (comp_com (IF b THEN c1 ELSE c2))))"
  sorry

lemma comp_IfFalse_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some False; (c2, s) \<Rightarrow> Some y;
        \<And>t. \<lbrakk>code_installed t (comp_com c2); state_rel s t\<rbrakk> \<Longrightarrow> state_rel y (steps t (length (comp_com c2)));
        code_installed ta (comp_com (IF b THEN c1 ELSE c2)); state_rel s ta\<rbrakk>
       \<Longrightarrow> state_rel y (steps ta (length (comp_com (IF b THEN c1 ELSE c2))))"
  sorry

lemma comp_WhileFalse_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some False; code_installed t (comp_com (WHILE b DO c)); state_rel s t\<rbrakk>
       \<Longrightarrow> state_rel s (steps t (length (comp_com (WHILE b DO c))))"
  sorry

lemma comp_WhileTrue_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some True; (c, s) \<Rightarrow> Some s'';
        \<And>t. \<lbrakk>code_installed t (comp_com c); state_rel s t\<rbrakk> \<Longrightarrow> state_rel s'' (steps t (length (comp_com c))); (WHILE b DO c, s'') \<Rightarrow> Some y;
        \<And>t. \<lbrakk>code_installed t (comp_com (WHILE b DO c)); state_rel s'' t\<rbrakk> \<Longrightarrow> state_rel y (steps t (length (comp_com (WHILE b DO c))));
        code_installed t (comp_com (WHILE b DO c)); state_rel s t\<rbrakk>
       \<Longrightarrow> state_rel y (steps t (length (comp_com (WHILE b DO c))))"
  sorry

lemma comp_Flush_correct:
  "\<lbrakk>mode s = Kernel; code_installed t (comp_com (Flush f)); state_rel s t\<rbrakk>
       \<Longrightarrow> state_rel
            (s\<lparr>incon_set := flush_effect_iset f (incon_set s) (p_state.global_set s) (asid s),
                 p_state.global_set := flush_effect_glb f (p_state.global_set s) (asid s) (heap s) (root s),
                 ptable_snapshot := flush_effect_snp f (ptable_snapshot s) (asid s)\<rparr>)
            (steps t (length (comp_com (Flush f))))"
  sorry

lemma comp_UpdateTTBR0_correct:
  "\<lbrakk>mode s = Kernel; \<lbrakk>rte\<rbrakk> s = Some rt; code_installed t (comp_com (UpdateTTBR0 rte)); state_rel s t\<rbrakk>
       \<Longrightarrow> state_rel
            (s\<lparr>root := Addr rt, incon_set := incon_set s \<union> MMU_Prg_Logic.incon_comp (asid s) (asid s) (heap s) (heap s) (root s) (Addr rt),
                 p_state.global_set :=
                   p_state.global_set s \<union>
                   \<Union> (MMU_Prg_Logic.range_of ` MMU_Prg_Logic.global_entries (ran (MMU_Prg_Logic.pt_walk (asid s) (heap s) (Addr rt))))\<rparr>)
            (steps t (length (comp_com (UpdateTTBR0 rte))))"
  sorry

end
