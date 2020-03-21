theory Aexp_to_MachineProof
imports ARM_MnemonicProofs
        Source_to_Machine
begin

fun
  code_installed :: "'a set_tlb_state_scheme \<Rightarrow> instruction list \<Rightarrow>  bool"
where
  "code_installed s [] = True" |
  "code_installed s (i#is) = (
    case Fetch s of (m,s1) \<Rightarrow> (
      case Decode m s1 of (j,s2) \<Rightarrow> i=j \<and> code_installed (
        s2\<lparr>REG := (REG s)(RName_PC := REG s RName_PC + 4)\<rparr>
      )
      is
    )
  )"

fun
  steps :: "'a set_tlb_state_scheme \<Rightarrow> nat \<Rightarrow> 'a set_tlb_state_scheme"
where
  "steps s 0 = s" |
  "steps s (Suc i) = steps (snd (Next s)) i"

(*
record p_state =
  heap      :: heap
  asid      :: asid 
  root      :: paddr
  incon_set :: incon_set
  global_set :: global_set
  ptable_snapshot :: ptable_snapshot
  mode      :: mode_t
*)

definition
  machine_config :: "'a set_tlb_state_scheme \<Rightarrow> bool"
where
  "machine_config s = (
    Architecture s = ARMv7_A \<and>
    Encoding s = Encoding_ARM \<and>
    Extensions s = {} \<and>
    \<not>J (CPSR s) \<and>
    \<not>T (CPSR s)
  )"

definition
  heap_rel :: "p_state \<Rightarrow> 'a set_tlb_state_scheme \<Rightarrow> bool"
where
  "heap_rel s t = HOL.undefined"

(*
 * TODO
 * Figure out mode in ARM/CPSR
 * Figure out heap_rel: SP holds virtual address. push/pop use SP,
 * heaps will be identical except the stack region
 *)
definition
  state_rel :: "p_state \<Rightarrow> 'a set_tlb_state_scheme \<Rightarrow> bool"
where
  "state_rel s t \<equiv>
     (asid s = ASID t) \<and>
     (root s = TTBR0 t) \<and>
     (incon_set s = set_tlb.iset (set_tlb t)) \<and>
     (HOL.undefined s = set_tlb.global_set (set_tlb t)) \<and>
     (HOL.undefined s = set_tlb.snapshot (set_tlb t)) \<and>
     (mode s = HOL.undefined t) \<and>
     heap_rel s t \<and>
     machine_config t"

(*
(\<exists>v. e = Const v \<or> (\<exists>a v. e = UnOp a (Const v)) \<or> 
     (\<exists>b v v'. e = BinOp b (Const v) (Const v')) \<or>
     (\<exists>v. e = HeapLookup (Const v)))
*)

lemma abc: "\<lbrakk>first_assumption; second_assumption\<rbrakk> \<Longrightarrow> something\<and>first_assumption"
  sorry

lemma "P \<and> P' \<Longrightarrow> P"
  apply (erule conjE)
  apply assumption
  done

lemma "\<lbrakk>R'; Z'\<rbrakk> \<Longrightarrow> R'"
  apply (drule_tac first_assumption = "R'" and second_assumption = "Z'" in abc)
   apply assumption
  sorry

lemma itadvance_RName_0usr_eq:
  "REG (snd (ITAdvance () s)) RName_0usr = 
    REG s RName_0usr"
  apply (clarsimp simp: ITAdvance_def split: prod.splits)
  apply (safe;clarsimp?)
  by (clarsimp simp: HaveThumb2_def ITSTATE_def write'ITSTATE_def split: prod.splits)+

lemma incpc_RName_0usr:
  "IncPC () s = ((), t) \<Longrightarrow> 
   state.REG t RName_0usr = state.REG s RName_0usr "
  sorry

(* using [[show_types]] *)
(* declare [[show_types]] *)
(* apply (subgoal_tac "something") *)
lemma word_extracts_d: 
  "L3_Lib.word_extract 3 2 (0xD::4 word) \<noteq> (2::2 word)"
  by (clarsimp simp: word_extract_def word_bits_def mask_def)
  

lemma comp_aexp_proof_Const_1:
  "\<lbrakk>state_rel s t; e = Const val; val < 0x1000; Fetch t = (x, y); Decode x y = (mov_imm 0 (UCAST(32 \<rightarrow> 12) val), ya);
        Run (mov_imm 0 (UCAST(32 \<rightarrow> 12) val)) ya = ((), x2)\<rbrakk>
       \<Longrightarrow> state.REG x2 RName_0usr = val"
apply (clarsimp simp: mov_imm_def Run_def dfn'ArithLogicImmediate_def split: prod.splits)

      (* update comp expression to remove v < 0x1000 
         open ExpandImm_C, then prove not IsSecure and keep processing *)

      apply (clarsimp simp: DataProcessing_def DataProcessingALU_def word_extracts_d split: prod.splits)
      apply (clarsimp simp: write'R_def)
      apply (drule incpc_RName_0usr, simp)
      (*apply (thin_tac "state.REG x2 RName_0usr = state.REG x2b RName_0usr")*)
      apply (clarsimp simp: write'Rmode_def split: prod.splits)
      


      apply (subgoal_tac "\<not>(\<not> x1 \<and> PSR.M (CPSR x2a) = 0x16)",simp)
      apply(subgoal_tac "x1",simp)
  sorry

lemma comp_aexp_proof: 
  "\<lbrakk>aval e s = Some val;
    code_installed t (comp_aexp e);
    state_rel s t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t (length (comp_aexp e)) = t' \<and> REG t' RName_0usr = val"
 (*
 apply(case_tac e;clarsimp)
     apply (clarsimp split: if_split_asm)
      apply (rule_tac x="1" in exI, clarsimp)
      apply (clarsimp simp: Next_def)
      apply (clarsimp split: prod.splits)
      apply (clarsimp simp: itadvance_RName_0usr_eq)
  apply(clarsimp simp: comp_aexp_proof_Const_1)
*)
  sorry

lemma comp_bexp_proof: 
  "\<lbrakk>bval e s = Some val;
    code_installed t (comp_bexp e);
    state_rel s t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t (length (comp_bexp e)) = t' \<and> REG t' RName_0usr = (if val then 1 else 0)"
  
  sorry

(* s\<lparr>REG := (REG s)(RName_0usr := aunopval op x, RName_PC := REG s RName_PC + 4)\<rparr> = s' *)

lemma comp_aexp_proof': 
  "\<lbrakk>aval e s = Some val;
    code_installed t (comp_aexp e @ ins);
    state_rel s t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      REG t' RName_0usr = val"
 (* apply(case_tac e;clarsimp)
     apply (clarsimp split: if_split_asm)
      apply (rule_tac x="1" in exI, clarsimp)
      apply (clarsimp simp: Next_def)
      apply (clarsimp split: prod.splits)
      apply (clarsimp simp: itadvance_RName_0usr_eq)
  apply(clarsimp simp: comp_aexp_proof_Const_1) *)
  sorry

lemma state_rel_mov_ins:
  "\<lbrakk>state_rel s t ; 
   code_installed t (mov_reg 1 0 # ins) \<rbrakk>\<Longrightarrow>
   code_installed (snd (Next t)) ins \<and> state_rel s (snd (Next t)) \<and>
   REG (snd (Next t)) RName_1usr = REG t RName_0usr"

  sorry

lemma  state_rel_str_imm:
  "\<lbrakk>code_installed t [str_imm False False False 0 1 0]; state_rel s t;
    addr_trans s (Addr (REG t RName_1usr)) = Some pp;
   val = REG t RName_0usr\<rbrakk> \<Longrightarrow>
   state_rel (s\<lparr>heap := heap s(pp \<mapsto> val),
                     incon_set := iset_upd s pp val,
                     global_set := gset_upd s pp val\<rparr>) (snd (Next t))"

  sorry

lemma ptable_lift_mov_ins:
"\<lbrakk> code_installed t (mov_reg 1 0 # ins);
   addr_trans s (Addr (state.REG t RName_0usr)) = Some pp;
   state_rel s t \<rbrakk> \<Longrightarrow> 
     addr_trans s (Addr (REG (snd (Next t)) RName_1usr)) = Some pp"
  sorry

lemma ptable_lift_aexp: 
  "\<lbrakk>code_installed t (comp_aexp e @ ins);
    addr_trans s (Addr (state.REG t RName_1usr)) = Some pp;
    state_rel s t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
     addr_trans s (Addr (REG t' RName_1usr)) = Some pp"
  sorry

(*
not being used anywhere
lemma val_str_imm:
  "\<lbrakk>code_installed t [str_imm False False False 0 1 0];
    state_rel
         (s\<lparr>heap := heap s(pp \<mapsto> the (\<lbrakk>rval\<rbrakk> s)), incon_set := HOL.undefined, p_state.global_set := HOL.undefined\<rparr>)
         (snd (Next t))\<rbrakk> \<Longrightarrow> state_rel
            (s\<lparr>heap := heap s(pp \<mapsto> state.REG t RName_0usr),
                 incon_set := HOL.undefined, p_state.global_set := HOL.undefined\<rparr>)
            (steps (snd (Next (snd (Next t)))) (length (comp_aexp lval) + length (comp_aexp rval)))"
  sorry
*)

lemma code_installed_append:
  "\<lbrakk>code_installed t (c @ c')\<rbrakk> \<Longrightarrow> code_installed t c"
  sorry

lemma code_installed_prepend:
  "\<lbrakk>code_installed t (c @ c')\<rbrakk> \<Longrightarrow> code_installed (steps t (length c)) c'"
  sorry

lemma steps_add: "steps (steps t i) i' = steps t (i+i')"
  sorry

lemma steps_inc: "snd (Next (steps t i)) = steps t (i+1)"
  sorry

lemma comp_com_correct:
  "\<lbrakk>(p, s) \<Rightarrow> st; 
    st \<noteq> None; state_rel s t;
    code_installed t (comp_com p) \<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t (length (comp_com p)) = t' \<and> state_rel (the st) t'"
  apply (induction arbitrary: t rule: big_step_induct; clarsimp)
           apply (frule_tac t = "t" and ins = "mov_reg 1 0 # comp_aexp rval @ [str_imm False False False 0 1 0]" in comp_aexp_proof', simp, simp)
           apply safe 
           apply (frule_tac t = "steps t (length (comp_aexp lval))" and ins = "comp_aexp rval @ [str_imm False False False 0 1 0]" in state_rel_mov_ins, simp)
           apply safe
           apply (frule_tac t = "(snd (Next (steps t (length (comp_aexp lval)))))" and ins = "[str_imm False False False 0 1 0]" in comp_aexp_proof',simp,simp)
           apply safe  (* state.REG t' RName_0usr = v *)
           apply (frule_tac s = "s" and t = "steps (snd (Next (steps t (length (comp_aexp lval))))) (length (comp_aexp rval))" and pp = "pp" and val = "the (aval rval s)" in state_rel_str_imm, simp)
             apply (frule_tac s = "s" and t = "steps t (length (comp_aexp lval))" and ins = "comp_aexp rval @ [str_imm False False False 0 1 0]" and pp = "pp" in ptable_lift_mov_ins, simp)
              apply safe
             apply (frule_tac t = "snd (Next (steps t (length (comp_aexp lval))))" and ins = "[str_imm False False False 0 1 0]" and pp = "pp" in ptable_lift_aexp,simp,simp,simp)
            apply (clarsimp)
           apply(simp add: steps_add steps_inc)
          (* Seq case *)
          apply(frule code_installed_append)
          apply(subgoal_tac "state_rel s2 (steps t (length (comp_com c1)))") prefer 2
           apply(force)
          apply(frule code_installed_prepend)
          apply (subgoal_tac "state_rel y (steps (steps t (length (comp_com c1))) (length (comp_com c2)))") prefer 2
           apply (force)
          apply(simp add: steps_add)

  oops

    

  


end