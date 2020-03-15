theory Source_to_MachineProofs

imports ARM_MnemonicProofs
        Source_to_Machine

begin

fun
  code_installed :: "'a::mmu state_scheme \<Rightarrow> instruction list \<Rightarrow>  bool"
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

(*
 * memory_related
 *
 * true if two memory spaces are equal
 *)
fun
  memory_related :: "(paddr \<rightharpoonup> byte) \<Rightarrow> (paddr \<rightharpoonup> byte) \<Rightarrow> bool"
where
  "memory_related m m' = (
    \<forall>x. m x = m' x
  )"

(*
 * state_related
 *
 * true if memory of state is related (equal) as memory of p_state.
 * Since p_state deals with words, the lambda returns the least significant
 * byte of each word, if it exists
 *
 * TODO Check more properties
 *)
fun
  state_related :: "'a::mmu state_scheme \<Rightarrow> p_state \<Rightarrow> bool"
where
  "state_related s t = memory_related (MEM s) (
    \<lambda>x. do {
      y \<leftarrow> (heap t) x;
      Some (ucast (y && 0xff))
    }
  )"

(* 
 * steps
 *
 * the state after i steps are executed
 *)
fun
  steps :: "'a::mmu state_scheme \<Rightarrow> nat \<Rightarrow> 'a::mmu state_scheme"
where
  "steps s 0 = s" |
  "steps s i = steps (snd (Next s)) (i-1)"

lemma comp_aunop_proof: "\<lbrakk>
  arm_preconditions s;
  c = comp_aunop op;
  x = REG s RName_0usr;
  code_installed s c;
  s' = steps s (length c)
\<rbrakk> \<Longrightarrow>
  s\<lparr>REG := (REG s)(RName_0usr := aunopval op x, RName_PC := REG s RName_PC + 4)\<rparr> = s'
"
  apply (induction op)
  apply (clarsimp simp: Next_def snd_def)
  apply (case_tac "Run (neg 0 0) ya", simp)
  apply (case_tac "ITAdvance () b", simp)
  apply (rule neg_proof)
  apply (auto)
  done

lemma comp_abinop_proof: "\<lbrakk>
  c = comp_abinop op;
  x = (REG s) RName_0usr;
  y = (REG s) RName_1usr;
  z = abinopval op x y;
  code_installed s c;
  s' = steps s (length c)
\<rbrakk> \<Longrightarrow>
  z = (REG s') RName_0usr
"
  apply(induction op)
  sorry

lemma comp_aexp_proof: "\<lbrakk>
  aval a t = Some v;
  code_installed s (comp_aexp a);
  state_related s t
\<rbrakk> \<Longrightarrow>
  \<exists>i. steps s i = s' \<and> state_related s' t'
"
  apply (induction a)
  sorry

lemma comp_bexp_proof: "\<lbrakk>
  bval b t = Some v;
  code_installed s (comp_bexp b);
  state_related s t
\<rbrakk> \<Longrightarrow>
  \<exists>i. steps s i = s' \<and> state_related s' t'
"
  apply (induction b)
  sorry

theorem compiler_correctness: "\<lbrakk>
  code_installed s (comp_com p);
  state_related s t;
  (p,t) \<Rightarrow> (Some t')
\<rbrakk> \<Longrightarrow> (
  \<exists>i. steps s i = s' \<and> state_related s' t'
)"
  sorry
end
