theory Source_to_MachineProofs

imports Source_to_Machine

begin

fun
  fetch_decode :: "'a::mmu state_scheme \<Rightarrow> instruction \<times> 'a::mmu state_scheme"
where
  "fetch_decode s = (let (m,s') = Fetch s in Decode m s')"

fun
  code_installed :: "'a::mmu state_scheme \<Rightarrow> instruction list \<Rightarrow>  bool"
where
  "code_installed s [] = True" |
  "code_installed s (i#is) = (
    let (j,s') = fetch_decode s
    in i=j \<and> code_installed s' is
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

theorem compiler_correctness: "\<lbrakk>
  code_installed s (comp_com p);
  state_related s t;
  (p,t) \<Rightarrow> (Some t')
\<rbrakk> \<Longrightarrow> (
  \<exists>i. steps s i = s' \<and> state_related s' t'
)"
  sorry
end
