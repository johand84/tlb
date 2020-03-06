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

fun
  memory_related :: "(paddr \<rightharpoonup> byte) \<Rightarrow> (paddr \<rightharpoonup> byte) \<Rightarrow> bool"
where
  "memory_related m m' = (
    \<forall>x. m x = m' x
  )"

(* TODO Change the lambda into something returning bytes *)
fun
  state_related :: "'a::mmu state_scheme \<Rightarrow> p_state \<Rightarrow> bool"
where
  "state_related s t = memory_related (MEM s) (
    \<lambda>x. do {
      Some 0
    }
  )"

end
