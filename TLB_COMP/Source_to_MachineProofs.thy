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

end
