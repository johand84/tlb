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

end