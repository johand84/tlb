theory Source_to_Machine

imports TLB_COMP.Logic
        MMU_DEFS.MMU_Instants_TLB_PDC


begin

fun
  comp_com :: "com \<Rightarrow> MachineCode list"
where
  "comp_com SKIP = []"

end
