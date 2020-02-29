theory Source_to_Machine

imports ARM_ConditionalMnemonic
        TLB_COMP.Logic
        TLB_COMP.MMU_Instants_TLB_PDC


begin

fun
  comp_aunop :: "aunop \<Rightarrow> instruction list"
where
  "comp_aunop Neg = [neg 0 0]"

fun
  comp_abinop :: "abinop \<Rightarrow> instruction list"
where
  "comp_abinop Plus = [add_reg 0 0 1]" |
  "comp_abinop Minus = [sub_reg 0 0 1]"

end
