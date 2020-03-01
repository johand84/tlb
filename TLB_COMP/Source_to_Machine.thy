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

fun
  comp_aexp :: "aexp \<Rightarrow> instruction list"
where
  "comp_aexp (Const v) = (
    if v < 0x1000
    then [mov_imm 0 (ucast v)]
    else [b_imm 0, Undefined v, ldr_lit False 0 12]
  )" |
  "comp_aexp (UnOp op a) = comp_aexp a @ comp_aunop op" |
  "comp_aexp (BinOp op a1 a2) = comp_aexp a2 @ push 0 # comp_aexp a1 @ pop 1 # comp_abinop op" |
  "comp_aexp (HeapLookup a) = comp_aexp a @ [ldr_imm False False False 0 0 0]"

fun
  comp_bunop :: "bunop \<Rightarrow> instruction list"
where
  "comp_bunop Not = cmp_imm 0 0 # moveq_imm 0 1 @ movne_imm 0 0"

fun
  comp_bbinop :: "bbinop \<Rightarrow> instruction list"
where
  "comp_bbinop And = [and_reg 0 0 1]" |
  "comp_bbinop Or = [or_reg 0 0 1]"

fun
  comp_bcomp :: "bcomp \<Rightarrow> instruction list"
where
  "comp_bcomp Less = cmp_reg 0 1 # movlt_imm 0 1 @ movge_imm 0 0"

end
