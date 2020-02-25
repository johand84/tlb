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

fun
  comp_bexp :: "bexp \<Rightarrow> instruction list"
where
  "comp_bexp (BConst v) = [mov_imm 0 (if v then 1 else 0)]" |
  "comp_bexp (BUnOp op b) = comp_bexp b @ comp_bunop op" |
  "comp_bexp (BBinOp op b1 b2) = comp_bexp b2 @ push 0 # comp_bexp b1 @ pop 1 # comp_bbinop op" |
  "comp_bexp (BComp op a1 a2) = comp_aexp a2 @ push 0 # comp_aexp a1 @ pop 1 # comp_bcomp op"

fun code_size ::
  "instruction list \<Rightarrow> 32 word"
where
  "code_size [] = 0" |
  "code_size ((IfThen _) # is) = code_size is" |
  "code_size (i#is) = code_size is + 4"

fun
  comp_com :: "com \<Rightarrow> instruction list"
where
  "comp_com SKIP = []" |
  "comp_com (Assign a1 a2) = comp_aexp a2 @ push 0 # comp_aexp a1 @ pop 1 # [str_imm False False False 0 1 0]" |
  "comp_com (Seq c1 c2) = (comp_com c1) @ (comp_com c2)" |
  "comp_com (If b c1 c2) = (
    let i1 = comp_com c1;
        i2 = comp_com c2
    in comp_bexp b @ cmp_imm 0 0 # beq_imm ((code_size i1) + 4) @ i1 @ b_imm (code_size i2) # i2
  )" |
  "comp_com (While b c) = (
    let i = comp_com c
    in comp_bexp b @ cmp_imm 0 0 # beq_imm ((code_size i) + 4) @ i @ [b_imm (code_size i)]
  )" |
  "comp_com c = []"

end
