theory Source_to_Machine

imports TLB_COMP.Logic
        MMU_DEFS.MMU_Instants_TLB_PDC
        Mnemonics


begin

fun
  comp_aunop :: "aunop \<Rightarrow> MachineCode list"
where
  "comp_aunop Neg = [neg 0 0]"

fun
  comp_abinop :: "abinop \<Rightarrow> MachineCode list"
where
  "comp_abinop Plus = [add_reg 0 0 1]" |
  "comp_abinop Minus = [sub_reg 0 0 1]"

definition
  comp_aexp_mov :: "4 word \<Rightarrow> 32 word \<Rightarrow> MachineCode list"
where
  "comp_aexp_mov rt v = (
    if word_extract 31 8 v = (0::24 word)
    then [mov_imm rt (ucast v)]
    else [b_imm 0, (ARM v), ldr_lit 0 rt 12]
  )"

fun
  comp_aexp :: "aexp \<Rightarrow> MachineCode list"
where
  "comp_aexp (Const v) = comp_aexp_mov 0 v" |
  "comp_aexp (UnOp op a) = comp_aexp_mov 0 a @ comp_aunop op" |
  "comp_aexp (BinOp op a1 a2) = comp_aexp_mov 0 a1 @ comp_aexp_mov 1 a2 @ comp_abinop op" |
  "comp_aexp (HeapLookup a) = comp_aexp_mov 0 a @ [ldr_imm 0 0 0]"

definition
  comp_bexp_mov :: "4 word \<Rightarrow> bool \<Rightarrow> MachineCode list"
where
  "comp_bexp_mov rt v = [mov_imm rt (if v then 1 else 0)]"

fun
  comp_bunop :: "bunop \<Rightarrow> MachineCode list"
where
  "comp_bunop Not = [cmp_imm 0 0, moveq_imm 0 1, movne_imm 0 0]"

fun
  comp_bbinop :: "bbinop \<Rightarrow> MachineCode list"
where
  "comp_bbinop And = [and_reg 0 0 1]" |
  "comp_bbinop Or = [or_reg 0 0 1]"

fun
  comp_bcomp :: "bcomp \<Rightarrow> MachineCode list"
where
  "comp_bcomp Less = [cmp_reg 0 1, movlt_imm 0 1, movge_imm 0 0]"

fun
  comp_bexp :: "bexp \<Rightarrow> MachineCode list"
where
  "comp_bexp (BConst v) = comp_bexp_mov 0 v" |
  "comp_bexp (BUnOp op b) = comp_bexp_mov 0 b @ comp_bunop op" |
  "comp_bexp (BBinOp op b1 b2) = comp_bexp_mov 0 b1 @ comp_bexp_mov 1 b2 @ comp_bbinop op" |
  "comp_bexp (BComp op a1 a2) = comp_aexp a1 @ mov_reg 0 2 # comp_aexp a2 @ mov_reg 2 1 # comp_bcomp op"

definition
  code_size :: "MachineCode list \<Rightarrow> 24 word"
where
  "code_size is = word_of_int (int (length is))"

term addr_val

fun
  comp_flush :: "MMU_Prg_Logic.flush_type \<Rightarrow> MachineCode list"
where
  "comp_flush flushTLB = [tlbiall]" |
  "comp_flush (flushASID a) = [mov_imm 0 (ucast a), tlbiasid 0]" |
  "comp_flush (flushvarange va) = [
    b_imm 0,
    ARM (addr_val va),
    ldr_lit 0 0 12,
    tlbimvaa 0
  ]" |
  "comp_flush (flushASIDvarange a va) = [
    b_imm 0,
    ARM (word_cat a (word_extract 23 0 (addr_val va)::24 word)),
    ldr_lit 0 0 12,
    tlbimva 0
  ]"

fun
  comp_set_mode :: "mode_t \<Rightarrow> MachineCode list"
where
  "comp_set_mode Kernel = []" |
  "comp_set_mode User = [mov_imm 0 0x10, msr_reg 0 0x1 0]"

fun
  comp_com :: "com \<Rightarrow> MachineCode list"
where
  "comp_com SKIP = []" |
  "comp_com (Assign addr val) = comp_aexp addr @ mov_reg 2 0 # comp_aexp val @ [str_imm 0 2 0]" |
  "comp_com (Seq c1 c2) = (comp_com c1) @ (comp_com c2)" |
  "comp_com (If b c1 c2) = (
    let i1 = comp_com c1;
        i2 = comp_com c2
    in (
      comp_bexp b @
      cmp_imm 0 0 #
      beq_imm ((code_size i1)-1) #
      i1 @ b_imm ((code_size i2)-1) #
      i2
    )
  )" |
  "comp_com (While b c) = (
    let i1 = comp_bexp b;
        i2 = comp_com c
    in (
      i1 @
      cmp_imm 0 0 #
      beq_imm ((code_size i2)-1) #
      i2 @
      [b_imm (-((code_size i1) + (code_size i2) + 4))]
    )
  )" |
  "comp_com (Flush t) = comp_flush t" |
  "comp_com (UpdateTTBR0 a) = comp_aexp a @ [setttbr0 0]" |
  "comp_com (UpdateASID v) = [mov_imm 0 (ucast v), setasid 0]" |
  "comp_com (SetMode m) = comp_set_mode m"

end
