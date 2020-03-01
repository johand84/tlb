theory ARM_Mnemonic
  imports TLBJ.ARM_Monadic
begin

definition
  setflags :: "bool"
where
  "setflags = False"

(* add rd, rn, rm *)
fun
  add_reg :: "4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> instruction"
where
  "add_reg rd rn rm = Data (
    Register (
      0x4,
      setflags,
      rd,
      rn,
      rm,
      SRType_LSL,
      0
    )
  )"

(* and rd, rn, rm *)
fun
  and_reg :: "4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> instruction"
where
  "and_reg rd rn rm = Data (
    Register (
      0x0,
      setflags,
      rd,
      rn,
      rm,
      SRType_LSL,
      0
    )
  )"

fun
  b_imm :: "32 word \<Rightarrow> instruction"
where
  "b_imm imm24 = Branch (
    BranchTarget imm24
  )"

(* cmp rn, #imm12 *)
fun
  cmp_imm :: "4 word \<Rightarrow> 12 word \<Rightarrow> instruction"
where
  "cmp_imm rn imm12 = Data (
    ArithLogicImmediate (
      0xa,
      True,
      rn,
      0,
      imm12
    )
  )"

(* cmp rn, rm *)
fun
  cmp_reg :: "4 word \<Rightarrow> 4 word \<Rightarrow> instruction"
where
  "cmp_reg rn rm = Data (
    Register (
      0xa,
      True,
      rn,
      0,
      rm,
      SRType_LSL,
      0
    )
  )"

(* ldr rt, [rn, #imm12] *)
fun
  ldr_imm :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 12 word \<Rightarrow> instruction"
where
  "ldr_imm p u w rt rn imm12 = Load (
    LoadWord (
      u,
      p,
      w,
      rt,
      rn,
      immediate_form1 (ucast imm12)
    )
  )"

(* ldr rt, [pc, #imm32] *)
fun
  ldr_lit :: "bool \<Rightarrow> 4 word \<Rightarrow> 32 word \<Rightarrow> instruction"
where
  "ldr_lit u rt imm32 = Load (
    LoadLiteral (
      u,
      rt,
      imm32
    )
  )"

(* mov rd, #imm12 *)
fun
  mov_imm :: "4 word \<Rightarrow> 12 word \<Rightarrow> instruction"
where
  "mov_imm rd imm12 = Data (
    ArithLogicImmediate (
      0xd,
      setflags,
      rd,
      0,
      imm12
    )
  )"

(* orr rd, rn, rm *)
fun
  or_reg :: "4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> instruction"
where
  "or_reg rd rn rm = Data (
    Register (
      0xc,
      setflags,
      rd,
      rn,
      rm,
      SRType_LSL,
      0
    )
  )"

(* rsb rd, rn, #imm12 *)
fun
  rsb_imm :: "4 word \<Rightarrow> 4 word \<Rightarrow> 12 word \<Rightarrow> instruction"
where
  "rsb_imm rd rn imm12 = Data (
    ArithLogicImmediate (
      0x03,
      setflags,
      rd,
      rn,
      imm12
    )
  )"

(* str rt, [rn, #imm12] *)
fun
  str_imm :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 12 word \<Rightarrow> instruction"
where
  "str_imm p u w rt rn imm12 = Store (
    StoreWord (
      u,
      p,
      w,
      rt,
      rn,
      immediate_form1 (ucast imm12)
    )
  )"

(* sub rd, rn, rm *)
fun
  sub_reg :: "4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> instruction"
where
  "sub_reg rd rn rm = Data (
    Register (
      0x2,
      setflags,
      rd,
      rn,
      rm,
      SRType_LSL,
      0
    )
  )"

(* Aliases *)

fun
  neg :: "4 word \<Rightarrow> 4 word \<Rightarrow> instruction"
where
  "neg rd rm = rsb_imm rd rm 0"

fun
  pop :: "4 word \<Rightarrow> instruction"
where
  "pop r = ldr_imm False True False r 13 4"

fun
  push :: "4 word \<Rightarrow> instruction"
where
  "push r = str_imm True False True r 13 4"

end