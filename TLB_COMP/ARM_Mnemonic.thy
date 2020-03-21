theory ARM_Mnemonic
  imports TLBJ.ARM_Monadic
begin

(* add rd, rn, rm *)
definition
  add_reg :: "4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> instruction"
where
  "add_reg rd rn rm = Data (
    Register (
      0x4,
      False,
      rd,
      rn,
      rm,
      SRType_LSL,
      0
    )
  )"

(* and rd, rn, rm *)
definition
  and_reg :: "4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> instruction"
where
  "and_reg rd rn rm = Data (
    Register (
      0x0,
      False,
      rd,
      rn,
      rm,
      SRType_LSL,
      0
    )
  )"

definition
  b_imm :: "32 word \<Rightarrow> instruction"
where
  "b_imm imm24 = Branch (
    BranchTarget imm24
  )"

(* cmp rn, #imm12 *)
definition
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
definition
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
definition
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
definition
  ldr_lit :: "bool \<Rightarrow> 4 word \<Rightarrow> 32 word \<Rightarrow> instruction"
where
  "ldr_lit u rt imm32 = Load (
    LoadLiteral (
      u,
      rt,
      imm32
    )
  )"

definition
  mcr_reg :: "3 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 3 word \<Rightarrow> 4 word \<Rightarrow> instruction"
where
  "mcr_reg opc1 crn rt coproc opc2 crm = CoprocessorInstruction (
    MoveToCoprocessorFromRegister(
      opc1,
      crn,
      rt,
      coproc,
      opc2,
      crm
    )
  )"

(* mov rd, #imm12 *)
definition
  mov_imm :: "4 word \<Rightarrow> 12 word \<Rightarrow> instruction"
where
  "mov_imm rd imm12 = Data (
    ArithLogicImmediate (
      0xd,
      False,
      rd,
      0,
      imm12
    )
  )"

definition
  mov_reg :: "4 word \<Rightarrow> 4 word \<Rightarrow> instruction"
where
  "mov_reg rd rm = Data (
    Register (
      0xd,
      False,
      0,
      rd,
      rm,
      SRType_LSL,
      0
    )
  )"

(* orr rd, rn, rm *)
definition
  or_reg :: "4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> instruction"
where
  "or_reg rd rn rm = Data (
    Register (
      0xc,
      False,
      rd,
      rn,
      rm,
      SRType_LSL,
      0
    )
  )"

(* rsb rd, rn, #imm12 *)
definition
  rsb_imm :: "4 word \<Rightarrow> 4 word \<Rightarrow> 12 word \<Rightarrow> instruction"
where
  "rsb_imm rd rn imm12 = Data (
    ArithLogicImmediate (
      0x03,
      False,
      rd,
      rn,
      imm12
    )
  )"

(* str rt, [rn, #imm12] *)
definition
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
definition
  sub_reg :: "4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> instruction"
where
  "sub_reg rd rn rm = Data (
    Register (
      0x2,
      False,
      rd,
      rn,
      rm,
      SRType_LSL,
      0
    )
  )"

(* Aliases *)

definition
  neg :: "4 word \<Rightarrow> 4 word \<Rightarrow> instruction"
where
  "neg rd rm = rsb_imm rd rm 0"

definition
  pop :: "4 word \<Rightarrow> instruction"
where
  "pop r = ldr_imm False True False r 13 4"

definition
  push :: "4 word \<Rightarrow> instruction"
where
  "push r = str_imm True False True r 13 4"

definition
  tlbiall :: "instruction"
where
  "tlbiall = mcr_reg 0 8 0 15 0 7"

definition
  tlbiasid :: "4 word \<Rightarrow> instruction"
where
  "tlbiasid rt = mcr_reg 0 8 rt 15 2 7"

definition
  tlbimva :: "4 word \<Rightarrow> instruction"
where
  "tlbimva rt = mcr_reg 0 8 rt 15 1 7"

definition
  tlbimvaa :: "4 word \<Rightarrow> instruction"
where
  "tlbimvaa rt = mcr_reg 0 8 rt 15 3 7"


end
