theory Mnemonics
  imports TLBJ.ARM_Monadic
          Conditionals
begin

definition
  data_arith_logic_imm :: "4 word \<Rightarrow> 1 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 12 word \<Rightarrow> 28 word"
where
  "data_arith_logic_imm op s rn rd imm12 =
    (word_cat
      (word_cat
        (word_cat
          (word_cat
            (word_cat
              (0x1::3 word)
              op
            ::7 word)
            s
          ::8 word)
          rn
        ::12 word)
        rd
      ::16 word)
      imm12
    ::28 word)"

definition
  data_register :: "4 word \<Rightarrow> 1 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 28 word"
where
  "data_register op s rd rn rm =
    (word_cat
      (word_cat
        (word_cat
          (word_cat
            (word_cat
              (word_cat
                (0x0::3 word)
                op
              ::7 word)
              s
            ::8 word)
            rn
          ::12 word)
          rd
        ::16 word)
        (0x00::8 word)
      ::24 word)
      rm
    ::28 word)"

definition
  add_reg1 :: "4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 28 word"
where
  "add_reg1 rd rn rm = data_register 0x4 0 rd rn rm"

definition
  and_reg1 :: "4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 28 word"
where
  "and_reg1 rd rn rm = data_register 0x0 0 rd rn rm"

definition
  b_imm1 :: "24 word \<Rightarrow> 28 word"
where
  "b_imm1 imm24 = word_cat (0xa::4 word) imm24"

definition
  cmp_reg1 :: "4 word \<Rightarrow> 4 word \<Rightarrow> 28 word"
where
  "cmp_reg1 rn rm = data_register 0xa 1 0 rn rm"

definition
  ldr_imm1 :: "1 word \<Rightarrow> 1 word \<Rightarrow> 1 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 12 word \<Rightarrow> 28 word"
where
  "ldr_imm1 p u w rt rn imm12 = 
    (word_cat
      (word_cat
        (word_cat
          (word_cat
            (word_cat
              (word_cat
                (word_cat
                  (word_cat
                    (0x2::3 word)
                    p
                  ::4 word)
                  u
                ::5 word)
                (0x0::1 word)
              ::6 word)
              w
            ::7 word)
            (0x1::1 word)
          ::8 word)
          rn
        ::12 word)
        rt
      ::16 word)
      imm12
    ::28 word)"

definition
  ldr_lit1 :: "1 word \<Rightarrow> 4 word \<Rightarrow> 12 word \<Rightarrow> 28 word"
where
  "ldr_lit1 u rt imm12 =
    (word_cat
      (word_cat
        (word_cat
          (word_cat
            (word_cat
              (word_cat
                (word_cat
                  (word_cat
                    (0x2::3 word)
                    (0x1::1 word)
                  ::4 word)
                  u
                ::5 word)
                (0x0::1 word)
              ::6 word)
              (0x0::1 word)
            ::7 word)
            (0x1::1 word)
          ::8 word)
          (0xf::4 word)
        ::12 word)
        rt
      ::16 word)
      imm12
    ::28 word)"

definition
  mcr_reg1 :: "3 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 3 word \<Rightarrow> 4 word \<Rightarrow> 28 word"
where
  "mcr_reg1 opc1 crn rt coproc opc2 crm =
    (word_cat
      (word_cat
        (word_cat
          (word_cat
            (word_cat
              (word_cat
                (word_cat
                  (word_cat
                    (0xe::4 word)
                    opc1
                  ::7 word)
                  (0x0::1 word)
                ::8 word)
                crn
              ::12 word)
              rt
            ::16 word)
            coproc
          ::20 word)
          opc2
        ::23 word)
        (0x1::1 word)
      ::24 word)
      crm
    ::28 word)"

definition
  mov_imm1 :: "4 word \<Rightarrow> 12 word \<Rightarrow> 28 word"
where
  "mov_imm1 rd imm12 = data_arith_logic_imm 0xd 0 0 rd imm12"

definition
  mov_reg1 :: "4 word \<Rightarrow> 4 word \<Rightarrow> 28 word"
where
  "mov_reg1 rd rm = data_register 0xd 0 rd 0 rm"

definition
  msr_imm1 :: "1 word \<Rightarrow> 4 word \<Rightarrow> 12 word \<Rightarrow> 28 word"
where
  "msr_imm1 r m imm12 =
    (word_cat
      (word_cat
        (word_cat
          (word_cat
            (word_cat
              (0x10::5 word)
              r
            ::6 word)
            (0x2::2 word)
          ::8 word)
          m
        ::12 word)
        (0xf::4 word)
      ::16 word)
      imm12
    ::28 word)"

definition
  msr_reg1 :: "1 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 28 word"
where
  "msr_reg1 r m rn =
    (word_cat
      (word_cat
        (word_cat
          (word_cat
            (word_cat
              (0x02::5 word)
              r
            ::6 word)
            (0x2::2 word)
          ::8 word)
          m
        ::12 word)
        (0xf00::12 word)
      ::24 word)
      rn
    ::28 word)"

definition
  or_reg1 :: "4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 28 word"
where
  "or_reg1 rd rn rm = data_register 0xc 0 rd rn rm"

definition
  rsb_imm1 :: "4 word \<Rightarrow> 4 word \<Rightarrow> 12 word \<Rightarrow> 28 word"
where
  "rsb_imm1 rn rd imm12 = data_arith_logic_imm 0x3 0 rn rd imm12"

definition
  str_imm1 :: "1 word \<Rightarrow> 1 word \<Rightarrow> 1 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 12 word \<Rightarrow> 28 word"
where
  "str_imm1 p u w rt rn imm12 = 
    (word_cat
      (word_cat
        (word_cat
          (word_cat
            (word_cat
              (word_cat
                (word_cat
                  (word_cat
                    (0x2::3 word)
                    p
                  ::4 word)
                  u
                ::5 word)
                (0x0::1 word)
              ::6 word)
              w
            ::7 word)
            (0x0::1 word)
          ::8 word)
          rn
        ::12 word)
        rt
      ::16 word)
      imm12
    ::28 word)"

definition
  sub_reg1 :: "4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 28 word"
where
  "sub_reg1 rd rn rm = data_register 0x2 0 rd rn rm"

(* add rd, rn, rm *)
definition
  add_reg :: "4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> MachineCode"
where
  "add_reg rd rn rm = always (add_reg1 rd rn rm)"

(* and rd, rn, rm *)
definition
  and_reg :: "4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> MachineCode"
where
  "and_reg rd rn rm = always (and_reg1 rd rn rm)"

definition
  b_imm :: "24 word \<Rightarrow> MachineCode"
where
  "b_imm imm24 = always (b_imm1 imm24)"

definition
  beq_imm :: "24 word \<Rightarrow> MachineCode"
where
  "beq_imm imm24 = eq (b_imm1 imm24)"

(* cmp rn, #imm12 *)
definition
  cmp_imm :: "4 word \<Rightarrow> 12 word \<Rightarrow> MachineCode"
where
  "cmp_imm rn imm12 = always (data_arith_logic_imm 0xa 1 rn 0 imm12)"

(* cmp rn, rm *)
definition
  cmp_reg :: "4 word \<Rightarrow> 4 word \<Rightarrow> MachineCode"
where
  "cmp_reg rn rm = always (cmp_reg1 rn rm)"

(* ldr rt, [rn, #imm12] *)
definition
  ldr_imm :: "4 word \<Rightarrow> 4 word \<Rightarrow> 12 word \<Rightarrow> MachineCode"
where
  "ldr_imm rt rn imm12 = always (ldr_imm1 0 0 0 rt rn imm12)"

(* ldr rt, [pc, #imm32] *)
definition
  ldr_lit :: "1 word \<Rightarrow> 4 word \<Rightarrow> 12 word \<Rightarrow> MachineCode"
where
  "ldr_lit u rt imm12 = always (ldr_lit1 u rt imm12)"

definition
  mcr_reg :: "3 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> 3 word \<Rightarrow> 4 word \<Rightarrow> MachineCode"
where
  "mcr_reg opc1 crn rt coproc opc2 crm = always (mcr_reg1 opc1 crn rt coproc opc2 crm)"

(* mov rd, #imm12 *)
definition
  mov_imm :: "4 word \<Rightarrow> 12 word \<Rightarrow> MachineCode"
where
  "mov_imm rd imm12 = always (mov_imm1 rd imm12)"

definition
  mov_reg :: "4 word \<Rightarrow> 4 word \<Rightarrow> MachineCode"
where
  "mov_reg rd rm = always (mov_reg1 rd rm)"

definition
  moveq_imm :: "4 word \<Rightarrow> 12 word \<Rightarrow> MachineCode"
where
  "moveq_imm rd imm12 = eq (mov_imm1 rd imm12)"

definition
  movge_imm :: "4 word \<Rightarrow> 12 word \<Rightarrow> MachineCode"
where
  "movge_imm rd imm12 = ge (mov_imm1 rd imm12)"

definition
  movlt_imm :: "4 word \<Rightarrow> 12 word \<Rightarrow> MachineCode"
where
  "movlt_imm rd imm12 = lt (mov_imm1 rd imm12)"

definition
  movne_imm :: "4 word \<Rightarrow> 12 word \<Rightarrow> MachineCode"
where
  "movne_imm rd imm12 = ne (mov_imm1 rd imm12)"

definition
  msr_imm :: "1 word \<Rightarrow> 4 word \<Rightarrow> 12 word \<Rightarrow> MachineCode"
where
  "msr_imm r m imm12 = always (msr_imm1 r m imm12)"

definition
  msr_reg :: "1 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> MachineCode"
where
  "msr_reg r m rn = always (msr_reg1 r m rn)"

(* orr rd, rn, rm *)
definition
  or_reg :: "4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> MachineCode"
where
  "or_reg rd rn rm = always (or_reg1 rd rn rm)"

(* rsb rd, rn, #imm12 *)
definition
  rsb_imm :: "4 word \<Rightarrow> 4 word \<Rightarrow> 12 word \<Rightarrow> MachineCode"
where
  "rsb_imm rd rn imm12 = always (rsb_imm1 rn rd imm12)"

(* str rt, [rn, #imm12] *)
definition
  str_imm :: "4 word \<Rightarrow> 4 word \<Rightarrow> 12 word \<Rightarrow> MachineCode"
where
  "str_imm rt rn imm12 = always (str_imm1 0 0 0 rt rn imm12)"

(* sub rd, rn, rm *)
definition
  sub_reg :: "4 word \<Rightarrow> 4 word \<Rightarrow> 4 word \<Rightarrow> MachineCode"
where
  "sub_reg rd rn rm = always (sub_reg1 rd rn rm)"

(* Aliases *)

definition
  neg :: "4 word \<Rightarrow> 4 word \<Rightarrow> MachineCode"
where
  "neg rd rm = rsb_imm rd rm 0"

definition
  pop :: "4 word \<Rightarrow> MachineCode"
where
  "pop r = always (ldr_imm1 0 1 0 r 13 4)"

definition
  push :: "4 word \<Rightarrow> MachineCode"
where
  "push r = always (str_imm1 1 0 1 r 13 4)"

definition
  setasid ::  "4 word \<Rightarrow> MachineCode"
where
  "setasid rt = mcr_reg 0 13 rt 15 0 0"

definition
  tlbiall :: "MachineCode"
where
  "tlbiall = mcr_reg 0 8 0 15 0 7"

definition
  tlbiasid :: "4 word \<Rightarrow> MachineCode"
where
  "tlbiasid rt = mcr_reg 0 8 rt 15 2 7"

definition
  tlbimva :: "4 word \<Rightarrow> MachineCode"
where
  "tlbimva rt = mcr_reg 0 8 rt 15 1 7"

definition
  tlbimvaa :: "4 word \<Rightarrow> MachineCode"
where
  "tlbimvaa rt = mcr_reg 0 8 rt 15 3 7"

definition
  setttbr0 :: "4 word \<Rightarrow> MachineCode"
where
  "setttbr0 rt = mcr_reg 0 2 rt 15 0 0"

end
