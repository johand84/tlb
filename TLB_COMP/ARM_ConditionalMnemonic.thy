theory ARM_ConditionalMnemonic
  imports ARM_Conditional
          ARM_Mnemonic
begin

fun
  beq_imm :: "32 word \<Rightarrow> instruction list"
where
  "beq_imm imm32 = [eq, b_imm imm32]"

fun
  moveq_imm :: "4 word \<Rightarrow> 12 word \<Rightarrow> instruction list"
where
  "moveq_imm rd imm12 = [
    eq,
    mov_imm rd imm12
  ]"

fun
  movge_imm :: "4 word \<Rightarrow> 12 word \<Rightarrow> instruction list"
where
  "movge_imm rd imm12 = [
    ge,
    mov_imm rd imm12
  ]"

fun
  movlt_imm :: "4 word \<Rightarrow> 12 word \<Rightarrow> instruction list"
where
  "movlt_imm rd imm12 = [
    lt,
    mov_imm rd imm12
  ]"

fun
  movne_imm :: "4 word \<Rightarrow> 12 word \<Rightarrow> instruction list"
where
  "movne_imm rd imm12 = [
    ne,
    mov_imm rd imm12
  ]"

end