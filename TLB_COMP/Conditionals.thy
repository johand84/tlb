theory Conditionals
  imports TLBJ.ARM_Monadic
begin

definition
  always :: "28 word \<Rightarrow> MachineCode"
where
  "always m = ARM (word_cat (0xe::4 word) m)"

definition
  eq :: "28 word \<Rightarrow> MachineCode"
where
  "eq m = ARM (word_cat (0x0::4 word) m)"

definition
  ge :: "28 word \<Rightarrow> MachineCode"
where
  "ge m = ARM (word_cat (0xa::4 word) m)"

definition
  lt :: "28 word \<Rightarrow> MachineCode"
where
  "lt m = ARM (word_cat (0xb::4 word) m)"

definition
  ne :: "28 word \<Rightarrow> MachineCode"
where
  "ne m = ARM (word_cat (0x1::4 word) m)"

end