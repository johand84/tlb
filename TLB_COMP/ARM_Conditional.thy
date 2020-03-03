theory ARM_Conditional
  imports TLBJ.ARM_Monadic
begin

definition
  eq :: "instruction"
where
  "eq = IfThen (0x0,0x4)"

definition
  ge :: "instruction"
where
  "ge = IfThen (0xa,0xc)"

definition
  lt :: "instruction"
where
  "lt = IfThen (0xb,0xc)"

definition
  ne :: "instruction"
where
  "ne = IfThen (0x1,0x4)"

end