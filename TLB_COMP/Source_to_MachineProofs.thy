theory Source_to_MachineProofs

imports Source_to_Machine

begin

definition
  bin_to_reg :: "4 word \<Rightarrow> RName"
where
  "bin_to_reg r = (
    if r = 0 then RName_0usr
    else if r = 1 then RName_1usr
    else if r = 2 then RName_2usr
    else if r = 3 then RName_3usr
    else if r = 4 then RName_4usr
    else if r = 5 then RName_5usr
    else if r = 6 then RName_6usr
    else if r = 7 then RName_7usr
    else if r = 8 then RName_8usr
    else if r = 9 then RName_9usr
    else if r = 10 then RName_10usr
    else if r = 11 then RName_11usr
    else if r = 12 then RName_12usr
    else if r = 13 then RName_SPusr
    else if r = 14 then RName_LRusr
    else RName_PC
  )"

fun
  code_installed :: "'a set_tlb_state_scheme \<Rightarrow> MachineCode list \<Rightarrow>  bool"
where
  "code_installed s [] = True" |
  "code_installed s (x#xs) = (
    case Fetch s of (m,t) \<Rightarrow> m = x \<and> code_installed (
        t\<lparr>REG := (REG s)(RName_PC := REG s RName_PC + 4)\<rparr>
      )
      xs
  )"

definition
  aligned :: "paddr \<Rightarrow> bool"
where
  "aligned v \<equiv> ((ucast (addr_val v))::2 word) = 0"


definition
  heap_rel :: "p_state \<Rightarrow> 'a set_tlb_state_scheme \<Rightarrow> _"
where
  "heap_rel s t \<equiv>
   (\<forall>adr val.
     (heap s) adr = Some val \<and> aligned adr \<longrightarrow>
     (MEM t) adr = Some (ucast val) \<and>
     (MEM t) (adr r+ 1) = Some (ucast (val >> 8)) \<and>
     (MEM t) (adr r+ 2) = Some (ucast (val >> 16)) \<and>
     (MEM t) (adr r+ 3) = Some (ucast (val >> 24)) )"


definition
  general_purpose_reg  :: "4 word \<Rightarrow> bool"
where
  "general_purpose_reg r \<equiv> r = 0 \<or> r = 1 \<or> r = 2 \<or> r = 3 \<or> r = 4 \<or> r = 5 \<or>
                           r = 6 \<or> r = 7 \<or> r = 8 \<or> r = 9 \<or> r = 10 \<or> r = 11 \<or>
                           r = 12"

definition
  machine_config :: "'a set_tlb_state_scheme \<Rightarrow> bool"
where
  "machine_config s = (
    Architecture s = ARMv7_A \<and>
    Encoding s = Encoding_ARM \<and>
    Extensions s = {} \<and>
    Aligned1 (Addr (REG s RName_PC), 4) \<and>
    \<not>J (CPSR s) \<and> \<not>T (CPSR s) \<and> \<not>E (CPSR s) \<and>
    (PSR.M (CPSR s) = 0x10 \<or> PSR.M (CPSR s) = 0x13)
  )"

definition
  machine_state_rel :: "'a set_tlb_state_scheme \<Rightarrow> 'a set_tlb_state_scheme \<Rightarrow> bool"
where
  "machine_state_rel s t \<equiv>
    ASID s = ASID t \<and>
    TTBR0 s = TTBR0 t \<and>
    set_tlb.iset (set_tlb s) = set_tlb.iset (set_tlb t) \<and>
    set_tlb.global_set (set_tlb s) = set_tlb.global_set (set_tlb t) \<and>
    set_tlb.snapshot (set_tlb s) = set_tlb.snapshot (set_tlb t) \<and>
    PSR.M (CPSR s) = PSR.M (CPSR t) \<and>
    MEM s = MEM t"

definition
  mode_rel :: "mode_t \<Rightarrow> 5 word \<Rightarrow> _"
where
  "mode_rel m cpsrm \<equiv>
   case m of
      Kernel => cpsrm = 0b10011
    | User   => cpsrm = 0b10000"

definition
  state_rel :: "p_state \<Rightarrow> 'a set_tlb_state_scheme \<Rightarrow> bool"
where
  "state_rel s t \<equiv>
     (asid s = ASID t) \<and>
     (root s = TTBR0 t) \<and>
     (p_state.incon_set s = set_tlb.iset (set_tlb t)) \<and>
     (p_state.global_set s = set_tlb.global_set (set_tlb t)) \<and>
     (HOL.undefined s = set_tlb.snapshot (set_tlb t)) \<and>
     mode_rel (mode s) (PSR.M (CPSR t)) \<and>
     heap_rel s t \<and>
     machine_config t"

fun
  steps :: "'a set_tlb_state_scheme \<Rightarrow> nat \<Rightarrow> 'a set_tlb_state_scheme"
where
  "steps s 0 = s" |
  "steps s (Suc i) = steps (snd (Next s)) i"

(* Proofs *)

lemma code_installed_append:
  "\<lbrakk>code_installed t (ca @ cb)\<rbrakk> \<Longrightarrow> code_installed t ca"
  by (induction ca arbitrary: t, clarsimp+)

lemma code_installed_prepend:
  "\<lbrakk>code_installed t (ca @ cb)\<rbrakk> \<Longrightarrow> code_installed (steps t (length ca)) cb"
  sorry

lemma steps_add:
  "(steps (steps t l1) l2) = (steps t (l1 + l2))"
  sorry

lemma steps_inc:
  "(snd (Next (steps t l))) = (steps (snd (Next t)) l)"
  sorry

lemma machine_config_mmu_translate:
  "\<lbrakk>mmu_translate v s = (p, t); machine_config s\<rbrakk> \<Longrightarrow> machine_config t \<and> machine_state_rel s t \<and> REG s = REG t"
  apply (clarsimp simp: mmu_translate_set_tlb_state_ext_def Let_def machine_state_rel_def
                  split: if_split_asm)
  by (clarsimp simp: raise'exception_def machine_config_def split:if_split_asm)+

lemma machine_config_mmu_read_size:
  "\<lbrakk>mmu_read_size v s = (r, t); machine_config s\<rbrakk> \<Longrightarrow> machine_config t \<and> machine_state_rel s t \<and> REG s = REG t"
  apply (clarsimp simp: mmu_read_size_set_tlb_state_ext_def split: prod.splits)
  apply (frule machine_config_mmu_translate, simp)
  apply (clarsimp simp: mem_read1_def split: if_split_asm)
      apply (clarsimp simp: mem1_def raise'exception_def machine_config_def machine_state_rel_def
                     split: option.splits if_split_asm)
     apply (clarsimp simp: mem1_def raise'exception_def machine_config_def
                     split: option.splits if_split_asm)
    apply (clarsimp simp: mem1_def raise'exception_def machine_config_def machine_state_rel_def
                    split: option.splits if_split_asm)
  sorry

lemma Fetch_correct:
  "\<lbrakk>Fetch s = (mc, t); machine_config s\<rbrakk> \<Longrightarrow> machine_config t \<and> machine_state_rel s t \<and> REG s = REG t"
  apply (clarsimp simp: machine_config_def Fetch_def CurrentInstrSet_def
                        ISETSTATE_def word_cat_def)
  apply (clarsimp simp: MemA_def CurrentModeIsNotUser_def BadMode_def)
  apply (erule disjE; clarsimp)
   apply (clarsimp simp: MemA_with_priv_def split: prod.splits)
    apply (frule machine_config_mmu_read_size, clarsimp simp: machine_config_def)
    apply (clarsimp simp: machine_config_def machine_state_rel_def)
  apply (clarsimp simp: MemA_with_priv_def split: prod.splits)
  apply (frule machine_config_mmu_read_size, clarsimp simp: machine_config_def)
  by (clarsimp simp: machine_config_def machine_state_rel_def)

lemma Decode_add_reg_correct:
  "\<lbrakk>machine_config s;
    Decode (add_reg rd rn rm) s = (i,t)\<rbrakk> \<Longrightarrow>
      t = s \<and> i = Data (Register (0x4, False, rd, rn, rm, SRType_LSL, 0))"
  sorry

lemma Decode_and_reg_correct:
  "Decode (and_reg rd rn rm) t = (i,t') \<Longrightarrow> i = Data (Register (0x0, False, rd, rn, rm, SRType_LSL, 0))"
  sorry

lemma Decode_b_imm_correct:
  "Decode (b_imm imm24) s = (i,t) \<Longrightarrow> t = s \<and> i = Branch (BranchTarget (ucast imm24))"
  sorry

lemma Decode_cmp_imm_correct:
  "Decode (cmp_imm rn imm12) t = (i,t') \<Longrightarrow> i = Data (ArithLogicImmediate (0xa, True, 0, rn, imm12))"
  sorry

lemma Decode_ldr_imm_correct:
  "Decode (ldr_imm rt rn imm12) t = (i,t') \<Longrightarrow>
    i = Load (LoadWord (False, False, False, rt, rn, immediate_form1 (ucast imm12)))"
  sorry

lemma Decode_ldr_lit_correct:
  "Decode (ldr_lit u rt imm12) t = (i,t') \<Longrightarrow> i = Load (LoadLiteral ((imm12 < 0), rt, (ucast imm12)))"
  sorry

lemma Decode_mov_imm_correct:
  "\<lbrakk>Decode (mov_imm rd imm12) t = (i,t'); machine_config t \<rbrakk>\<Longrightarrow> 
     i = Data (ArithLogicImmediate (0xd, False, rd, 0, imm12)) \<and>
     t' = t"
  sorry

lemma Decode_mov_reg_correct:
  "Decode (mov_reg rd rm) t = (i,t') \<Longrightarrow> i = Data (Register (0xd, False, rd, 0, rm, SRType_LSL, 0))"
  sorry

lemma Decode_moveq_imm_correct:
  "Decode (moveq_imm rd imm12) t = (i,t') \<Longrightarrow>
    i = (if PSR.Z (CPSR t) then Data (ArithLogicImmediate (0xd, False, rd, 0, imm12)) else NoOperation)"
  sorry

lemma Decode_movne_imm_correct:
  "Decode (movne_imm rd imm12) t = (i,t') \<Longrightarrow>
    i = (if PSR.Z (CPSR t) then NoOperation else Data (ArithLogicImmediate (0xd, False, rd, 0, imm12)))"
  sorry

lemma Decode_neg_correct:
  "Decode (neg rd rm) t = (i,t') \<Longrightarrow> i = Data (ArithLogicImmediate (0x3, False, rd, rm, imm12))"
  sorry

lemma Decode_or_reg_correct:
  "Decode (or_reg rd rn rm) t = (i,t') \<Longrightarrow> i = Data (Register (0xc, False, rd, rn, rm, SRType_LSL, 0))"
  sorry

lemma Decode_str_imm_correct:
  "Decode (str_imm rt rn imm12) t = (i,t') \<Longrightarrow>
    i = Store (StoreWord (False, False, False, rt, rn, immediate_form1 (ucast imm12)))"
  sorry

lemma Decode_sub_reg_correct:
  "Decode (sub_reg rd rn rm) t = (i,t') \<Longrightarrow> i = Data (Register (0x2, False, rd, rn, rm, SRType_LSL, 0))"
  sorry

lemma Aligned1_correct:
  "Aligned1 (Addr val, 4) \<Longrightarrow> Aligned1 (Addr (val + 4), 4)"
  sorry

lemma ArchVersion_correct:
  "machine_config s \<Longrightarrow> ArchVersion () s = (7, s)"
  by (simp add: ArchVersion_def machine_config_def)

lemma armexpand_imm_c_state_eq:
  "ARMExpandImm_C (v, c) s = ((a, b), t) \<Longrightarrow> t = s"
  apply (clarsimp simp: ARMExpandImm_C_def Shift_C_def split: SRType.splits if_split_asm)
  by (clarsimp simp: ROR_C_def)


lemma armexpand_imm_c_vals:
  "ARMExpandImm_C (v, c) s = ((a, b), t) \<Longrightarrow>
   (uint ((word_extract 11 8 v) :: 4 word) = 0 \<longrightarrow> a = (word_of_int (uint ((word_extract 7 0 v) :: 8 word)) :: 32 word) \<and> b = c) \<and>
   (uint ((word_extract 11 8 v) :: 4 word) \<noteq> 0 \<longrightarrow>
     a = word_rotr (2 * nat (uint ((word_extract 11 8 v) :: 4 word))) (word_of_int (uint ((word_extract 7 0 v):: 8 word))) \<and>
     b = msb a) "
  apply (clarsimp simp: ARMExpandImm_C_def Shift_C_def split: SRType.splits if_split_asm)
  by (clarsimp simp: ROR_C_def Let_def)

lemma CurrentInstrSet_correct:
  "machine_config s \<Longrightarrow> CurrentInstrSet () s = (InstrSet_ARM, s)"
  by (simp add: CurrentInstrSet_def ISETSTATE_def machine_config_def word_cat_def split: if_split_asm)

lemma BranchWritePC_correct:
  "\<lbrakk>machine_config s;
    BranchWritePC (REG s RName_PC + 8 + (ucast offset)) s = ((), t)\<rbrakk> \<Longrightarrow>
      t = s\<lparr>REG := (REG s)(RName_PC := REG s RName_PC + (ucast offset) + 8)\<rparr> \<and>
        machine_config t \<and>
        machine_state_rel s t"
  apply (frule CurrentInstrSet_correct)
  apply (frule ArchVersion_correct, safe)
    apply (simp add: BranchWritePC_def BranchTo_def)
    defer
    defer
    apply (simp add: BranchWritePC_def BranchTo_def machine_state_rel_def, safe, simp+)
  sorry

lemma ITAdvance_correct:
  "machine_config s \<Longrightarrow> ITAdvance () s = ((), s)"
  by (simp add: HaveThumb2_def ITAdvance_def machine_config_def)

lemma IncPC_correct:
  "\<lbrakk>machine_config s;
    IncPC () s = ((),t)\<rbrakk> \<Longrightarrow>
      t = s\<lparr>REG := (REG s)(RName_PC := REG s RName_PC + 4)\<rparr> \<and>
      machine_config t \<and>
      machine_state_rel s t"
  apply (simp add: BranchTo_def
                   IncPC_def
                   ThisInstrLength_def
                   machine_config_def
                   machine_state_rel_def, safe)
  by (drule Aligned1_correct, simp)+

lemma IsSecure_correct:
  "machine_config s \<Longrightarrow> IsSecure () s = (True, s)"
  by (simp add: HaveSecurityExt_def IsSecure_def machine_config_def)

lemma LookUpRName_correct:
  "\<lbrakk>machine_config s;
    LookUpRName (reg, x) s = (y, t);
    general_purpose_reg reg;
    x = 0x10 \<or> x = 0x13\<rbrakk> \<Longrightarrow> y = bin_to_reg reg \<and> s = t"
  by (simp add: BadMode_def
                LookUpRName_def
                RBankSelect_def
                RfiqBankSelect_def
                bin_to_reg_def
                general_purpose_reg_def
                machine_state_rel_def
           split: if_split_asm)

lemma PC_correct:
  "\<lbrakk>machine_config s;
    PC s = (x, t)\<rbrakk> \<Longrightarrow> s = t \<and> x = REG s RName_PC + 8"
  by (simp add: CurrentInstrSet_correct PC_def R_def, safe)

lemma write'R_correct:
  "\<lbrakk>machine_config s;
    write'R (val, reg) s = ((),t);
    general_purpose_reg reg\<rbrakk> \<Longrightarrow>
      t = s\<lparr>REG := (REG s)(bin_to_reg reg := val)\<rparr> \<and>
      machine_config t \<and>
      machine_state_rel s t"
  apply (frule IsSecure_correct)
  apply (simp add: write'R_def write'Rmode_def split: if_split_asm prod.splits)
     apply (simp add: general_purpose_reg_def)
    apply (simp add: general_purpose_reg_def)
   apply (simp add: general_purpose_reg_def)
  apply (frule LookUpRName_correct, simp, simp)
   apply (simp add: machine_config_def, simp, clarify)
  apply (simp add: bin_to_reg_def
                   general_purpose_reg_def
                   machine_config_def
                   machine_state_rel_def
              split: if_split_asm)
  done

lemma Run_add_reg_correct:
  "\<lbrakk>machine_config s;
    Run (Data (Register (4, False, 0, 0, 1, SRType_LSL, 0))) s = ((), t)\<rbrakk> \<Longrightarrow>
      machine_config t \<and>
      machine_state_rel s t \<and>
      REG t = (REG s)(RName_0usr := REG s RName_0usr + REG s RName_1usr,
                      RName_PC := REG s RName_PC + 4)"
  apply (simp add: Run_def dfn'Register_def doRegister_def split: prod.splits)
  apply (frule IsSecure_correct)
  apply (simp add: R_def Rmode_def split: prod.splits)
  apply (simp add: LookUpRName_def)
  apply (simp add: Shift_C_def)
  apply (simp add: DataProcessing_def mask_def word_bits_def word_extract_def split: prod.splits)
  apply (simp add: R_def Rmode_def split: prod.splits)
  apply (simp add: LookUpRName_def)
  apply (simp add: DataProcessingALU_def)
  apply (frule write'R_correct, simp, safe)
     apply (simp add: general_purpose_reg_def)
    apply (frule IncPC_correct, simp, safe, simp)
   apply (frule IncPC_correct, simp, safe, simp)
   apply (simp add: machine_config_def machine_state_rel_def)
  apply (simp add: AddWithCarry_def Let_def bin_to_reg_def wi_hom_syms)
  apply (frule IncPC_correct, simp, simp)
  done

lemma add_reg_state_rel_correct:
  "\<lbrakk>state_rel s t;
    Fetch t = (add_reg 0 0 1, ft);
    machine_config t\<rbrakk> \<Longrightarrow> state_rel s (snd (Next t))"
  apply (simp add: Next_def split: prod.splits, safe)
  apply (frule Fetch_correct, simp, safe)
  apply (frule Decode_add_reg_correct, simp, safe)
  apply (frule Run_add_reg_correct, simp, safe)
  apply (frule_tac s = "x2a" in ITAdvance_correct)
  apply (simp add: machine_state_rel_def snd_def state_rel_def, safe)
  apply (simp add: heap_rel_def)
  done

lemma add_reg_REG_correct:
  "\<lbrakk>machine_config t;
    Fetch t = (add_reg 0 0 1, ft);
    REG t RName_0usr = val1;
    REG t RName_1usr = val2\<rbrakk> \<Longrightarrow>
      REG (steps t 1) = (REG t)(RName_0usr := val1 + val2, RName_PC := REG t RName_PC + 4)"
  apply (simp add: Next_def split: prod.splits)
  apply (frule Fetch_correct, safe)
  apply (frule Decode_add_reg_correct, simp, simp, safe)
  apply (frule Run_add_reg_correct, simp, safe)
  apply (frule_tac s = "x2a" in ITAdvance_correct, simp)
  done

lemma add_reg_correct:
  "\<lbrakk>state_rel s t;
    Fetch t = (add_reg 0 0 1, ft);
    machine_config t;
    REG t RName_0usr = val1;
    REG t RName_1usr = val2\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        state_rel s t' \<and>
        REG t' = (REG t)(RName_0usr := val1 + val2,
                        RName_PC := REG t RName_PC + 4)"
   apply (frule add_reg_state_rel_correct, simp+)
  apply (frule add_reg_REG_correct, simp+)
  done

lemma and_reg_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (and_reg 0 0 1 # ins);
    REG t RName_0usr = val1;
    REG t RName_1usr = val2\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = val1 && val2"
  sorry

lemma Run_b_imm_correct:
  "\<lbrakk>machine_config s;
    Run (Branch (BranchTarget (UCAST(24 \<rightarrow> 32) offset))) s = ((), t) \<rbrakk> \<Longrightarrow>
      machine_config t \<and>
      machine_state_rel s t \<and>
      REG t = (REG s)(RName_PC := REG s RName_PC + (ucast offset) + 8)"
  apply (simp add: Run_def dfn'BranchTarget_def split: prod.splits)
  apply (frule PC_correct, simp, safe)
    apply (frule BranchWritePC_correct, simp, safe)
   apply (frule BranchWritePC_correct, simp, safe)
  apply (frule BranchWritePC_correct, simp, safe, simp)
  done

lemma b_imm_correct:
  "\<lbrakk>state_rel s t;
    machine_config t;
    Fetch t = (b_imm offset, ft)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        state_rel s t' \<and>
        machine_config t' \<and>
        REG t' = (REG t)(RName_PC := REG t RName_PC + (ucast offset) + 8)"
  apply (simp add: Next_def split: prod.splits)
  apply (frule Fetch_correct, simp, safe)
    apply (frule Decode_b_imm_correct, safe)
    apply (frule Run_b_imm_correct, simp, simp, safe)
    apply (frule_tac s = "x2a" in ITAdvance_correct)
    apply (simp add: heap_rel_def machine_config_def machine_state_rel_def state_rel_def)
   apply (frule Decode_b_imm_correct, safe)
   apply (frule Run_b_imm_correct, simp, simp, safe)
   apply (frule_tac s = "x2a" in ITAdvance_correct, simp)
  apply (frule Decode_b_imm_correct, safe)
  apply (frule Run_b_imm_correct, simp, simp, safe)
  apply (frule_tac s = "x2a" in ITAdvance_correct, simp)
  done

lemma cmp_imm_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (cmp_imm 0 0 # ins);
    REG t RName_0usr = (if val then 1 else 0)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        (if val then \<not>PSR.Z (CPSR t') else PSR.Z (CPSR t'))"
  sorry

lemma ldr_imm_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (ldr_imm 0 0 0 # ins);
    mem_read_hp' (incon_set s) (heap s) (root s) (mode s) (Addr (REG t RName_0usr)) = Some val\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = val \<and>
        REG t' RName_2usr = REG t RName_2usr"
  sorry

lemma ldr_lit_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (ldr_lit 0 reg 0xC # ins);
    code_installed (t\<lparr>REG := (REG t)(RName_PC := REG t RName_PC - 4)\<rparr>) (ARM val # ldr_lit 0 reg 0xC # ins)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' (if reg = 0 then RName_0usr else RName_1usr) = val"
  sorry

lemma mov_imm_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (mov_imm reg (ucast val) # ins)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = (if reg = 0 then val else REG t RName_0usr) \<and>
        REG t' RName_1usr = (if reg = 1 then val else REG t RName_1usr) \<and>
        REG t' RName_2usr = REG t RName_2usr"
  sorry

lemma mov_reg_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (mov_reg 2 0 # ins);
    REG t' RName_0usr = val\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_2usr  = val"
  sorry

lemma moveq_imm_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (moveq_imm 0 (ucast val) # ins)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        PSR.Z (CPSR t') = PSR.Z (CPSR t) \<and>
        REG t' RName_0usr = (if PSR.Z (CPSR t) then val else REG t RName_0usr)"
  sorry

lemma movne_imm_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (movne_imm 0 (ucast val) # ins)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        PSR.Z (CPSR t') = PSR.Z (CPSR t) \<and>
        REG t' RName_0usr = (if PSR.Z (CPSR t) then REG t RName_0usr else val)"
  sorry

lemma neg_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (neg 0 0 # ins);
    REG t RName_0usr = val\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = -val \<and>
        REG t' RName_2usr = REG t RName_2usr"
  sorry

lemma or_reg_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (or_reg 0 0 1 # ins);
    REG t RName_0usr = val1;
    REG t RName_1usr = val2\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = val1 || val2"
  sorry

lemma str_imm_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (str_imm 0 2 0 # ins);
    REG t RName_0usr = val;
    addr_trans s (Addr (REG t RName_2usr)) = Some pp\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel (s\<lparr>heap := heap s(pp \<mapsto> val),
          p_state.incon_set := iset_upd s pp val,
          p_state.global_set := gset_upd s pp val\<rparr>) t'"
  sorry

lemma sub_reg_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (sub_reg 0 0 1 # ins);
    REG t RName_0usr = val1;
    REG t RName_1usr = val2\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = val1 - val2 \<and>
        REG t' RName_2usr = REG t RName_2usr"
  sorry

lemma comp_aexp_mov_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (comp_aexp_mov reg val @ ins)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t (length (comp_aexp_mov reg val)) = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = (if reg = 0 then val else REG t RName_0usr) \<and>
        REG t' RName_1usr = (if reg = 1 then val else REG t RName_1usr) \<and>
        REG t' RName_2usr = REG t RName_2usr"
  apply (simp only: comp_aexp_mov_def split: if_split_asm)
   apply (drule mov_imm_correct, simp, safe, simp)
   apply (drule_tac insa = "[ARM val]" and insb = "ldr_lit 0 reg 0xC # ins" in b_imm_correct)
   apply (simp add: code_size_def word_arith_wis word_of_int_def, safe)
  apply (drule_tac ins = "ins" and reg = "reg" and val = "val" in ldr_lit_correct, simp)
  sorry

lemma comp_aexp_Const_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some val; code_installed t (comp_aexp e @ ins); state_rel s t; e = Const x1\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = val \<and>
      REG t' RName_2usr = REG t RName_2usr"
  apply (simp)
  apply (drule comp_aexp_mov_correct, simp+)
  done

lemma comp_aexp_UnOp_Neg_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some val'; code_installed t (comp_aexp e @ ins); state_rel s t; e = UnOp op val; op = Neg\<rbrakk> \<Longrightarrow> 
    \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = val' \<and>
      REG t' RName_2usr = REG t RName_2usr"
  apply (frule comp_aexp_mov_correct, simp, safe)
  apply (drule neg_correct, simp, simp, safe)
  apply (simp add: steps_inc)
  done

lemma comp_aexp_UnOp_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some val'; code_installed t (comp_aexp e @ ins); state_rel s t; e = UnOp op val\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = val' \<and>
      REG t' RName_2usr = REG t RName_2usr"
  apply (cases op)
  apply (rule comp_aexp_UnOp_Neg_correct, force+)
  done

lemma comp_aexp_BinOp_Plus_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some val; code_installed t (comp_aexp e @ ins); state_rel s t; e = BinOp op val1 val2; op = Plus\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = val \<and>
      REG t' RName_2usr = REG t RName_2usr"
  apply (drule comp_aexp_mov_correct, simp, safe)
  apply (drule comp_aexp_mov_correct, simp, safe)
  apply (drule add_reg_correct, simp, simp, simp, safe)
  apply (simp add: steps_add steps_inc)
  done

lemma comp_aexp_BinOp_Minus_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some val; code_installed t (comp_aexp e @ ins); state_rel s t; e = BinOp op val1 val2; op = Minus\<rbrakk>
    \<Longrightarrow> \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = val \<and>
      REG t' RName_2usr = REG t RName_2usr"
  apply (drule comp_aexp_mov_correct, simp, safe)
  apply (drule comp_aexp_mov_correct, simp, safe)
  apply (drule sub_reg_correct, simp, simp, simp, safe)
  apply (simp add: steps_add steps_inc)
  done

lemma comp_aexp_BinOp_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some val; code_installed t (comp_aexp e @ ins); state_rel s t; e = BinOp op val1 val2\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = val \<and>
      REG t' RName_2usr = REG t RName_2usr"
  apply (cases op)
   apply (rule comp_aexp_BinOp_Plus_correct, force+)
  apply (rule comp_aexp_BinOp_Minus_correct, force+)
  done

lemma comp_aexp_HeapLookup_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some val; code_installed t (comp_aexp e @ ins); state_rel s t; e = HeapLookup x4\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = val \<and>
      REG t' RName_2usr = REG t RName_2usr"
  apply (drule comp_aexp_mov_correct, simp, safe)
  apply (drule ldr_imm_correct, simp, simp, safe)
  apply (simp add: steps_add steps_inc)
  done

lemma comp_aexp_correct:
  "\<lbrakk>aval e s = Some val;
    code_installed t (comp_aexp e);
    state_rel s t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t (length (comp_aexp e)) = t' \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = val \<and>
        REG t' RName_2usr = REG t RName_2usr"
  apply (cases e)
     apply (rule comp_aexp_Const_correct, force+)
    apply (rule comp_aexp_UnOp_correct, force+)
   apply (rule comp_aexp_BinOp_correct, force+)
  apply (rule comp_aexp_HeapLookup_correct, force+)
  done

lemma comp_bexp_mov_correct:
  "\<lbrakk>state_rel s t;
    code_installed t (comp_bexp_mov reg val @ ins)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t (length (comp_bexp_mov reg val)) = t' \<and>
        code_installed t' ins \<and>
        state_rel s t' \<and>
        REG t' RName_0usr = (if reg = 0 then (if val then 1 else 0) else REG t RName_0usr) \<and>
        REG t' RName_1usr = (if reg = 1 then (if val then 1 else 0) else REG t RName_1usr)"
  apply (cases val)
   apply (simp only: comp_bexp_mov_def)
   apply (drule_tac val = "1" in mov_imm_correct, simp, safe, simp)
  apply (simp only: comp_bexp_mov_def)
  apply (drule_tac val = "0" in mov_imm_correct, simp, safe, simp)
  done

lemma comp_bexp_BConst_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val; code_installed t (comp_bexp b @ ins); state_rel s t; b = BConst x\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_bexp b)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = (if val then 1 else 0)"
  apply (drule comp_bexp_mov_correct, simp, simp)
  done

lemma comp_bexp_BComp_Less_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val; code_installed t (comp_bexp b @ ins); state_rel s t; b = BComp op a1 a2; op = Less\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_bexp b)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = (if val then 1 else 0)"
  sorry

lemma comp_bexp_BComp_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val; code_installed t (comp_bexp b @ ins); state_rel s t; b = BComp op a1 a2\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_bexp b)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = (if val then 1 else 0)"
  apply (cases op)
  apply (rule comp_bexp_BComp_Less_correct, force+)
  done

lemma comp_bexp_BBinOp_And_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val; code_installed t (comp_bexp b @ ins); state_rel s t; b = BBinOp op b1 b2; op = And\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_bexp b)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = (if val then 1 else 0)"
  apply (drule comp_bexp_mov_correct, simp, safe)
  apply (drule comp_bexp_mov_correct, simp, safe)
  apply (drule and_reg_correct, simp, simp, simp, safe)
  apply (simp add: steps_add steps_inc, safe)
  done

lemma comp_bexp_BBinOp_Or_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val; code_installed t (comp_bexp b @ ins); state_rel s t; b = BBinOp op b1 b2; op = Or\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_bexp b)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = (if val then 1 else 0)"
  apply (drule comp_bexp_mov_correct, simp, safe)
  apply (drule comp_bexp_mov_correct, simp, safe)
  apply (drule or_reg_correct, simp, simp, simp, safe)
  apply (simp add: steps_add steps_inc, safe)
  done

lemma comp_bexp_BBinOp_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val; code_installed t (comp_bexp b @ ins); state_rel s t; b = BBinOp op b1 b2\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_bexp b)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = (if val then 1 else 0)"
  apply (cases op)
   apply (rule comp_bexp_BBinOp_And_correct, force+)
  apply (rule comp_bexp_BBinOp_Or_correct, force+)
  done

lemma comp_bexp_BUnOp_Not_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val; code_installed t (comp_bexp b @ ins); state_rel s t; b = BUnOp op a; op = bunop.Not\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_bexp b)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = (if val then 1 else 0)"
  apply (cases val)
   apply (drule_tac ins = "cmp_imm 0 0 # moveq_imm 0 1 # movne_imm 0 0 # ins" in comp_bexp_mov_correct, simp, safe)
   apply (drule_tac ins = "moveq_imm 0 1 # movne_imm 0 0 # ins" in cmp_imm_correct, simp, simp, safe)
   apply (drule_tac ins = "movne_imm 0 0 # ins" and val = "1" in moveq_imm_correct, simp, safe)
    apply (drule_tac ins = "ins" and val = "0" in movne_imm_correct, simp, safe)
    apply (simp add: comp_bexp_mov_def)
   apply (drule_tac ins = "ins" and val = "0" in movne_imm_correct, simp, safe)
   apply (simp add: comp_bexp_mov_def)
  apply (drule_tac ins = "cmp_imm 0 0 # moveq_imm 0 1 # movne_imm 0 0 # ins" in comp_bexp_mov_correct, simp, safe)
  apply (drule_tac ins = "moveq_imm 0 1 # movne_imm 0 0 # ins" in cmp_imm_correct, simp, simp, safe)
  apply (drule_tac ins = "movne_imm 0 0 # ins" and val = "1" in moveq_imm_correct, simp, safe)
   apply (drule_tac ins = "ins" and val = "0" in movne_imm_correct, simp, safe)
   apply (simp add: comp_bexp_mov_def)
  apply (drule_tac ins = "ins" and val = "0" in movne_imm_correct, simp, safe)
  apply (simp add: comp_bexp_mov_def)
  done

lemma comp_bexp_BUnOp_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val; code_installed t (comp_bexp b @ ins); state_rel s t; b = BUnOp op a\<rbrakk> \<Longrightarrow>
    \<exists>t'. steps t (length (comp_bexp b)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      state.REG t' RName_0usr = (if val then 1 else 0)"
  apply (cases op)
  apply (rule comp_bexp_BUnOp_Not_correct, force+)
  done

lemma comp_bexp_correct:
  "\<lbrakk>bval e s = Some value;
    code_installed t (comp_bexp e @ ins);
    state_rel s t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t (length (comp_bexp e)) = t' \<and>
      code_installed t' ins \<and>
      state_rel s t' \<and>
      REG t' RName_0usr = (if value then 1 else 0)"
  apply (cases e)
     apply (rule comp_bexp_BConst_correct, force+)
    apply (rule comp_bexp_BComp_correct, force+)
   apply (rule comp_bexp_BBinOp_correct, force+)
  apply (rule comp_bexp_BUnOp_correct, force+)
  done

lemma comp_Assign_correct:
  "\<lbrakk>\<lbrakk>lval\<rbrakk> s = Some vp;
    \<lbrakk>rval\<rbrakk> s = Some v;
    Addr vp \<notin> incon_set s;
    addr_trans s (Addr vp) = Some pp;
    code_installed t (comp_aexp lval @ mov_reg 2 0 # comp_aexp rval @ str_imm 0 2 0 # ins);
    state_rel s t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps (snd (Next (snd (Next t)))) (length (comp_aexp lval) + length (comp_aexp rval)) = t' \<and>
        code_installed t' ins \<and>
        state_rel (s\<lparr>heap := heap s(pp \<mapsto> v), incon_set := iset_upd s pp v, p_state.global_set := gset_upd s pp v\<rparr>) t'"
  apply (drule_tac ins = "mov_reg 2 0 # comp_aexp rval @ str_imm 0 2 0 # ins" in comp_aexp_correct, simp, simp, safe)
  apply (drule_tac ins = "comp_aexp rval @ str_imm 0 2 0 # ins" and val = "vp" in mov_reg_correct, simp, simp, safe)
  apply (drule_tac ins = "str_imm 0 2 0 # ins" in comp_aexp_correct, simp, simp, safe)
  apply (drule_tac ins = "ins" and pp = "pp" in str_imm_correct, simp, simp, simp, safe)
  apply (simp add: steps_add steps_inc)
  done

lemma comp_Seq_correct:
  "\<lbrakk>\<forall>t::'a set_tlb_state_scheme. code_installed t (comp_com c1) \<and> state_rel s1 t \<longrightarrow> state_rel s2 (steps t (length (comp_com c1)));
    \<forall>t::'a set_tlb_state_scheme. code_installed t (comp_com c2) \<and> state_rel s2 t \<longrightarrow> state_rel y (steps t (length (comp_com c2)));
    code_installed (t::'a set_tlb_state_scheme) (comp_com c1 @ comp_com c2);
    state_rel s1 t\<rbrakk>
       \<Longrightarrow> state_rel y (steps t (length (comp_com c1) + length (comp_com c2)))"
  apply (frule code_installed_append)
  apply (subgoal_tac "state_rel s2 (steps t (length (comp_com c1)))")
   apply (drule code_installed_prepend)
   apply (subgoal_tac "state_rel y (steps (steps t (length (comp_com c1))) (length (comp_com c2)))")
    apply (clarsimp simp: steps_add)
  by (force+)

lemma comp_IfTrue_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some True; (c1, s) \<Rightarrow> Some y;
        \<forall>t::'a set_tlb_state_scheme. code_installed t (comp_com c1) \<and> state_rel s t \<longrightarrow> state_rel y (steps t (length (comp_com c1)));
        code_installed ta
         (let i1 = comp_com c1; i2 = comp_com c2
          in comp_bexp b @ cmp_imm 0 0 # beq_imm (code_size i1 - 1) # i1 @ b_imm (code_size i2 - 1) # i2);
        state_rel s ta\<rbrakk>
       \<Longrightarrow> state_rel y
            (steps ta
              (length
                (let i1 = comp_com c1; i2 = comp_com c2
                 in comp_bexp b @ cmp_imm 0 0 # beq_imm (code_size i1 - 1) # i1 @ b_imm (code_size i2 - 1) # i2)))"
  apply (clarsimp simp: Let_def)
  apply (drule_tac ins = "cmp_imm 0 0 # beq_imm (code_size (comp_com c1) - 1) # comp_com c1 @ b_imm (code_size (comp_com c2) - 1) # comp_com c2" in comp_bexp_correct, simp, simp)
  apply safe
  apply (drule_tac ins = "beq_imm (code_size (comp_com c1) - 1) # comp_com c1 @ b_imm (code_size (comp_com c2) - 1) # comp_com c2" in cmp_imm_correct, simp, simp)
  apply safe
  apply (drule code_installed_append)
  sorry

lemma comp_IfFalse_correct:
  "\<And>b s c2 c1 ta y.
       \<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some False; (c2, s) \<Rightarrow> Some y;
        \<And>t. \<lbrakk>code_installed t (comp_com c2); state_rel s t\<rbrakk> \<Longrightarrow> state_rel y (steps t (length (comp_com c2)));
        code_installed ta
         (let i1 = comp_com c1; i2 = comp_com c2
          in comp_bexp b @ cmp_imm 0 0 # beq_imm (code_size i1 - 1) # i1 @ b_imm (code_size i2 - 1) # i2);
        state_rel s ta\<rbrakk>
       \<Longrightarrow> state_rel y
            (steps ta
              (length
                (let i1 = comp_com c1; i2 = comp_com c2
                 in comp_bexp b @ cmp_imm 0 0 # beq_imm (code_size i1 - 1) # i1 @ b_imm (code_size i2 - 1) # i2)))"
  sorry

lemma comp_WhileFalse_correct:
  "\<And>b s c t.
       \<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some False;
        code_installed t
         (let i1 = comp_bexp b; i2 = comp_com c
          in i1 @ cmp_imm 0 0 # beq_imm (code_size i2 - 1) # i2 @ [b_imm (- code_size i1 - code_size i2 + 0xFFFFFC)]);
        state_rel s t\<rbrakk>
       \<Longrightarrow> state_rel s
            (steps t
              (length
                (let i1 = comp_bexp b; i2 = comp_com c
                 in i1 @ cmp_imm 0 0 # beq_imm (code_size i2 - 1) # i2 @ [b_imm (- code_size i1 - code_size i2 + 0xFFFFFC)])))"
  sorry

lemma comp_WhileTrue_correct:
  "\<And>b s c s'' t y.
       \<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some True; (c, s) \<Rightarrow> Some s'';
        \<And>t. \<lbrakk>code_installed t (comp_com c); state_rel s t\<rbrakk> \<Longrightarrow> state_rel s'' (steps t (length (comp_com c))); (WHILE b DO c, s'') \<Rightarrow> Some y;
        \<And>t. \<lbrakk>code_installed t
               (let i1 = comp_bexp b; i2 = comp_com c
                in i1 @ cmp_imm 0 0 # beq_imm (code_size i2 - 1) # i2 @ [b_imm (- code_size i1 - code_size i2 + 0xFFFFFC)]);
              state_rel s'' t\<rbrakk>
             \<Longrightarrow> state_rel y
                  (steps t
                    (length
                      (let i1 = comp_bexp b; i2 = comp_com c
                       in i1 @ cmp_imm 0 0 # beq_imm (code_size i2 - 1) # i2 @ [b_imm (- code_size i1 - code_size i2 + 0xFFFFFC)])));
        code_installed t
         (let i1 = comp_bexp b; i2 = comp_com c
          in i1 @ cmp_imm 0 0 # beq_imm (code_size i2 - 1) # i2 @ [b_imm (- code_size i1 - code_size i2 + 0xFFFFFC)]);
        state_rel s t\<rbrakk>
       \<Longrightarrow> state_rel y
            (steps t
              (length
                (let i1 = comp_bexp b; i2 = comp_com c
                 in i1 @ cmp_imm 0 0 # beq_imm (code_size i2 - 1) # i2 @ [b_imm (- code_size i1 - code_size i2 + 0xFFFFFC)])))"
  sorry

lemma comp_Flush_correct:
  "\<And>s f flush_effect_snp flush_effect_glb flush_effect_iset t.
       \<lbrakk>mode s = Kernel; code_installed t (comp_flush f); state_rel s t\<rbrakk>
       \<Longrightarrow> state_rel
            (s\<lparr>incon_set := flush_effect_iset f (incon_set s) (p_state.global_set s) (asid s),
                 p_state.global_set := flush_effect_glb f (p_state.global_set s) (asid s) (heap s) (root s),
                 ptable_snapshot := flush_effect_snp f (ptable_snapshot s) (asid s)\<rparr>)
            (steps t (length (comp_flush f)))"
  sorry

lemma comp_UpdateTTBR0_correct:
  "\<And>s rte rt t.
       \<lbrakk>mode s = Kernel; \<lbrakk>rte\<rbrakk> s = Some rt; code_installed t (comp_aexp rte @ [mcr_reg 0 2 0 0xF 0 0]); state_rel s t\<rbrakk>
       \<Longrightarrow> state_rel (s\<lparr>root := Addr rt, incon_set := iset_upd' s rt, p_state.global_set := gset_upd' s rt\<rparr>)
            (steps (snd (Next t)) (length (comp_aexp rte)))"
  sorry

lemma comp_UpdateASID_correct:
  "\<And>s a t y ya.
       \<lbrakk>mode s = Kernel; state_rel s t; Fetch t = (mov_imm 0 (UCAST(8 \<rightarrow> 12) a), y);
        Fetch (y\<lparr>state.REG := (state.REG t)(RName_PC := state.REG t RName_PC + 4)\<rparr>) = (mcr_reg 0 0xD 0 0xF 0 0, ya)\<rbrakk>
       \<Longrightarrow> state_rel
            (s\<lparr>asid := a,
                 incon_set :=
                   incon_load (cur_pt_snp' (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s)) (incon_set s) (p_state.global_set s)
                    a (heap s) (root s),
                 ptable_snapshot := cur_pt_snp' (ptable_snapshot s) (incon_set s) (heap s) (root s) (asid s)\<rparr>)
            (snd (Next (snd (Next t))))"
  sorry

lemma comp_SetMode_correct:
  "\<And>s m t.
       \<lbrakk>mode s = Kernel; code_installed t (comp_set_mode m); state_rel s t\<rbrakk> \<Longrightarrow> state_rel (s\<lparr>mode := m\<rparr>) (steps t (length (comp_set_mode m)))"
  sorry

theorem comp_com_correct:
  "\<lbrakk>(p,s) \<Rightarrow> st;
    code_installed t (comp_com p);
    st \<noteq> None;
    state_rel s t
    \<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t (length (comp_com p)) = t' \<and> state_rel (the st) t'"
  apply (induction arbitrary: t rule: big_step_induct; clarsimp)
           apply(drule comp_Assign_correct, force+)
          apply(rule comp_Seq_correct,force+)
         apply(rule comp_IfTrue_correct,force+)
        apply(rule comp_IfFalse_correct,force+)
       apply(rule comp_WhileFalse_correct,simp+)
      apply(rule comp_WhileTrue_correct,force+)
     apply(rule comp_Flush_correct,simp+)
    apply(rule comp_UpdateTTBR0_correct,simp+)
   apply(rule comp_UpdateASID_correct,simp+)
  apply(rule comp_SetMode_correct,simp+)
  done

end
