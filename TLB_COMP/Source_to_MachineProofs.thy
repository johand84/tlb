theory Source_to_MachineProofs

imports Source_to_Machine
        Source_to_MachineAssumptions

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

definition
  flags_preserved :: "'a set_tlb_state_scheme \<Rightarrow> 'a set_tlb_state_scheme \<Rightarrow> bool"
where
  "flags_preserved s t = (PSR.Z (CPSR s) = PSR.Z (CPSR t))"

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
    (PSR.M (CPSR s) = 0x10 \<or> PSR.M (CPSR s) = 0x13) \<and>
    exception s = NoException
  )"

definition
  machine_state_preserved :: "'a set_tlb_state_scheme \<Rightarrow> 'a set_tlb_state_scheme \<Rightarrow> bool"
where
  "machine_state_preserved s t \<equiv>
    ASID s = ASID t \<and>
    TTBR0 s = TTBR0 t \<and>
    iset (set_tlb s) = iset (set_tlb t) \<and>
    global_set (set_tlb s) = global_set (set_tlb t) \<and>
    snapshot (set_tlb s) = snapshot (set_tlb t) \<and>
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
     aligned (root s) \<and>
     (incon_set s = iset (set_tlb t)) \<and>
     (p_state.global_set s = global_set (set_tlb t)) \<and>
     (ptable_snapshot s = snapshot (set_tlb t)) \<and>
     mode_rel (mode s) (PSR.M (CPSR t)) \<and>
     heap_rel s t"


lemma load_machine_word_eq:
  "\<lbrakk>state_rel s t; heap s p = Some z; aligned p\<rbrakk> \<Longrightarrow> 
    load_machine_word (MEM t) p = Some z"
  apply (clarsimp simp: load_machine_word_def load_value_def 
                        state_rel_def heap_rel_def)
  apply (clarsimp simp: load_list_def deoption_list_def load_list_basic_def)
  apply word_bitwise 
  sorry
  

lemma get_pde_eq:
  "\<lbrakk>state_rel s t; get_pde' (heap s) (root s) va = Some e\<rbrakk> \<Longrightarrow> 
     get_pde (MEM t) (TTBR0 t) va = Some e"
  apply (clarsimp simp: get_pde'_def decode_heap_pde'_def get_pde_def decode_heap_pde_def)
  apply (frule_tac p = "root s r+ (vaddr_pd_index (addr_val va) << 2)" in load_machine_word_eq, simp)
   apply (clarsimp simp: state_rel_def)
   apply (clarsimp simp: aligned_def vaddr_pd_index_def addr_add_def mask_def)
   apply word_bitwise
  apply (clarsimp simp: state_rel_def)
  done

lemma get_pde_aligned:
  "\<lbrakk>get_pde' (heap s) (root s) va = Some (PageTablePDE pa)\<rbrakk> \<Longrightarrow> 
     aligned pa"
  apply (clarsimp simp: get_pde'_def decode_heap_pde'_def get_pde_def
                        decode_heap_pde_def aligned_def decode_pde_def Let_def 
                        decode_pde_section_def decode_pde_pt_def pt_base_mask_def mask_def
                  split:if_split_asm)
  by word_bitwise

lemma get_pte_eq:
  "\<lbrakk>state_rel s t; get_pte' (heap s) pa va = Some (SmallPagePTE a b) ;
    aligned pa\<rbrakk> \<Longrightarrow> 
   get_pte (MEM t) pa va = Some (SmallPagePTE a b)"
  apply (clarsimp simp: get_pte'_def decode_heap_pte'_def)
  apply (clarsimp simp: get_pte_def decode_heap_pte_def)
  apply (frule_tac p = "pa r+ (vaddr_pt_index (addr_val va) << 2)" and z = "z" in load_machine_word_eq; simp?)
  apply (clarsimp simp: aligned_def vaddr_pt_index_def mask_def addr_add_def)
 by word_bitwise


lemma addr_trans_mmu_translate_eq:
  "\<lbrakk>addr_trans s va = Some pa ;  va \<notin> incon_set s; 
    state_rel s t\<rbrakk> \<Longrightarrow> mmu_translate va t = (pa, t)"
  apply (subgoal_tac "va \<notin> iset (set_tlb t)") 
   prefer 2 
   apply (clarsimp simp: state_rel_def)
  apply (clarsimp simp: addr_trans_def ptable_lift_m_def 
      lookup_pde_perm_def)
  apply (clarsimp simp: filter_pde_def split: option.splits if_split_asm)
  apply (erule disjE)
   apply (clarsimp simp: lookup_pde'_def split: option.splits pde.splits)
    apply (clarsimp simp: lookup_pte'_def split: pte.splits option.splits)
    apply (clarsimp simp: mmu_translate_set_tlb_state_ext_def Let_def pt_walk_def)
    apply (frule_tac va = "va" in get_pde_eq; simp?)
    apply clarsimp
    apply (subgoal_tac "get_pte (MEM t) x3 va = Some (SmallPagePTE a b)")
     prefer 2
     apply (rule_tac s = "s" in get_pte_eq, simp,simp, drule get_pde_aligned, simp)
    apply clarsimp
    apply (clarsimp simp: is_fault_def)
    apply (clarsimp simp: word_extract_def word_bits_def vaddr_offset_def mask_def)
    defer 
    apply (clarsimp simp: mmu_translate_set_tlb_state_ext_def Let_def pt_walk_def)
    apply (frule_tac va = "va" in get_pde_eq; simp?)
    apply (clarsimp simp: is_fault_def) 
    apply (clarsimp simp: word_extract_def word_bits_def vaddr_offset_def mask_def)
    defer 
     apply (clarsimp simp: lookup_pde'_def split: option.splits pde.splits)
    apply (clarsimp simp: lookup_pte'_def split: pte.splits option.splits)
    apply (clarsimp simp: mmu_translate_set_tlb_state_ext_def Let_def pt_walk_def)
    apply (frule_tac va = "va" in get_pde_eq; simp?)
    apply clarsimp
    apply (subgoal_tac "get_pte (MEM t) x3 va = Some (SmallPagePTE a b)")
     prefer 2
     apply (rule_tac s = "s" in get_pte_eq, simp,simp, drule get_pde_aligned, simp)
    apply clarsimp
    apply (clarsimp simp: is_fault_def)
    apply (clarsimp simp: word_extract_def word_bits_def vaddr_offset_def mask_def)
    defer 
    apply (clarsimp simp: mmu_translate_set_tlb_state_ext_def Let_def pt_walk_def)
    apply (frule_tac va = "va" in get_pde_eq; simp?)
    apply (clarsimp simp: is_fault_def) 
    apply (clarsimp simp: word_extract_def word_bits_def vaddr_offset_def mask_def)
  sorry


lemma mem_read_mmu_translate_eq:
  "\<lbrakk>state_rel s t ;  ptable_lift_m (heap s) (TTBR0 t) (mode s) va = Some pa;
    aligned pa;  
   mem_read_hp' (incon_set s) (heap s) (root s) (mode s) va = Some val\<rbrakk> \<Longrightarrow>
    mmu_read_size (va, 4) t = (to_bl val, t)"
  apply (clarsimp simp: mem_read_hp'_def split: if_split_asm)
  apply (clarsimp simp: fun_rcomp_option_def split: option.splits)
  apply (clarsimp simp: mmu_read_size_set_tlb_state_ext_def)
  apply (subgoal_tac " mmu_translate va t = (pa, t)")
   prefer 2
   apply (rule_tac s = "s" in addr_trans_mmu_translate_eq; 
          simp add: addr_trans_def)
  apply (clarsimp simp: load_value_word_hp_def load_list_word_hp_def
                        load_list_def deoption_list_def split: if_split_asm)
   apply (clarsimp simp: mem_read1_def mem1_def state_rel_def heap_rel_def)
  apply clarsimp
  sorry
 


fun
  steps :: "'a set_tlb_state_scheme \<Rightarrow> nat \<Rightarrow> 'a set_tlb_state_scheme"
where
  "steps s 0 = s" |
  "steps s (Suc i) = steps (snd (Next s)) i"

definition
  code_installed :: "'a set_tlb_state_scheme \<Rightarrow> MachineCode list \<Rightarrow>  bool"
where
  "code_installed t mc \<equiv>
        unat (REG t RName_PC) + 4 * length mc < 2^32 \<and> (
         \<forall>i. let pci = REG t RName_PC;
                 pcf = REG (steps t i) RName_PC in
             pci \<le> pcf \<and>
             unat (pcf - pci) div 4 < length mc \<longrightarrow>
               (let (m, ft) = Fetch (steps t i) in
                exception ft = NoException \<and>
                m =  mc ! (unat (pcf - pci) div 4)))"

(* Proofs *)

lemma code_installed_append1:
  "\<lbrakk>code_installed t (ca # cb)\<rbrakk> \<Longrightarrow> code_installed t [ca]"
  apply (clarsimp simp: code_installed_def Let_def split: prod.splits)
  by (drule_tac x = "i" in spec, simp)

lemma code_installed_append:
  "code_installed t (a @ b) \<Longrightarrow> code_installed t a"
  apply (clarsimp simp: code_installed_def Let_def split: prod.splits)
  apply (drule_tac x = "i" in spec, simp)
  by (simp add: nth_append)

lemma code_installed_prepend:
  "\<lbrakk>code_installed t (ca @ cb);
    REG (steps t k) RName_PC = REG t RName_PC + 4 * (word_of_int (int (length ca)))\<rbrakk> \<Longrightarrow>
    code_installed (steps t k) cb"
  sorry

lemma code_installed_implies_Fetch:
  "code_installed t (x#xs) \<Longrightarrow> Fetch t = (x, snd (Fetch t))"
  apply (clarsimp simp: code_installed_def Let_def)
  apply (erule_tac x = "0" in allE, clarsimp)
  done

lemma general_purpose_reg_correct:
  "general_purpose_reg reg \<Longrightarrow>
    bin_to_reg reg \<noteq> RName_SPusr \<and>
    bin_to_reg reg \<noteq> RName_LRusr \<and>
    bin_to_reg reg \<noteq> RName_PC"
  by (simp add: bin_to_reg_def general_purpose_reg_def, safe, simp+)

lemma state_rel_preserved:
  "\<lbrakk>state_rel s t; machine_state_preserved t t'\<rbrakk> \<Longrightarrow> state_rel s t'"
  apply (simp add: heap_rel_def machine_state_preserved_def state_rel_def)
  by force

lemma steps_add:
  "(steps (steps t l1) l2) = (steps t (l1 + l2))"
  by (induction l1 arbitrary: t, simp, simp)

lemma steps_inc1:
  "steps (snd (Next t)) l = steps t (l+1)"
  by simp

lemma steps_inc:
  "snd (Next (steps t l)) = steps t (l+1)"
  by (metis steps.simps(1) steps_add steps_inc1)

lemma steps_one:
  "snd (Next t) = steps t 1"
  by simp

lemma code_installed_prepend1:
  "\<lbrakk>code_installed t (ca # cb);
    REG (steps t k) RName_PC = REG t RName_PC + 4\<rbrakk> \<Longrightarrow>
    code_installed (steps t k) cb"
  sorry

lemma machine_config_mmu_translate:
  "\<lbrakk>mmu_translate v s = (p, t); machine_config s\<rbrakk> \<Longrightarrow>
    flags_preserved s t \<and>
    machine_config t \<and>
    machine_state_preserved s t \<and>
    REG s = REG t"
  apply (clarsimp simp: Let_def
                        flags_preserved_def
                        machine_config_def
                        machine_state_preserved_def
                        mmu_translate_set_tlb_state_ext_def
                  split: if_split_asm)
   apply (clarsimp simp: raise'exception_def machine_config_def split:if_split_asm)+
  sorry

lemma machine_config_mmu_read_size:
  "\<lbrakk>mmu_read_size v s = (r, t); machine_config s\<rbrakk> \<Longrightarrow>
    flags_preserved s t \<and>
    machine_config t \<and>
    machine_state_preserved s t \<and>
    REG s = REG t"
  apply (clarsimp simp: mmu_read_size_set_tlb_state_ext_def split: prod.splits)
  apply (frule machine_config_mmu_translate, simp)
  apply (clarsimp simp: mem_read1_def split: if_split_asm)
      apply (clarsimp simp: mem1_def raise'exception_def flags_preserved_def machine_config_def machine_state_preserved_def
                     split: option.splits if_split_asm)
  sorry

lemma Fetch_correct:
  "\<lbrakk>Fetch s = (mc, t);
    machine_config s\<rbrakk> \<Longrightarrow>
      flags_preserved s t \<and>
      machine_config t \<and>
      machine_state_preserved s t \<and>
      REG s = REG t"
  apply (clarsimp simp: machine_config_def Fetch_def CurrentInstrSet_def
                        ISETSTATE_def word_cat_def)
  apply (clarsimp simp: MemA_def CurrentModeIsNotUser_def BadMode_def)
  apply (erule disjE; clarsimp)
   apply (clarsimp simp: MemA_with_priv_def split: prod.splits)
    apply (frule machine_config_mmu_read_size, clarsimp simp: machine_config_def)
    apply (clarsimp simp: flags_preserved_def machine_config_def machine_state_preserved_def)
  apply (clarsimp simp: MemA_with_priv_def split: prod.splits)
  apply (frule machine_config_mmu_read_size, clarsimp simp: machine_config_def)
  by (clarsimp simp: flags_preserved_def machine_config_def machine_state_preserved_def)

lemma Aligned1_correct:
  "Aligned1 (Addr val, 4) \<Longrightarrow> Aligned1 (Addr (val + 4), 4)"
  sorry

lemma ARMExpandImm_C_correct:
  "\<lbrakk>machine_config s;
    ARMExpandImm_C (imm12, PSR.C (CPSR s)) s = (x, t);
    word_extract 11 8 imm12 = (0::4 word)\<rbrakk> \<Longrightarrow>
      s = t \<and>
      x = (ucast imm12, PSR.C (CPSR s))"
  apply (simp add: ARMExpandImm_C_def Shift_C_def split: SRType.splits if_split_asm, clarify)
  apply (clarsimp simp: word_extract_def word_bits_def mask_def)
  apply (subgoal_tac "((word_of_int (uint (UCAST(12 \<rightarrow> 8) (imm12 && 0xFF)))) :: 32 word) =
    (UCAST(8 \<rightarrow> 32) (UCAST(12 \<rightarrow> 8) (imm12 && 0xFF)))")
   prefer 2
   apply (force simp: ucast_def)
  apply (simp add:)
  apply word_bitwise
  done

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

lemma HaveSecurityExt_correct:
  "machine_config s \<Longrightarrow> HaveSecurityExt () s = (False, s)"
  by (simp add: ArchVersion_correct HaveSecurityExt_def machine_config_def)

lemma HaveVirtExt_correct:
  "machine_config s \<Longrightarrow> HaveVirtExt () s = (False, s)"
  by (simp add: ArchVersion_correct HaveVirtExt_def machine_config_def)

lemma BadMode_correct:
  "machine_config s \<Longrightarrow> BadMode (PSR.M (CPSR s)) s = (False, s)"
  by (simp add: BadMode_def
                HaveSecurityExt_correct
                HaveVirtExt_correct
                machine_config_def, safe, simp+)

lemma CurrentInstrSet_correct:
  "machine_config s \<Longrightarrow> CurrentInstrSet () s = (InstrSet_ARM, s)"
  by (simp add: CurrentInstrSet_def ISETSTATE_def machine_config_def word_cat_def split: if_split_asm)

lemma BranchWritePC_correct:
  "\<lbrakk>machine_config s;
    BranchWritePC (REG s RName_PC + 8 + (ucast offset)) s = ((), t)\<rbrakk> \<Longrightarrow>
      t = s\<lparr>REG := (REG s)(RName_PC := REG s RName_PC + (ucast offset) + 8)\<rparr> \<and>
        machine_config t \<and>
        machine_state_preserved s t"
  apply (frule CurrentInstrSet_correct)
  apply (frule ArchVersion_correct, safe)
    apply (simp add: BranchWritePC_def BranchTo_def)
    defer
    defer
    apply (simp add: BranchWritePC_def BranchTo_def machine_state_preserved_def, safe, simp+)
  sorry

lemma ExpandImm_C_correct:
  "\<lbrakk>machine_config s;
    ExpandImm_C (val, PSR.C (CPSR s)) s = (x, t);
    word_extract 11 8 val = (0::4 word)\<rbrakk> \<Longrightarrow>
      s = t \<and>
      x = (ucast val, PSR.C (CPSR s))"
  apply (simp add: ExpandImm_C_def split: if_split_asm)
   apply (simp add: machine_config_def)
  apply (frule ARMExpandImm_C_correct, simp, simp, simp)
  done

lemma ITAdvance_correct:
  "machine_config s \<Longrightarrow> ITAdvance () s = ((), s)"
  by (simp add: HaveThumb2_def ITAdvance_def machine_config_def)

lemma IncPC_correct:
  "\<lbrakk>machine_config s;
    IncPC () s = ((),t)\<rbrakk> \<Longrightarrow>
      t = s\<lparr>REG := (REG s)(RName_PC := REG s RName_PC + 4)\<rparr> \<and>
      flags_preserved s t\<and>
      machine_config t \<and>
      machine_state_preserved s t"
  apply (simp add: BranchTo_def
                   IncPC_def
                   ThisInstrLength_def
                   flags_preserved_def
                   machine_config_def
                   machine_state_preserved_def, safe)
  by (drule Aligned1_correct, simp)+

lemma IsSecure_correct:
  "machine_config s \<Longrightarrow> IsSecure () s = (True, s)"
  by (simp add: HaveSecurityExt_def IsSecure_def machine_config_def)

lemma RfiqBankSelect_correct:
  "\<lbrakk>machine_config s; general_purpose_reg reg\<rbrakk> \<Longrightarrow> RfiqBankSelect (PSR.M (CPSR s),usr,fiq) s = (usr,s)"
  by (simp add: BadMode_correct RBankSelect_def RfiqBankSelect_def machine_config_def bin_to_reg_def, safe, simp)

lemma LookUpRName_correct:
  "\<lbrakk>machine_config s; general_purpose_reg reg\<rbrakk> \<Longrightarrow> LookUpRName (reg, PSR.M (CPSR s)) s = (bin_to_reg reg, s)"
  by (simp add: LookUpRName_def RfiqBankSelect_correct bin_to_reg_def general_purpose_reg_def, safe, simp+)

lemma PC_correct:
  "\<lbrakk>machine_config s;
    PC s = (x, t)\<rbrakk> \<Longrightarrow> s = t \<and> x = REG s RName_PC + 8"
  by (simp add: CurrentInstrSet_correct PC_def R_def, safe)

lemma R_correct:
  "\<lbrakk>general_purpose_reg reg; machine_config s\<rbrakk> \<Longrightarrow> R reg s = (REG s (bin_to_reg reg), s)"
  by (simp add: IsSecure_correct LookUpRName_correct R_def Rmode_def general_purpose_reg_def, safe, simp+)

lemma write'R_correct:
  "\<lbrakk>machine_config s;
    write'R (val, reg) s = ((),t);
    general_purpose_reg reg\<rbrakk> \<Longrightarrow>
      t = s\<lparr>REG := (REG s)(bin_to_reg reg := val)\<rparr> \<and>
      machine_config t \<and>
      machine_state_preserved s t"
  apply (frule IsSecure_correct)
  apply (simp add: write'R_def write'Rmode_def split: if_split_asm prod.splits)
     apply (simp add: general_purpose_reg_def)
    apply (simp add: general_purpose_reg_def)
   apply (simp add: general_purpose_reg_def)
  apply (frule LookUpRName_correct)
   apply (simp add: machine_config_def, simp, clarify)
  apply (simp add: bin_to_reg_def
                   general_purpose_reg_def
                   machine_config_def
                   machine_state_preserved_def
              split: if_split_asm)
  done

lemma Run_nop_correct:
  "\<lbrakk>Run NoOperation s = ((), t);
    machine_config s\<rbrakk> \<Longrightarrow>
      flags_preserved s t \<and>
      machine_config t \<and>
      machine_state_preserved s t \<and>
      REG t = (REG s)(RName_PC := REG s RName_PC + 4)"
  apply (simp add: Run_def dfn'NoOperation_def)
  apply (frule IncPC_correct, simp, simp, safe)
  done

lemma Run_add_reg_correct:
  "\<lbrakk>machine_config s;
    Run (Data (Register (4, False, rd, rn, rm, SRType_LSL, 0))) s = ((), t);
    general_purpose_reg rd;
    general_purpose_reg rn;
    general_purpose_reg rm\<rbrakk> \<Longrightarrow>
      machine_config t \<and>
      machine_state_preserved s t \<and>
      REG t = (REG s)(bin_to_reg rd := REG s (bin_to_reg rn) + REG s (bin_to_reg rm),
                      RName_PC := REG s RName_PC + 4)"
  apply (simp add: Run_def dfn'Register_def doRegister_def split: prod.splits)
  apply (frule_tac reg = "rm" in R_correct, simp)
  apply (simp add: Shift_C_def split: if_split_asm)
   apply (simp add: general_purpose_reg_def)
  apply (simp add: DataProcessing_def
                   mask_def
                   word_bits_def
                   word_extract_def
              split: if_split_asm prod.splits)
   apply (simp add: general_purpose_reg_def)
  apply (frule_tac reg = "rn" in R_correct, simp)
  apply (simp add: DataProcessingALU_def, clarify)
  apply (frule write'R_correct, simp, simp, simp, safe)
    apply (frule IncPC_correct, simp, safe)
   apply (frule IncPC_correct, simp, safe)
   apply (simp add: machine_config_def machine_state_preserved_def)
  apply (simp add: AddWithCarry_def Let_def wi_hom_syms, safe)
  apply (frule IncPC_correct, simp, simp)
  apply (frule general_purpose_reg_correct, safe)
  apply (simp add: bin_to_reg_def general_purpose_reg_def split: if_split_asm)+
  done

lemma add_reg_correct:
  "\<lbrakk>Fetch t = (add_reg rd rn rm, ft);
    general_purpose_reg rd;
    general_purpose_reg rn;
    general_purpose_reg rm;
    machine_config t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        machine_config t' \<and>
        machine_state_preserved t t' \<and>
        REG t' = (REG t)(bin_to_reg rd := REG t (bin_to_reg rn) + REG t (bin_to_reg rm),
                         RName_PC := REG t RName_PC + 4)"
  apply (frule Fetch_correct, simp)
  apply (simp add: Decode_add_reg_correct Next_def split: prod.splits, safe)
    apply (frule Run_add_reg_correct, simp+, safe)
    apply (frule_tac s = "x2" in ITAdvance_correct)
    apply (simp add: snd_def)
   apply (frule Run_add_reg_correct, simp+, safe)
   apply (frule_tac s = "x2" in ITAdvance_correct)
   apply (simp add: machine_state_preserved_def snd_def)
  apply (frule Run_add_reg_correct, simp+, safe)
  apply (frule_tac s = "x2" in ITAdvance_correct)
  apply (simp add: snd_def)
  done

lemma Run_and_reg_correct:
  "\<lbrakk>machine_config s;
    Run (Data (Register (0, False, rd, rn, rm, SRType_LSL, 0))) s = ((), t);
    general_purpose_reg rd;
    general_purpose_reg rn;
    general_purpose_reg rm\<rbrakk> \<Longrightarrow>
      machine_config t \<and>
      machine_state_preserved s t \<and>
      REG t = (REG s)(bin_to_reg rd := REG s (bin_to_reg rn) && REG s (bin_to_reg rm),
                      RName_PC := REG s RName_PC + 4)"
  apply (simp add: Run_def dfn'Register_def doRegister_def split: prod.splits)
  apply (frule_tac reg = "rm" in R_correct, simp)
  apply (simp add: Shift_C_def split: if_split_asm)
   apply (simp add: general_purpose_reg_def)
  apply (simp add: DataProcessing_def
                   mask_def
                   word_bits_def
                   word_extract_def
              split: if_split_asm prod.splits)
  apply (frule_tac reg = "rn" in R_correct, simp)
  apply (simp add: DataProcessingALU_def)
  apply (frule write'R_correct, simp, simp, clarify)
  apply (frule IncPC_correct, simp, simp, safe)
       apply (frule general_purpose_reg_correct, safe, simp+)
      apply (frule general_purpose_reg_correct, safe, simp+)
     apply (frule general_purpose_reg_correct, safe, simp+)
   apply (simp add: machine_state_preserved_def)
  done

lemma and_reg_correct:
  "\<lbrakk>Fetch t = (and_reg rd rn rm, ft);
    general_purpose_reg rd;
    general_purpose_reg rn;
    general_purpose_reg rm;
    machine_config t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        machine_config t' \<and>
        machine_state_preserved t t' \<and>
        REG t' = (REG t)(bin_to_reg rd := REG t (bin_to_reg rn) && REG t (bin_to_reg rm),
                         RName_PC := REG t RName_PC + 4)"
  apply (frule Fetch_correct, simp)
  apply (simp add: Decode_and_reg_correct Next_def split: prod.splits, safe)
    apply (frule Run_and_reg_correct, simp+, safe)
    apply (frule_tac s = "x2" in ITAdvance_correct)
    apply (simp add: snd_def)
   apply (frule Run_and_reg_correct, simp+, safe)
   apply (frule_tac s = "x2" in ITAdvance_correct)
   apply (simp add: machine_state_preserved_def snd_def)
  apply (frule Run_and_reg_correct, simp+, safe)
  apply (frule_tac s = "x2" in ITAdvance_correct)
  apply (simp add: snd_def)
  done

lemma Run_b_imm_correct:
  "\<lbrakk>machine_config s;
    Run (Branch (BranchTarget (UCAST(24 \<rightarrow> 32) offset))) s = ((), t) \<rbrakk> \<Longrightarrow>
      machine_config t \<and>
      machine_state_preserved s t \<and>
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
        machine_config t' \<and>
        machine_state_preserved t t' \<and>
        REG t' = (REG t)(RName_PC := REG t RName_PC + (ucast offset) + 8)"
  apply (simp add: Next_def split: prod.splits)
  apply (frule Fetch_correct, simp, safe)
    apply (frule Decode_b_imm_correct, safe)
    apply (frule Run_b_imm_correct, simp, simp, safe)
    apply (frule_tac s = "x2a" in ITAdvance_correct, simp)
   apply (frule Decode_b_imm_correct, safe)
   apply (frule Run_b_imm_correct, simp, simp, safe)
   apply (frule_tac s = "x2a" in ITAdvance_correct, simp)
   apply (simp add: machine_state_preserved_def)
  apply (frule Decode_b_imm_correct, safe)
  apply (frule Run_b_imm_correct, simp, simp, safe)
  apply (frule_tac s = "x2a" in ITAdvance_correct, simp)
  done

lemma Run_cmp_imm_correct:
  "\<lbrakk>Run (Data (ArithLogicImmediate (0xA, True, 0, reg, 0))) s = ((), t);
    REG s (bin_to_reg reg) = (if val then 1 else 0);
    general_purpose_reg reg;
    machine_config s\<rbrakk> \<Longrightarrow>
      machine_config t \<and>
      machine_state_preserved s t \<and>
      PSR.Z (CPSR t) = (\<not>val) \<and>
      REG t = (REG s)(RName_PC := REG s RName_PC + 4)"
  apply (simp add: dfn'ArithLogicImmediate_def Run_def split: prod.splits)
  apply (frule ExpandImm_C_correct, simp)
   apply (simp add: word_bits_def word_extract_def)
  apply (simp add: ArithmeticOpcode_def
                   DataProcessing_def
                   mask_def
                   word_bits_def
                   word_extract_def
              split: prod.splits)
  apply (frule R_correct, simp)
  apply (simp add: AddWithCarry_def
                   Let_def
                   DataProcessingALU_def
                   max_word_def
                   wi_hom_syms)
  apply (subgoal_tac "machine_config (s\<lparr>CPSR := CPSR s\<lparr>PSR.N := REG s (bin_to_reg reg) !! 31,
                                                       PSR.Z := REG s (bin_to_reg reg) = 0,
                                                       PSR.C := True,
                                                       PSR.V := False\<rparr>\<rparr>)")
   apply (frule_tac s = "s\<lparr>CPSR := CPSR s\<lparr>PSR.N := REG s (bin_to_reg reg) !! 31,
                                          PSR.Z := REG s (bin_to_reg reg) = 0,
                                          PSR.C := True,
                                          PSR.V := False\<rparr>\<rparr>" in IncPC_correct, simp, safe)
      apply (simp add:  machine_config_def machine_state_preserved_def)+
  done

lemma cmp_imm_correct:
  "\<lbrakk>Fetch t = (cmp_imm reg 0, ft);
    REG t (bin_to_reg reg) = (if val then 1 else 0);
    general_purpose_reg reg;
     machine_config t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        machine_config t' \<and>
        machine_config_preserved t t' \<and>
        PSR.Z (CPSR t') = (\<not>val) \<and>
        REG t' = (REG t)(RName_PC := REG t RName_PC + 4)"
  apply (frule Fetch_correct, simp)
  apply (simp add: Decode_cmp_imm_correct Next_def split: prod.splits, safe)
      apply (frule Run_cmp_imm_correct, simp, safe)
       apply (frule_tac s = "x2" in ITAdvance_correct, simp)
      apply (frule_tac s = "x2" in ITAdvance_correct, simp)
     apply (frule Run_cmp_imm_correct, simp, safe)
      apply (frule_tac s = "x2" in ITAdvance_correct, simp add: machine_config_preserved_def)
     apply (frule_tac s = "x2" in ITAdvance_correct, simp add: machine_config_preserved_def)
    apply (frule Run_cmp_imm_correct, simp, safe)
    apply (frule_tac s = "x2" in ITAdvance_correct, simp)
   apply (frule Run_cmp_imm_correct, simp, safe)
   apply (frule_tac s = "x2" in ITAdvance_correct, simp)
  apply (frule Run_cmp_imm_correct, simp, safe)
   apply (frule_tac s = "x2" in ITAdvance_correct, simp)
  apply (frule Run_cmp_imm_correct, simp, safe)
  apply (frule_tac s = "x2" in ITAdvance_correct, simp)
  done

lemma ldr_imm_correct:
  "\<lbrakk>Fetch t = (ldr_imm rt rn 0, ft);
    general_purpose_reg rn;
    general_purpose_reg rt;
    machine_config t;
    mmu_read_size (Addr (REG t (bin_to_reg rn)), 4) t = (to_bl val, t)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        machine_config t' \<and>
        machine_config_preserved t t' \<and>
        REG t' = (REG t)(bin_to_reg rt := val,
                         RName_PC := REG t RName_PC + 4)"
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

lemma Run_mov_imm_correct:
  "\<lbrakk>Run (Data (ArithLogicImmediate (0xd, False, rd, 0, imm12))) s = ((), t);
    general_purpose_reg rd;
    machine_config s;
    word_extract 11 8 imm12 = (0::4 word)\<rbrakk> \<Longrightarrow>
      flags_preserved s t \<and>
      machine_config t \<and>
      machine_config_preserved s t \<and>
      REG t = (REG s)(bin_to_reg rd := ucast imm12,
                      RName_PC := REG s RName_PC + 4)"
  apply (simp add: Run_def dfn'ArithLogicImmediate_def split: if_split_asm prod.splits)
   apply (simp add: general_purpose_reg_def)
  apply (frule ExpandImm_C_correct, simp, simp)
  apply (simp add: DataProcessing_def mask_def word_bits_def word_extract_def split: prod.splits)
   apply (simp add: DataProcessingALU_def)
  apply (frule write'R_correct, simp, simp, clarify)
  apply (frule IncPC_correct, simp, safe, simp)
    apply (simp add: flags_preserved_def, simp)
   apply (simp add: machine_config_preserved_def, simp, rule)
  apply (simp add: bin_to_reg_def
                   general_purpose_reg_def
                   machine_config_def
              split: if_split_asm)
  done

lemma mov_imm_correct:
  "\<lbrakk>Fetch t = (mov_imm reg val, ft);
    general_purpose_reg reg;
    machine_config t;
    word_extract 11 8 val = (0::4 word)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        machine_config t' \<and>
        machine_config_preserved t t' \<and>
        REG t' = (REG t)(bin_to_reg reg := ucast val,
                         RName_PC := REG t RName_PC + 4)"
  apply (frule Fetch_correct, simp)
  apply (simp add: Decode_mov_imm_correct Next_def split: prod.splits, safe)
    apply (frule Run_mov_imm_correct, simp, safe)
    apply (frule_tac s = "x2" in ITAdvance_correct, simp add: machine_config_def)
   apply (frule Run_mov_imm_correct, simp, safe)
   apply (frule_tac s = "x2" in ITAdvance_correct, simp add: machine_config_preserved_def)
  apply (frule Run_mov_imm_correct, simp, safe)
  apply (frule_tac s = "x2" in ITAdvance_correct, simp)
  done

lemma Run_mov_reg_correct:
  "\<lbrakk>machine_config s;
    Run (Data (Register (0xd, False, rd, 0, rm, SRType_LSL, 0))) s = ((), t);
    general_purpose_reg rd;
    general_purpose_reg rm\<rbrakk> \<Longrightarrow>
      machine_config t \<and>
      machine_config_preserved s t \<and>
      REG t = (REG s)(bin_to_reg rd := REG s (bin_to_reg rm),
                      RName_PC := REG s RName_PC + 4)"
  apply (simp add: Run_def dfn'Register_def doRegister_def split: prod.splits)
  apply (frule_tac reg = "rm" in R_correct, simp)
  apply (simp add: Shift_C_def split: if_split_asm)
   apply (simp add: general_purpose_reg_def)
  apply (simp add: DataProcessing_def
                   mask_def
                   word_bits_def
                   word_extract_def
              split: if_split_asm prod.splits)
  apply (simp add: DataProcessingALU_def)
  apply (frule write'R_correct, simp, simp, clarify)
  apply (frule IncPC_correct, simp, simp, safe)
       apply (frule general_purpose_reg_correct, safe, simp+)
      apply (frule general_purpose_reg_correct, safe, simp+)
     apply (frule general_purpose_reg_correct, safe, simp+)
   apply (simp add: machine_config_preserved_def)
  done

lemma mov_reg_correct:
  "\<lbrakk>Fetch t = (mov_reg rd rm, ft);
    general_purpose_reg rd;
    general_purpose_reg rm;
    machine_config t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        machine_config t' \<and>
        machine_config_preserved t t' \<and>
        REG t' = (REG t)(bin_to_reg rd := REG t (bin_to_reg rm),
                         RName_PC := REG t RName_PC + 4)"
  apply (frule Fetch_correct, simp)
  apply (simp add: Decode_mov_reg_correct Next_def split: prod.splits, safe)
    apply (frule Run_mov_reg_correct, simp+, safe)
    apply (frule_tac s = "x2" in ITAdvance_correct)
    apply (simp add: snd_def)
   apply (frule Run_mov_reg_correct, simp+, safe)
   apply (frule_tac s = "x2" in ITAdvance_correct)
   apply (simp add: machine_config_preserved_def snd_def)
  apply (frule Run_mov_reg_correct, simp+, safe)
  apply (frule_tac s = "x2" in ITAdvance_correct)
  apply (simp add: snd_def)
  done

lemma moveq_imm_correct:
  "\<lbrakk>Fetch t = (moveq_imm reg val, ft);
    general_purpose_reg reg;
    machine_config t;
    word_extract 11 8 val = (0::4 word)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        flags_preserved t t' \<and>
        machine_config t' \<and>
        machine_config_preserved t t' \<and>
        REG t' = (REG t)(bin_to_reg reg := (if PSR.Z (CPSR t) then ucast val else REG t (bin_to_reg reg)),
                         RName_PC := REG t RName_PC + 4)"
  apply (cases "PSR.Z (CPSR t)")
   apply (frule Fetch_correct, simp)
   apply (simp add: Decode_moveq_imm_correct Next_def flags_preserved_def split: prod.splits, safe)
      apply (frule Run_mov_imm_correct, simp, safe)
      apply (frule_tac s = "x2" in ITAdvance_correct, simp add: flags_preserved_def)
     apply (frule Run_mov_imm_correct, simp, safe)
     apply (frule_tac s = "x2" in ITAdvance_correct, simp add: machine_config_def)
    apply (frule Run_mov_imm_correct, simp, safe)
    apply (frule_tac s = "x2" in ITAdvance_correct, simp add: machine_config_preserved_def)
   apply (frule Run_mov_imm_correct, simp, safe)
   apply (frule_tac s = "x2" in ITAdvance_correct, simp)
  apply (frule Fetch_correct, simp)
  apply (simp add: Decode_moveq_imm_correct Next_def flags_preserved_def split: prod.splits, safe)
      apply (frule Run_nop_correct, simp, safe)
      apply (frule_tac s = "x2" in ITAdvance_correct, simp add: flags_preserved_def)
     apply (frule Run_nop_correct, simp, safe)
     apply (frule_tac s = "x2" in ITAdvance_correct, simp add: machine_config_def)
    apply (frule Run_nop_correct, simp, safe)
    apply (frule_tac s = "x2" in ITAdvance_correct, simp add: machine_config_preserved_def)
   apply (frule Run_nop_correct, simp, safe)
   apply (frule_tac s = "x2" in ITAdvance_correct, simp)
  done

lemma movne_imm_correct:
  "\<lbrakk>Fetch t = (movne_imm reg val, ft);
    general_purpose_reg reg;
    machine_config t;
    word_extract 11 8 val = (0::4 word)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        flags_preserved t t' \<and>
        machine_config t' \<and>
        machine_config_preserved t t' \<and>
        REG t' = (REG t)(bin_to_reg reg := (if PSR.Z (CPSR t) then REG t (bin_to_reg reg) else ucast val),
                         RName_PC := REG t RName_PC + 4)"
  apply (cases "PSR.Z (CPSR t)")
   apply (frule Fetch_correct, simp)
  apply (simp add: Decode_movne_imm_correct Next_def flags_preserved_def split: prod.splits, safe)
      apply (frule Run_nop_correct, simp, safe)
      apply (frule_tac s = "x2" in ITAdvance_correct, simp add: flags_preserved_def)
     apply (frule Run_nop_correct, simp, safe)
     apply (frule_tac s = "x2" in ITAdvance_correct, simp add: machine_config_def)
    apply (frule Run_nop_correct, simp, safe)
    apply (frule_tac s = "x2" in ITAdvance_correct, simp add: machine_config_preserved_def)
   apply (frule Run_nop_correct, simp, safe)
   apply (frule_tac s = "x2" in ITAdvance_correct, simp)
  apply (frule Fetch_correct, simp)
  apply (simp add: Decode_movne_imm_correct Next_def flags_preserved_def split: prod.splits, safe)
      apply (frule Run_mov_imm_correct, simp, safe)
      apply (frule_tac s = "x2" in ITAdvance_correct, simp add: flags_preserved_def)
     apply (frule Run_mov_imm_correct, simp, safe)
     apply (frule_tac s = "x2" in ITAdvance_correct, simp add: machine_config_def)
    apply (frule Run_mov_imm_correct, simp, safe)
    apply (frule_tac s = "x2" in ITAdvance_correct, simp add: machine_config_preserved_def)
   apply (frule Run_mov_imm_correct, simp, safe)
   apply (frule_tac s = "x2" in ITAdvance_correct, simp)
  done

lemma Run_neg_correct:
  "\<lbrakk>Run (Data (ArithLogicImmediate (3, False, rd, rm, 0))) s = ((), t);
    general_purpose_reg rd;
    general_purpose_reg rm;
    machine_config s\<rbrakk> \<Longrightarrow>
      machine_config t \<and>
      machine_config_preserved s t \<and>
      REG t = (REG s)(bin_to_reg rd := -(REG s (bin_to_reg rm)), RName_PC := REG s RName_PC + 4)"
  apply (simp add: Run_def dfn'ArithLogicImmediate_def split: if_split_asm prod.splits)
   apply (simp add: general_purpose_reg_def)
  apply (frule ExpandImm_C_correct, simp)
   apply (simp add: word_bits_def word_extract_def)
  apply (simp add: DataProcessing_def
                   DataProcessingALU_def
                   mask_def
                   word_bits_def
                   word_extract_def
              split: prod.splits)
  apply (frule_tac reg = "rm" in R_correct, simp)
  apply (frule write'R_correct, simp, safe)
    apply (frule IncPC_correct, simp, simp, safe)
     apply (simp add: machine_config_def)
    apply (simp add: machine_config_def)
   apply (frule IncPC_correct, simp, simp, safe)
    apply (frule general_purpose_reg_correct, simp+)
   apply (simp add: machine_config_preserved_def)
  apply (frule IncPC_correct, simp, simp, safe)
   apply (frule general_purpose_reg_correct, simp+)
  apply (simp add: AddWithCarry_def Let_def wi_hom_syms, clarify)
  sorry

lemma neg_correct:
  "\<lbrakk>Fetch t = (neg rd rm, ft);
    general_purpose_reg rd;
    general_purpose_reg rm;
    machine_config t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        machine_config t' \<and>
        machine_config_preserved t t' \<and>
        REG t' = (REG t)(bin_to_reg rd := -(REG t (bin_to_reg rm)), RName_PC := REG t RName_PC + 4)"
  apply (frule Fetch_correct, simp)
  apply (simp add: Decode_neg_correct Next_def split: prod.splits, safe)
    apply (frule Run_neg_correct, simp, safe)
    apply (frule_tac s = "x2" in ITAdvance_correct, simp add: machine_config_def)
   apply (frule Run_neg_correct, simp, safe)
   apply (frule_tac s = "x2" in ITAdvance_correct, simp add: machine_config_preserved_def)
  apply (frule Run_neg_correct, simp, safe)
  apply (frule_tac s = "x2" in ITAdvance_correct, simp)
  done

lemma Run_or_reg_correct:
  "\<lbrakk>machine_config s;
    Run (Data (Register (0xc, False, rd, rn, rm, SRType_LSL, 0))) s = ((), t);
    general_purpose_reg rd;
    general_purpose_reg rn;
    general_purpose_reg rm\<rbrakk> \<Longrightarrow>
      machine_config t \<and>
      machine_config_preserved s t \<and>
      REG t = (REG s)(bin_to_reg rd := REG s (bin_to_reg rn) || REG s (bin_to_reg rm),
                      RName_PC := REG s RName_PC + 4)"
  apply (simp add: Run_def dfn'Register_def doRegister_def split: prod.splits)
  apply (frule_tac reg = "rm" in R_correct, simp)
  apply (simp add: Shift_C_def split: if_split_asm)
   apply (simp add: general_purpose_reg_def)
  apply (simp add: DataProcessing_def
                   mask_def
                   word_bits_def
                   word_extract_def
              split: if_split_asm prod.splits)
  apply (frule_tac reg = "rn" in R_correct, simp)
  apply (simp add: DataProcessingALU_def)
  apply (frule write'R_correct, simp, simp, clarify)
  apply (frule IncPC_correct, simp, simp, safe)
       apply (frule general_purpose_reg_correct, safe, simp+)
      apply (frule general_purpose_reg_correct, safe, simp+)
     apply (frule general_purpose_reg_correct, safe, simp+)
   apply (simp add: machine_config_preserved_def)
  done

lemma or_reg_correct:
  "\<lbrakk>Fetch t = (or_reg rd rn rm, ft);
    general_purpose_reg rd;
    general_purpose_reg rn;
    general_purpose_reg rm;
    machine_config t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        machine_config t' \<and>
        machine_config_preserved t t' \<and>
        REG t' = (REG t)(bin_to_reg rd := REG t (bin_to_reg rn) || REG t (bin_to_reg rm),
                         RName_PC := REG t RName_PC + 4)"
  apply (frule Fetch_correct, simp)
  apply (simp add: Decode_or_reg_correct Next_def split: prod.splits, safe)
    apply (frule Run_or_reg_correct, simp+, safe)
    apply (frule_tac s = "x2" in ITAdvance_correct)
    apply (simp add: snd_def)
   apply (frule Run_or_reg_correct, simp+, safe)
   apply (frule_tac s = "x2" in ITAdvance_correct)
   apply (simp add: machine_config_preserved_def snd_def)
  apply (frule Run_or_reg_correct, simp+, safe)
  apply (frule_tac s = "x2" in ITAdvance_correct)
  apply (simp add: snd_def)
  done

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

lemma Run_sub_reg_correct:
  "\<lbrakk>machine_config s;
    Run (Data (Register (2, False, rd, rn, rm, SRType_LSL, 0))) s = ((), t);
    general_purpose_reg rd;
    general_purpose_reg rn;
    general_purpose_reg rm\<rbrakk> \<Longrightarrow>
      machine_config t \<and>
      machine_config_preserved s t \<and>
      REG t = (REG s)(bin_to_reg rd := REG s (bin_to_reg rn) - REG s (bin_to_reg rm),
                      RName_PC := REG s RName_PC + 4)"
  apply (simp add: Run_def dfn'Register_def doRegister_def split: prod.splits)
  apply (frule_tac reg = "rm" in R_correct, simp)
  apply (simp add: Shift_C_def split: if_split_asm)
   apply (simp add: general_purpose_reg_def)
  apply (simp add: DataProcessing_def
                   mask_def
                   word_bits_def
                   word_extract_def
              split: if_split_asm prod.splits)
   apply (simp add: general_purpose_reg_def)
  apply (frule_tac reg = "rn" in R_correct, simp)
  apply (simp add: DataProcessingALU_def, clarify)
  apply (frule write'R_correct, simp, simp, simp, safe)
    apply (frule IncPC_correct, simp, safe)
   apply (frule IncPC_correct, simp, safe)
   apply (simp add: machine_config_def machine_config_preserved_def)
  apply (simp add: AddWithCarry_def Let_def wi_hom_syms, safe)
  apply (frule IncPC_correct, simp, simp, safe)
  apply (frule general_purpose_reg_correct, simp)
  sorry

lemma sub_reg_correct:
  "\<lbrakk>Fetch t = (sub_reg rd rn rm, ft);
    general_purpose_reg rd;
    general_purpose_reg rn;
    general_purpose_reg rm;
    machine_config t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        machine_config t' \<and>
        machine_config_preserved t t' \<and>
        REG t' = (REG t)(bin_to_reg rd := REG t (bin_to_reg rn) - REG t (bin_to_reg rm),
                         RName_PC := REG t RName_PC + 4)"
  apply (frule Fetch_correct, simp)
  apply (simp add: Decode_sub_reg_correct Next_def split: prod.splits, safe)
    apply (frule Run_sub_reg_correct, simp+, safe)
    apply (frule_tac s = "x2" in ITAdvance_correct)
    apply (simp add: snd_def)
   apply (frule Run_sub_reg_correct, simp+, safe)
   apply (frule_tac s = "x2" in ITAdvance_correct)
   apply (simp add: machine_config_preserved_def snd_def)
  apply (frule Run_sub_reg_correct, simp+, safe)
  apply (frule_tac s = "x2" in ITAdvance_correct)
  apply (simp add: snd_def)
  done

lemma comp_aexp_mov_small_correct:
  "\<lbrakk>Fetch t = (mov_imm reg (ucast val), ft);
    general_purpose_reg reg;
    machine_config t;
    state_rel s t;
    word_extract 31 8 val = (0::24 word)\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        machine_config t' \<and>
        state_rel s t' \<and>
        REG t' = (REG t)(bin_to_reg reg := val, RName_PC := REG t RName_PC + 4)"
  apply (frule mov_imm_correct, simp, simp)
   apply (simp add: mask_def word_bits_def word_extract_def)
     apply (word_bitwise, simp, safe)
  apply (subgoal_tac "UCAST(12 \<rightarrow> 32) (UCAST(32 \<rightarrow> 12) val) = val", simp)
   apply (frule state_rel_preserved, simp, simp)
  apply (simp add: mask_def word_bits_def word_extract_def)
  apply (word_bitwise, simp)
  done

lemma comp_aexp_mov_large_correct:
  "\<lbrakk>state_rel s t;
    machine_config t;
    general_purpose_reg reg;
    code_installed t [b_imm 0, ARM val, ldr_lit 0 reg 0xC]\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 2 = t' \<and>
        state_rel s t' \<and>
        machine_config t' \<and>
        REG t' = (REG t)(bin_to_reg reg := val, RName_PC := REG t RName_PC + 12)"
  sorry

lemma comp_aexp_mov_correct:
  "\<lbrakk>code_installed t (comp_aexp_mov reg val);
    general_purpose_reg reg;
    machine_config t;
    state_rel s t\<rbrakk> \<Longrightarrow>
      \<exists>k t'. steps t k = t' \<and>
        machine_config t' \<and>
        state_rel s t' \<and>
        REG t' = (REG t)(bin_to_reg reg := val,
                         RName_PC := REG t RName_PC + 4 * (word_of_int (int (length (comp_aexp_mov reg val)))))"
  apply (simp add: comp_aexp_mov_def split: if_split_asm prod.splits, safe)
   apply (frule comp_aexp_mov_small_correct, simp+)
   apply (rule_tac x = "1" in exI, simp)
  apply (frule comp_aexp_mov_large_correct, force+)
  done

lemma comp_aexp_Const_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some val;
    code_installed t (comp_aexp e);
    machine_config t;
    state_rel s t;
    e = Const val\<rbrakk> \<Longrightarrow>
      \<exists>k t'. steps t k = t' \<and>
        machine_config t' \<and>
        state_rel s t' \<and>
        REG t' = (REG t)(RName_0usr := val,
                         RName_PC := REG t RName_PC + 4 * (word_of_int (int (length (comp_aexp e)))))"
  apply (simp)
  apply (frule comp_aexp_mov_correct)
   apply (simp add: general_purpose_reg_def, simp, simp, safe)
  apply (rule_tac x = "k" in exI, simp)
  apply (simp add: bin_to_reg_def)
  done

lemma comp_aexp_UnOp_Neg_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some y;
    code_installed t c;
    state_rel s t;
    c = comp_aexp e;
    e = UnOp Neg x;
    machine_config t\<rbrakk> \<Longrightarrow>
      \<exists>k t'. steps t k = t' \<and>
        machine_config t' \<and>
        state_rel s t' \<and>
        REG t' = (REG t)(RName_0usr := y,
                         RName_PC := REG t RName_PC + 4 * (word_of_int (int (length c))))"
  apply simp
  apply (frule code_installed_append)
  apply (frule comp_aexp_mov_correct)
   apply (simp add: general_purpose_reg_def, simp, simp, safe)
  apply (frule_tac k = "k" in code_installed_prepend, simp, simp split: prod.splits)
  apply (frule_tac rd = "0" and rm = "0" in neg_correct)
     apply (simp add: general_purpose_reg_def)
    apply (simp add: general_purpose_reg_def, simp)
  apply (rule_tac x = "k+1" in exI)
  apply (simp add: comp_aexp_mov_def bin_to_reg_def state_rel_preserved steps_inc, force)
  done

lemma comp_aexp_UnOp_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some y;
    c = comp_aexp e;
    code_installed t c;
    state_rel s t;
    e = UnOp op x;
    machine_config t\<rbrakk> \<Longrightarrow>
    \<exists>k t'. steps t k = t' \<and>
      machine_config t' \<and>
      state_rel s t' \<and>
      REG t' = (REG t)(RName_0usr := y,
                       RName_PC := REG t RName_PC + 4 * (word_of_int (int (length c))))"
  apply (cases op)
  apply (frule comp_aexp_UnOp_Neg_correct, simp+)
  done

lemma comp_aexp_BinOp_Plus_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some z;
    code_installed t c;
    state_rel s t;
    c = comp_aexp e;
    e = BinOp op x y;
    op = Plus;
    machine_config t\<rbrakk> \<Longrightarrow>
    \<exists>k t'. steps t k = t' \<and>
      machine_config t' \<and>
      state_rel s t' \<and>
      REG t' = (REG t)(RName_0usr := z,
                       RName_1usr := y,
                       RName_PC := REG t RName_PC + 4 * (word_of_int (int (length c))))"
  apply simp
  apply (frule code_installed_append)
  apply (drule comp_aexp_mov_correct)
   apply (simp add: general_purpose_reg_def, simp, simp, safe)
  apply (drule_tac k = "k" in code_installed_prepend, simp)
  apply (frule code_installed_append)
  apply (frule_tac reg = "1" in comp_aexp_mov_correct)
   apply (simp add: general_purpose_reg_def, simp, simp, safe)
  apply (drule_tac k = "ka" in code_installed_prepend, simp, simp split: prod.splits)
  apply (frule_tac t = "steps (steps t k) ka" in add_reg_correct)
      apply (simp add: general_purpose_reg_def)
     apply (simp add: general_purpose_reg_def)
    apply (simp add: general_purpose_reg_def)
   apply (simp add: machine_config_def)
  apply (rule_tac x = "k+ka+1" in exI, safe)
    apply (simp add: steps_inc steps_add)
   apply (simp add: state_rel_preserved steps_inc steps_add)
  apply (simp add: bin_to_reg_def
                   comp_aexp_mov_def
                   mask_def
                   steps_add
                   steps_inc
                   word_bits_def
                   word_extract_def, force)
  done

lemma comp_aexp_BinOp_Minus_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some z;
    code_installed t c;
    state_rel s t;
    c = comp_aexp e;
    e = BinOp op x y;
    op = Minus;
    machine_config t\<rbrakk> \<Longrightarrow>
    \<exists>k t'. steps t k = t' \<and>
      machine_config t' \<and>
      state_rel s t' \<and>
      REG t' = (REG t)(RName_0usr := z,
                       RName_1usr := y,
                       RName_PC := REG t RName_PC + 4 * (word_of_int (int (length c))))"
  apply simp
  apply (frule code_installed_append)
  apply (drule comp_aexp_mov_correct)
   apply (simp add: general_purpose_reg_def, simp, simp, safe)
  apply (drule_tac k = "k" in code_installed_prepend, simp)
  apply (frule code_installed_append)
  apply (frule_tac reg = "1" in comp_aexp_mov_correct)
   apply (simp add: general_purpose_reg_def, simp, simp, safe)
  apply (drule_tac k = "ka" in code_installed_prepend, simp, simp split: prod.splits)
  apply (frule_tac t = "steps (steps t k) ka" in sub_reg_correct)
      apply (simp add: general_purpose_reg_def)
     apply (simp add: general_purpose_reg_def)
    apply (simp add: general_purpose_reg_def)
   apply (simp add: machine_config_def)
  apply (rule_tac x = "k+ka+1" in exI, safe)
    apply (simp add: steps_inc steps_add)
   apply (simp add: state_rel_preserved steps_inc steps_add)
  apply (simp add: bin_to_reg_def
                   comp_aexp_mov_def
                   mask_def
                   steps_add
                   steps_inc
                   word_bits_def
                   word_extract_def, force)
  done

lemma comp_aexp_BinOp_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some z;
    code_installed t c;
    state_rel s t;
    c = comp_aexp e;
    e = BinOp op x y;
    machine_config t\<rbrakk> \<Longrightarrow>
    \<exists>k t'. steps t k = t' \<and>
      machine_config t' \<and>
      state_rel s t' \<and>
      REG t' = (REG t)(RName_0usr := z,
                       RName_1usr := y,
                       RName_PC := REG t RName_PC + 4 * (word_of_int (int (length c))))"
  apply (cases op)
   apply (frule comp_aexp_BinOp_Plus_correct, force+)
  apply (frule comp_aexp_BinOp_Minus_correct, force+)
  done

lemma comp_aexp_HeapLookup_correct:
  "\<lbrakk>\<lbrakk>e\<rbrakk> s = Some val;
    code_installed t c;
    machine_config t;
    state_rel s t;
    c = comp_aexp e;
    e = HeapLookup x4\<rbrakk> \<Longrightarrow>
    \<exists>k t'. steps t k = t' \<and>
      state_rel s t' \<and>
      machine_config t' \<and>
      REG t' = (REG t)(RName_0usr := val,
                       RName_PC := REG t RName_PC + 4 * (word_of_int (int (length c))))"
  apply simp
  apply (frule code_installed_append)
  apply (frule comp_aexp_mov_correct)
     apply (simp add: general_purpose_reg_def, simp, simp, safe)
  apply (frule_tac k = "k" in code_installed_prepend, simp, simp split: prod.splits, clarify)
   apply (frule_tac t = "steps t k" and val = "val" in ldr_imm_correct, simp)
       apply (simp add: general_purpose_reg_def)
      apply (simp add: general_purpose_reg_def, simp, simp split: if_split_asm, safe)
    apply (simp add: bin_to_reg_def)
  defer
   apply (rule_tac x = "k+1" in exI, safe)
    apply (simp add: state_rel_preserved steps_add steps_inc)
   apply (simp add: add.commute bin_to_reg_def comp_aexp_mov_def steps_add steps_inc)
  sorry

lemma comp_aexp_correct:
  "\<lbrakk>aval e s = Some val;
    code_installed t (comp_aexp e);
    machine_config t;
    state_rel s t\<rbrakk> \<Longrightarrow>
      \<exists>k t'. steps t k = t' \<and>
        machine_config t' \<and>
        state_rel s t' \<and>
        REG t' = (REG t)(RName_0usr := val,
                         RName_1usr := (REG t') RName_1usr,
                         RName_PC := REG t RName_PC + 4 * (word_of_int (int (length (comp_aexp e)))))"
  apply (cases e)
     apply (frule comp_aexp_Const_correct, force+)
    apply (frule comp_aexp_UnOp_correct, force+)
   apply (frule comp_aexp_BinOp_correct, force+)
  apply (frule comp_aexp_HeapLookup_correct, force+)
  done

lemma comp_bexp_mov_correct:
  "\<lbrakk>code_installed t (comp_bexp_mov reg val);
    general_purpose_reg reg;
    machine_config t;
    state_rel s t\<rbrakk> \<Longrightarrow>
      \<exists>t'. steps t 1 = t' \<and>
        machine_config t' \<and>
        state_rel s t' \<and>
        REG t' = (REG t)(bin_to_reg reg := (if val then 1 else 0),
                         RName_PC := REG t RName_PC + 4 * (word_of_int (int (length (comp_bexp_mov reg val)))))"
  apply (simp add: comp_bexp_mov_def split: prod.splits)
  apply (frule mov_imm_correct, simp, simp)
   apply (simp add: word_bits_def word_extract_def, safe)
       apply (simp add: state_rel_preserved)+
  done

lemma comp_bexp_BConst_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val;
    code_installed t c;
    machine_config t;
    state_rel s t;
    b = BConst x;
    c = comp_bexp b\<rbrakk> \<Longrightarrow>
    \<exists>k t'. steps t k = t' \<and>
      machine_config t' \<and>
      state_rel s t' \<and>
      REG t' = (REG t)(RName_0usr := (if val then 1 else 0),
                       RName_PC := REG t RName_PC + 4 * (word_of_int (int (length c))))"
  apply simp
  apply (frule comp_bexp_mov_correct)
     apply (simp add: general_purpose_reg_def, simp, simp)
  apply (cases val, simp)
   apply (rule_tac x = "1" in exI, simp)
   apply (simp add: bin_to_reg_def, simp)
  apply (rule_tac x = "1" in exI, simp)
  apply (simp add: bin_to_reg_def)
  done

lemma comp_bexp_BComp_Less_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val;
    code_installed t c;
    machine_config t;
    state_rel s t;
    b = BComp Less a1 a2;
    c = comp_bexp b\<rbrakk> \<Longrightarrow>
    \<exists>k t'. steps t k = t' \<and>
      machine_config t' \<and>
      state_rel s t' \<and>
      REG t' = (REG t)(RName_0usr := (if val then 1 else 0),
                       RName_1usr := REG t' RName_1usr,
                       RName_PC := REG t RName_PC + 4 * (word_of_int (int (length c))))"
  sorry

lemma comp_bexp_BComp_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val;
    code_installed t c;
    machine_config t;
    state_rel s t;
    b = BComp op a1 a2;
    c = comp_bexp b\<rbrakk> \<Longrightarrow>
    \<exists>k t'. steps t k = t' \<and>
      machine_config t' \<and>
      state_rel s t' \<and>
      REG t' = (REG t)(RName_0usr := (if val then 1 else 0),
                       RName_1usr := REG t' RName_1usr,
                       RName_PC := REG t RName_PC + 4 * (word_of_int (int (length c))))"
  apply (cases op)
  apply (rule_tac b = "b" in comp_bexp_BComp_Less_correct, simp+)
  done

lemma comp_bexp_BBinOp_And_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some z;
    code_installed t c;
    machine_config t;
    state_rel s t;
    b = BBinOp op x y;
    c = comp_bexp b;
    op = And\<rbrakk> \<Longrightarrow>
    \<exists>k t'. steps t k = t' \<and>
      machine_config t' \<and>
      state_rel s t' \<and>
      REG t' = (REG t)(RName_0usr := (if z then 1 else 0),
                       RName_1usr := REG t' RName_1usr,
                       RName_PC := REG t RName_PC + 4 * (word_of_int (int (length c))))"
  apply simp
  apply (frule code_installed_append)
  apply (frule comp_bexp_mov_correct)
     apply (simp add: general_purpose_reg_def, simp, simp)
  apply (thin_tac "code_installed t (comp_bexp_mov 0 x)")
  apply (frule_tac k = "1" in code_installed_prepend, simp)
  apply (thin_tac "code_installed t (comp_bexp_mov 0 x @ comp_bexp_mov 1 y @ [and_reg 0 0 1])")
  apply (frule code_installed_append)
  apply (frule_tac s = "s" in comp_bexp_mov_correct)
     apply (simp add: general_purpose_reg_def, simp)
   apply (simp add: steps_add steps_inc)
  apply (frule_tac k = "1" in code_installed_prepend)
  apply (simp add: steps_add steps_inc, simp split: prod.splits)
  apply (frule and_reg_correct)
      apply (simp add: general_purpose_reg_def)
     apply (simp add: general_purpose_reg_def)
    apply (simp add: general_purpose_reg_def, simp)
  apply (cases z)
   apply (simp add: bin_to_reg_def)
   apply (rule_tac x = "3" in exI)
   apply (simp add: add.commute
                    comp_bexp_mov_def
                    eval_nat_numeral
                    state_rel_preserved
                    steps_add
                    steps_one
               del: steps.simps, force)
  apply (simp add: bin_to_reg_def)
  apply (rule_tac x = "3" in exI)
  apply (simp add: add.commute
                   comp_bexp_mov_def
                   eval_nat_numeral
                   state_rel_preserved
                   steps_add
                   steps_one
              del: steps.simps, force)
  done

lemma comp_bexp_BBinOp_Or_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some z;
    code_installed t c;
    machine_config t;
    state_rel s t;
    b = BBinOp op x y;
    c = comp_bexp b;
    op = Or\<rbrakk> \<Longrightarrow>
    \<exists>k t'. steps t k = t' \<and>
      machine_config t' \<and>
      state_rel s t' \<and>
      REG t' = (REG t)(RName_0usr := (if z then 1 else 0),
                       RName_1usr := REG t' RName_1usr,
                       RName_PC := REG t RName_PC + 4 * (word_of_int (int (length c))))"
  apply simp
  apply (frule code_installed_append)
  apply (frule comp_bexp_mov_correct)
     apply (simp add: general_purpose_reg_def, simp, simp)
  apply (thin_tac "code_installed t (comp_bexp_mov 0 x)")
  apply (frule_tac k = "1" in code_installed_prepend, simp)
  apply (thin_tac "code_installed t (comp_bexp_mov 0 x @ comp_bexp_mov 1 y @ [or_reg 0 0 1])")
  apply (frule code_installed_append)
  apply (frule_tac s = "s" in comp_bexp_mov_correct)
     apply (simp add: general_purpose_reg_def, simp)
   apply (simp add: steps_add steps_inc)
  apply (frule_tac k = "1" in code_installed_prepend)
  apply (simp add: steps_add steps_inc, simp split: prod.splits)
  apply (frule or_reg_correct)
      apply (simp add: general_purpose_reg_def)
     apply (simp add: general_purpose_reg_def)
    apply (simp add: general_purpose_reg_def, simp)
  apply (cases z)
   apply (simp add: bin_to_reg_def)
   apply (rule_tac x = "3" in exI)
   apply (simp add: add.commute
                    comp_bexp_mov_def
                    eval_nat_numeral
                    state_rel_preserved
                    steps_add
                    steps_one
               del: steps.simps, force)
  apply (simp add: bin_to_reg_def)
  apply (rule_tac x = "3" in exI)
  apply (simp add: add.commute
                   comp_bexp_mov_def
                   eval_nat_numeral
                   state_rel_preserved
                   steps_add
                   steps_one
              del: steps.simps, force)
  done

lemma comp_bexp_BBinOp_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some z;
    code_installed t c;
    machine_config t;
    state_rel s t;
    b = BBinOp op x y;
    c = comp_bexp b\<rbrakk> \<Longrightarrow>
    \<exists>k t'. steps t k = t' \<and>
      machine_config t' \<and>
      state_rel s t' \<and>
      REG t' = (REG t)(RName_0usr := (if z then 1 else 0),
                       RName_1usr := REG t' RName_1usr,
                       RName_PC := REG t RName_PC + 4 * (word_of_int (int (length c))))"
  apply (cases op)
   apply (frule comp_bexp_BBinOp_And_correct, force+)
  apply (frule comp_bexp_BBinOp_Or_correct, force+)
  done

lemma comp_bexp_BUnOp_Not_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val;
    code_installed t c;
    machine_config t;
    state_rel s t;
    b = BUnOp op a;
    c = comp_bexp b;
    op = bunop.Not\<rbrakk> \<Longrightarrow>
    \<exists>k t'. steps t k = t' \<and>
      machine_config t' \<and>
      state_rel s t' \<and>
      REG t' = (REG t)(RName_0usr := (if val then 1 else 0),
                       RName_PC := REG t RName_PC + 4 * (word_of_int (int (length c))))"
  apply simp
  apply (frule code_installed_append)
  apply (frule comp_bexp_mov_correct)
     apply (simp add: general_purpose_reg_def, simp, simp, simp del: steps.simps)
  apply (drule_tac k = "1" in code_installed_prepend, simp)
  apply (frule hello)
  apply (frule_tac val = "a" in cmp_imm_correct)
     apply (simp add: bin_to_reg_def)
    apply (simp add: general_purpose_reg_def)
   apply (simp add: eval_nat_numeral, simp del: steps.simps)
  apply (drule_tac k = "1" in code_installed_prepend1, simp)
  apply (subgoal_tac "state_rel s (steps t (Suc 0))")
   apply (subgoal_tac "machine_state_preserved (steps t (Suc 0)) (steps (steps t (Suc 0)) (Suc 0))")
    apply (frule_tac t = "steps t (Suc 0)" and
                     t' = "steps (steps t (Suc 0)) (Suc 0)" in state_rel_preserved, simp)
    apply (frule hello)
    apply (frule moveq_imm_correct)
       apply (simp add: general_purpose_reg_def, simp)
     apply (simp add: word_bits_def word_extract_def)
    apply (drule_tac k = "1" in code_installed_prepend1, simp)
    apply (subgoal_tac "state_rel s (steps (steps t (Suc 0)) (Suc 0))")
     apply (subgoal_tac "machine_state_preserved (steps (steps t (Suc 0)) (Suc 0)) (steps (steps (steps t (Suc 0)) (Suc 0)) (Suc 0))")
      apply (frule_tac t = "steps (steps t (Suc 0)) (Suc 0)" and
                       t' = "steps (steps (steps t (Suc 0)) (Suc 0)) (Suc 0)" in state_rel_preserved, simp)
      apply (frule hello)
      apply (frule movne_imm_correct)
         apply (simp add: general_purpose_reg_def, simp)
       apply (simp add: word_bits_def word_extract_def, simp del: steps.simps, safe)
     apply (rule_tac x = "4" in exI, safe)
       apply (simp add: eval_nat_numeral)
      apply (frule_tac t = "steps (steps (steps t (Suc 0)) (Suc 0)) (Suc 0)" and
                       t' = "steps (steps (steps (steps t (Suc 0)) (Suc 0)) (Suc 0)) (Suc 0)" in state_rel_preserved, simp)
      apply (simp add: eval_nat_numeral)
     apply (simp add: bin_to_reg_def comp_bexp_mov_def eval_nat_numeral flags_preserved_def, force)
    apply (rule_tac x = "4" in allE, simp)
    apply (frule_tac t = "steps (steps (steps t (Suc 0)) (Suc 0)) (Suc 0)" and
                     t' = "steps (steps (steps (steps t (Suc 0)) (Suc 0)) (Suc 0)) (Suc 0)" in state_rel_preserved, simp)
    apply (simp add: bin_to_reg_def comp_bexp_mov_def eval_nat_numeral flags_preserved_def, force)
   apply (simp add: eval_nat_numeral, simp)
  done

lemma comp_bexp_BUnOp_correct:
  "\<lbrakk>\<lbrakk>b\<rbrakk>\<^sub>b s = Some val;
    code_installed t c;
    machine_config t;
    state_rel s t;
    b = BUnOp op a;
    c = comp_bexp b\<rbrakk> \<Longrightarrow>
    \<exists>k t'. steps t k = t' \<and>
      machine_config t' \<and>
      state_rel s t' \<and>
      REG t' = (REG t)(RName_0usr := (if val then 1 else 0),
                       RName_PC := REG t RName_PC + 4 * (word_of_int (int (length c))))"
  apply (cases op)
  apply (frule comp_bexp_BUnOp_Not_correct, simp+)
  done

lemma comp_bexp_correct:
  "\<lbrakk>bval e s = Some val;
    code_installed t c;
    machine_config t;
    state_rel s t;
    c = comp_bexp e\<rbrakk> \<Longrightarrow>
      \<exists>k t'. steps t k = t' \<and>
        machine_config t' \<and>
        state_rel s t' \<and>
        REG t' = (REG t)(RName_0usr := (if val then 1 else 0),
                         RName_1usr := REG t' RName_1usr,
                         RName_PC := REG t RName_PC + 4 * (word_of_int (int (length c))))"
  apply (cases e)
     apply (frule comp_bexp_BConst_correct, force+)
    apply (frule comp_bexp_BComp_correct, force+)
   apply (frule comp_bexp_BBinOp_correct, force+)
  apply (frule comp_bexp_BUnOp_correct, force+)
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
