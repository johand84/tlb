theory ARMv7_Mem_Write_Read_Ref

imports  ARMv7_Address_Translate_Ref

begin               




instantiation tlb_state_ext :: (type) mem_op 
begin

definition   
  "(mmu_read  :: (vaddr  \<Rightarrow>  'a tlb_state_scheme \<Rightarrow> bool list \<times>  'a tlb_state_scheme))
   \<equiv>  \<lambda>va. do {
                     pa  \<leftarrow> mmu_translate va;
                     mem1 pa
  }"

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a tlb_state_scheme \<Rightarrow> bool list \<times>  'a tlb_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va;
                     mem_read1 (pa , size)
  }"

thm  mmu_read_size_tlb_state_ext_def

definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a tlb_state_scheme \<Rightarrow> unit \<times> 'a tlb_state_scheme))
   \<equiv> \<lambda>(value, vaddr, size). do {
     paddr <- mmu_translate vaddr;
     exception <- read_state exception;
     if exception = NoException 
       then  write'mem1 (value, paddr, size)
       else return ()
  }"
(* print_context *)                      
  instance ..
end

thm  mmu_write_size_tlb_state_ext_def

instantiation tlb_det_state_ext :: (type) mem_op   
begin


definition   
  "(mmu_read  :: (vaddr  \<Rightarrow>  'a tlb_det_state_scheme \<Rightarrow> bool list \<times>  'a tlb_det_state_scheme))
   \<equiv>  \<lambda>va. do {
                     pa  \<leftarrow> mmu_translate va;
                     mem1 pa
  }"

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a tlb_det_state_scheme \<Rightarrow> bool list \<times>  'a tlb_det_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va;
                     mem_read1 (pa , size)
  }"

definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a tlb_det_state_scheme \<Rightarrow> unit \<times> 'a tlb_det_state_scheme))
   \<equiv> \<lambda>(value, vaddr, size). do {
     paddr <- mmu_translate vaddr;
     exception <- read_state exception;
     if exception = NoException 
       then  write'mem1 (value, paddr, size)
       else return ()
  }"
  instance ..
end




instantiation tlb_sat_state_ext :: (type) mem_op    
begin

definition   
  "(mmu_read  :: (vaddr  \<Rightarrow>  'a tlb_sat_state_scheme \<Rightarrow> bool list \<times>  'a tlb_sat_state_scheme))
   \<equiv>  \<lambda>va. do {
                     pa  \<leftarrow> mmu_translate va;
                     mem1 pa
  }"

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a tlb_sat_state_scheme \<Rightarrow> bool list \<times>  'a tlb_sat_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va;
                     mem_read1 (pa , size)
  }"

definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a tlb_sat_state_scheme \<Rightarrow> unit \<times> 'a tlb_sat_state_scheme))
   \<equiv> \<lambda>(value, vaddr, size).  do {
     ttbr0 <- read_state TTBR0;
     asid <- read_state ASID;
     pa <- mmu_translate vaddr;
     tlb0  <- read_state tlb_sat_set;
     exception <- read_state exception;
     if exception = NoException 
      then do { 
           write'mem1 (value, pa, size); 
           mem1  <- read_state MEM;
           let all_non_fault_entries = the ` {e\<in>pt_walk asid mem1 ttbr0 ` UNIV. \<not>is_fault e};
           let tlb = tlb0 \<union> all_non_fault_entries;  (* what about inconsistency here ? *)
           update_state (\<lambda>s. s\<lparr> tlb_sat_set := tlb \<rparr>)
          } 
      else return () 
    }"
instance ..
end


definition
  ptable_comp :: "asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> paddr \<Rightarrow> (asid \<times> vaddr) set"
where
  "ptable_comp a hp1 hp2 rt1 rt2 \<equiv>
         (\<lambda>x. (a, x)) ` {va. (\<exists>e1 e2. pt_walk a hp1 rt1 va = e1 \<and> pt_walk a hp2 rt2 va = e2  \<and> \<not>is_fault e1 \<and> \<not>is_fault e2 \<and> e1 \<noteq> e2 )  \<or>
                (\<exists>e1 e2. pt_walk a hp1 rt1 va = e1 \<and> pt_walk a hp2 rt2 va = e2  \<and> \<not>is_fault e1 \<and> is_fault e2 )}"



definition
  ptable_comp' :: "asid \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> paddr \<Rightarrow> paddr \<Rightarrow> vaddr set"
where
  "ptable_comp' a hp1 hp2 rt1 rt2 \<equiv>
               {va. (\<exists>e1 e2. pt_walk a hp1 rt1 va = e1 \<and> pt_walk a hp2 rt2 va = e2  \<and> \<not>is_fault e1 \<and> \<not>is_fault e2 \<and> e1 \<noteq> e2 )  \<or>
                   (\<exists>e1 e2. pt_walk a hp1 rt1 va = e1 \<and> pt_walk a hp2 rt2 va = e2  \<and> \<not>is_fault e1 \<and> is_fault e2 )}"



instantiation tlb_incon_state_ext :: (type) mem_op    
begin

definition   
  "(mmu_read  :: (vaddr  \<Rightarrow>  'a tlb_incon_state_scheme \<Rightarrow> bool list \<times>  'a tlb_incon_state_scheme))
   \<equiv>  \<lambda>va. do {
                     pa  \<leftarrow> mmu_translate va;
                     mem1 pa
  }"

definition
 "(mmu_read_size  :: (vaddr \<times> nat \<Rightarrow>  'a tlb_incon_state_scheme \<Rightarrow> bool list \<times>  'a tlb_incon_state_scheme))
  \<equiv> \<lambda>(va,size). do {
                     pa  \<leftarrow> mmu_translate va;
                     mem_read1 (pa , size)
  }"


definition   
  "(mmu_write_size  :: (bool list \<times> vaddr \<times> nat \<Rightarrow> 'a tlb_incon_state_scheme \<Rightarrow> unit \<times> 'a tlb_incon_state_scheme))
  \<equiv> \<lambda>(value, vaddr, size). do {
      ttbr0 <- read_state TTBR0;
      asid  <- read_state ASID;
      mem   <- read_state MEM; 
      paddr <- mmu_translate vaddr;
      tlb_incon_set <- read_state tlb_incon_set; 
      exception <- read_state exception;
      if exception = NoException 
        then  do {
                   write'mem1 (value, paddr, size);
                   mem' <- read_state MEM;
                   let ptable_asid_va = ptable_comp' asid mem mem' ttbr0 ttbr0;
                   let incon_set_n = iset tlb_incon_set \<union>  ptable_asid_va;
                   let tlb_incon_set = tlb_incon_set \<lparr>iset := incon_set_n \<rparr>;
                   update_state (\<lambda>s. s\<lparr> tlb_incon_set :=  tlb_incon_set \<rparr>)
            }
        else return ()
   }"
  instance ..
end


lemma mem1_exception:
  "mem1 p b = (val, r) \<Longrightarrow>  r = b\<lparr>exception := exception r\<rparr>"
  apply (clarsimp simp: mem1_def)
  apply (cases "MEM b p")
   apply (clarsimp simp: raise'exception_def split: if_split_asm)
  apply clarsimp
done


lemma mem1_read_exception:
  "mem_read1 (a, sz) b = (val, r) \<Longrightarrow> r = b \<lparr>exception := exception r\<rparr>"
  apply (clarsimp simp: mem_read1_def)
  apply (clarsimp split: if_split_asm)
      apply (case_tac "mem1 (a r+ 0) b" , clarsimp)
      apply (clarsimp simp: mem1_exception)
     apply (case_tac "mem1 (a r+ 1) b" , clarsimp)
     apply (case_tac "mem1 (a r+ 0) ba", clarsimp)
     apply (drule mem1_exception)
     apply (drule mem1_exception)
     apply (cases b, case_tac ba, cases r ,clarsimp)
    apply (case_tac "mem1 (a r+ 3) b" , clarsimp)
    apply (case_tac "mem1 (a r+ 2) ba", clarsimp)
    apply (case_tac "mem1 (a r+ 1) baa", clarsimp)
    apply (case_tac "mem1 (a r+ 0) bb", clarsimp)
    apply (drule mem1_exception)
    apply (drule mem1_exception)
    apply (drule mem1_exception)
    apply (drule mem1_exception)
    apply (cases b, case_tac ba, case_tac baa, case_tac bb , cases r ,clarsimp)
   apply (case_tac "mem1 (a r+ 7) b" , clarsimp)
   apply (case_tac "mem1 (a r+ 6) ba", clarsimp)
   apply (case_tac "mem1 (a r+ 5) baa", clarsimp)
   apply (case_tac "mem1 (a r+ 4) bb", clarsimp)
   apply (case_tac "mem1 (a r+ 3) bc", clarsimp)
   apply (case_tac "mem1 (a r+ 2) bd", clarsimp)
   apply (case_tac "mem1 (a r+ 1) be", clarsimp)
   apply (case_tac "mem1 (a r+ 0) bf", clarsimp)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (drule mem1_exception)
   apply (cases b, case_tac ba, case_tac baa, case_tac bb ,case_tac bc ,
                   case_tac bd ,  case_tac be ,  case_tac bf , cases r ,clarsimp)
  apply (clarsimp simp: raise'exception_def split:if_split_asm)
done


lemma pt_walk_range:
  "\<forall>va. pt_walk (ASID s) (MEM s) (TTBR0 s) va =  pt_walk (ASID s') (MEM s') (TTBR0 s') va  \<Longrightarrow> 
     pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV = pt_walk (ASID s') (MEM s') (TTBR0 s') ` UNIV"
  by auto



(* Refinement between write functions *)
(* writing to memory using saturated TLB *)


lemma write'mem'det1_TLBs1:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     tlb_det_set s' = tlb_det_set s \<or>  tlb_det_set s' = tlb_det_set s \<union> {the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)}"
  apply (cases "lookup (tlb_det_set s) (ASID s) va")
    apply (cases " is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
     apply (rule disjI1)
     apply (clarsimp simp: mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def
                           raise'exception_def write'mem1_eq_TLB split:if_split_asm)
    apply (rule disjI2)
    apply (clarsimp simp: mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def raise'exception_def
                          split:if_split_asm)
    apply (drule write'mem1_eq_TLB state.defs)
    apply (cases s , cases s' ; clarsimp)
   apply (rule disjI1)
   apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def raise'exception_def write'mem1_eq_TLB
                          split:if_split_asm)+
  apply (drule write'mem1_eq_TLB state.defs)
  apply (cases s , cases s' ; clarsimp)
done



lemma  write'mem'det1_rel1:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s')\<rbrakk>   \<Longrightarrow> 
      s' = s \<lparr> tlb_det_set := tlb_det_set s' , MEM:= MEM s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def split_def Let_def)
  apply (clarsimp split: if_split_asm)
   apply (drule write'mem1_rel)
   apply (cases "mmu_translate va s" , clarsimp)
   apply (drule mmu_det_rel)
   apply (cases s, cases s', case_tac b)
   apply clarsimp
  apply (clarsimp simp:  mmu_translate_tlb_det_state_ext_def Let_def split_def)
  apply (cases "lookup (tlb_det_set s) (ASID s) va")
    apply (clarsimp simp: Let_def raise'exception_def)
    apply (clarsimp simp: Let_def raise'exception_def)
   apply (clarsimp simp: Let_def raise'exception_def)
done




lemma  write'mem'_rel1:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s')\<rbrakk>   \<Longrightarrow> 
      s' = s \<lparr> tlb_set := tlb_set s' , MEM:= MEM s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def split_def Let_def)
  apply (clarsimp split: if_split_asm)
   apply (drule write'mem1_rel)
   apply (cases "mmu_translate va s" , clarsimp)
   apply (drule mmu_rel)
   apply (cases s, cases s', case_tac b)
   apply clarsimp
  apply (clarsimp simp:  mmu_translate_tlb_state_ext_def Let_def split_def)
  apply (cases "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) va")
    by (clarsimp simp: Let_def raise'exception_def)+
   



lemma write'mem'_TLBs1:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     tlb_set s' = tlb_set s - tlb_evict (typ_tlb s) \<or>  tlb_set s' = tlb_set s - tlb_evict (typ_tlb s) \<union> {the (pt_walk (ASID s) (MEM s) (TTBR0 s) va)}"
  apply (cases "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) va")
    apply (cases " is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
     apply (rule disjI1)
     apply (clarsimp simp: mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def Let_def
                           raise'exception_def write'mem1_eq_TLB split:if_split_asm)
    apply (rule disjI2)
    apply (clarsimp simp: mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def Let_def raise'exception_def
                          split:if_split_asm)
    apply (drule write'mem1_eq_TLB state.defs)
    apply (cases s , cases s' ; clarsimp)
   apply (rule disjI1)
   apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def mmu_translate_tlb_state_ext_def split_def Let_def raise'exception_def write'mem1_eq_TLB
                          split:if_split_asm)+
  apply (drule write'mem1_eq_TLB state.defs)
  apply (cases s , cases s' ; clarsimp)
done




lemma write_mem_state_trun_equal:
  "\<lbrakk>  write'mem1 (val, pa, sz) s = ((), s'); write'mem1 (val, pa, sz) t = ((), t'); 
     state.truncate s = state.truncate t \<rbrakk>  \<Longrightarrow> state.truncate s' = state.truncate t'"
  apply (frule write'mem1_rel)
  apply rotate_tac
  apply (frule write'mem1_rel)
  apply (subgoal_tac "MEM s' = MEM t' \<and> exception s' = exception t'")
   apply clarsimp
   apply (cases s, cases t, cases s', cases t', clarsimp simp: state.defs)
  apply (cases s, cases t, cases s', cases t', clarsimp simp: state.defs)
  apply (clarsimp simp: write'mem1_def Let_def state.defs raise'exception_def split:if_split_asm)
done

lemma  union_incon_cases:
  "lookup (t1 \<union> t2) a va = Incon \<Longrightarrow> 
      (lookup t1 a va = Incon \<and> lookup t2 a va = Incon)                       \<or>
      ((\<exists>x\<in>t1. lookup t1 a va = Hit x)  \<and> (\<exists>x\<in>t2. lookup t2 a va = Hit x))    \<or>
      (lookup t2 a va = Incon \<and> (\<exists>x\<in>t1. lookup t1 a va = Hit x) )             \<or>
      ((\<exists>x\<in>t2. lookup t2 a va = Hit x)  \<and> lookup t1 a va = Incon)             \<or>
      (lookup t1 a va = Miss \<and> lookup t2 a va = Incon)                        \<or>
      (lookup t1 a va = Incon \<and> lookup t2 a va = Miss) "
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm) 
  by auto

lemma  union_incon_cases1:
  "lookup (t1 \<union> t2) a va = Incon \<Longrightarrow> 
      (lookup t1 a va = Incon \<and> lookup t2 a va = Incon)                       \<or>
      ((\<exists>x\<in>t1. lookup t1 a va = Hit x)  \<and> (\<exists>x\<in>t2. lookup t2 a va = Hit x) \<and>  lookup t1 a va \<noteq>  lookup t2 a va)    \<or>
      (lookup t2 a va = Incon \<and> (\<exists>x\<in>t1. lookup t1 a va = Hit x) )             \<or>
      ((\<exists>x\<in>t2. lookup t2 a va = Hit x)  \<and> lookup t1 a va = Incon)             \<or>
      (lookup t1 a va = Miss \<and> lookup t2 a va = Incon)                        \<or>
      (lookup t1 a va = Incon \<and> lookup t2 a va = Miss) "
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  apply auto
   apply force+
done

lemma entry_set_hit_entry_range:
  "entry_set t a va = {x} \<Longrightarrow> (a , va) \<in> entry_range_asid_tags x"
  apply (clarsimp simp: entry_set_def split:if_split_asm)
   apply force
done

lemma asid_pt_walk:
  "\<lbrakk> \<not>is_fault (pt_walk asid mem ttbr0 x); 
      (a, va) \<in> entry_range_asid_tags (the (pt_walk asid mem ttbr0 x))\<rbrakk> \<Longrightarrow> a = asid"
  apply (clarsimp simp: pt_walk_def is_fault_def)
  apply (cases "get_pde mem ttbr0 x")
   apply (clarsimp simp: entry_range_asid_tags_def)
  apply (case_tac "aa" ; clarsimp simp: entry_range_asid_tags_def)
  apply (case_tac "get_pte mem x3 x" ,clarsimp simp: entry_range_asid_tags_def)
  apply (case_tac "aa" ; clarsimp simp: entry_range_asid_tags_def)
done


theorem entry_range_single_elementI:
  "\<lbrakk>x\<in> t ; (a, v) \<in> entry_range_asid_tags x ; (\<forall>y\<in>t. y\<noteq>x \<longrightarrow> (a, v) \<notin> entry_range_asid_tags y) \<rbrakk> \<Longrightarrow> 
         {E \<in> t. (a, v) \<in> entry_range_asid_tags E} = {x}" 
   by force



lemma asid_entry_set_pt_walk1 [simp]:
  "asid_entry ` the ` {e\<in>pt_walk asid m ttbr0 ` UNIV. \<not>is_fault e} = {asid} \<or>
     asid_entry ` the ` {e\<in>pt_walk asid m ttbr0 ` UNIV. \<not>is_fault e} = {}"
   by force+
 

lemma asid_lookup_miss:
  "\<lbrakk>asid_entry ` tlb = aset ; a \<notin> aset \<rbrakk> \<Longrightarrow> lookup tlb a va = Miss "
  using lookup_def entry_set_def entry_range_asid_tags_def by fastforce

  
lemma addr_val_eqD [dest!]:
  "addr_val a = addr_val b \<Longrightarrow> a = b"
  apply (cases a, cases b)
  by simp



(**************************************************************)


lemma  mmu_translate_asid_ttbr0 :
  "mmu_translate va (s::tlb_sat_state) = (a, b) \<Longrightarrow> ASID s = ASID b \<and> TTBR0 s = TTBR0 b"
 by (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def raise'exception_def split:lookup_type.splits if_split_asm) 
  

lemma mmu_translate_sat_sat_no_fault:
  "mmu_translate v s = (p,t) \<Longrightarrow>   saturated (typ_sat_tlb t)"
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def split: lookup_type.splits)
    by (clarsimp simp: saturated_def raise'exception_def split:if_split_asm)+


lemma write_mmu_sat_saturated:
  "\<lbrakk>mmu_write_size (val,va,sz) s = ((), t)  \<rbrakk>  \<Longrightarrow> saturated (typ_sat_tlb t)"
  apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def Let_def)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (clarsimp split: if_split_asm)
   apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
   apply (subgoal_tac "ASID s = ASID ba \<and> TTBR0 s = TTBR0 ba ")
    apply (clarsimp simp: saturated_def)
   apply (subgoal_tac "ASID s = ASID b \<and> TTBR0 s = TTBR0 b")
    apply clarsimp
    apply (clarsimp simp:  write'mem1_def Let_def)
    apply (clarsimp split: if_split_asm)
    apply (clarsimp simp:  raise'exception_def)
   apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def raise'exception_def split:lookup_type.splits  if_split_asm)
  using mmu_translate_sat_sat_no_fault surjective_pairing by blast



lemma write'mem1_eq_ASID_TTBR0:
  "\<lbrakk> write'mem1 (val, va, sz) s = ((), s') \<rbrakk>  \<Longrightarrow> ASID s' = ASID s \<and> TTBR0 s' = TTBR0 s"
   by (clarsimp simp: write'mem1_def raise'exception_def split: if_split_asm)
  

lemma wrtie_mem_sat_tlbs:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s') \<rbrakk> \<Longrightarrow>
     tlb_sat_set s' = tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e} \<or>
     tlb_sat_set s' = tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e} \<union> the ` {e\<in>pt_walk (ASID s') (MEM s') (TTBR0 s') ` UNIV. \<not> is_fault e}"
  apply (cases "exception (snd (mmu_translate va s)) \<noteq> NoException")
   apply (rule disjI1)
   apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def Let_def)
   apply (case_tac "mmu_translate va s" , clarsimp)
   apply (clarsimp simp: mmu_translate_sat_TLB_union')
  apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def Let_def)
  apply (case_tac "mmu_translate va s " , clarsimp)
  apply (case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (subgoal_tac "tlb_sat_set ba = tlb_sat_set b")
   apply (subgoal_tac "tlb_sat_set b  = tlb_sat_set s \<union> the ` {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
    apply (subgoal_tac "ASID ba = ASID s \<and>  TTBR0 ba = TTBR0 s")
     apply clarsimp
    apply (subgoal_tac "ASID b = ASID s \<and> TTBR0 b = TTBR0 s")
     apply (clarsimp simp: write'mem1_eq_ASID_TTBR0)
    apply (clarsimp simp: mmu_sat_eq_ASID_TTBR0_MEM)
   apply (clarsimp simp: mmu_translate_sat_TLB_union')
  apply (drule write'mem1_eq_TLB)
  apply (case_tac ba , case_tac b ; clarsimp)
done

lemma mmu_translate_subset_rel:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_tlb t) va; 
       tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ; mmu_translate va t = (pa', t')  \<rbrakk> \<Longrightarrow>
         tlb_det_set s' \<subseteq> tlb_sat_set t'"
  by (drule_tac t = t in  mmu_translate_det_sat_refine [unfolded tlb_rel_sat_def];
           simp add: tlb_rel_sat_def)

lemma mmu_translate_subset_rel':
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_tlb t) va; 
       tlb_rel_sat (typ_tlb s) (typ_sat_tlb t) ; mmu_translate va t = (pa', t')  \<rbrakk> \<Longrightarrow>
         tlb_set s' \<subseteq> tlb_sat_set t'"
  by (drule_tac t = t in  mmu_translate_sat_refine [unfolded tlb_rel_sat_def];
           simp add: tlb_rel_sat_def)
  

lemma mmu_write_tlb_subset:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t); 
       consistent (typ_sat_tlb t) va;
       mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> tlb_det_set s' \<subseteq> tlb_sat_set t'"
  apply (frule tlb_rel_satD)
  apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def , cases "mmu_translate va s" , clarsimp)
  apply (clarsimp simp:  mmu_write_size_tlb_sat_state_ext_def , cases "mmu_translate va t" , clarsimp)
  apply (frule_tac t' = ba and s' = b and t = t and s = s and pa' = aa in mmu_translate_subset_rel)
     apply simp
    apply simp
   apply simp
  apply (subgoal_tac "tlb_det_set b  =  tlb_det_set s'")
   apply simp
   apply (clarsimp split: if_split_asm)
      apply (case_tac "write'mem1 (val, aa, sz) ba", clarsimp simp:)
      apply (subgoal_tac "state.more bb = state.more ba")
       apply force
      apply (drule write'mem1_eq_TLB)  
      apply (drule write'mem1_eq_TLB)
      apply (clarsimp simp: typ_sat_tlb_def)
     apply force
    apply (case_tac "write'mem1 (val, aa, sz) ba", simp)
    apply (subgoal_tac "state.more ba = state.more b")
     apply force
    apply (drule write'mem1_eq_TLB)  
    apply (clarsimp simp: typ_sat_tlb_def)
   apply force
  apply (clarsimp split: if_split_asm)
   apply (drule write'mem1_eq_TLB)
   apply (cases s' , case_tac b, clarsimp simp:)
 apply (drule write'mem1_eq_TLB)
  by (cases s' , case_tac b, clarsimp simp:)


lemma mmu_translate_excep:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)\<rbrakk>  \<Longrightarrow>  exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule (2)  mmu_translate_det_sat_refine, clarsimp simp: Let_def)
 done




lemma mmu_translate_excep':
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p, t') ;
     consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_tlb s) (typ_sat_tlb t)\<rbrakk>  \<Longrightarrow>  exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat (typ_tlb s') (typ_sat_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule (2)  mmu_translate_sat_refine, clarsimp simp: Let_def)
 done



lemma sat_states_parameters:
  "\<lbrakk> mmu_translate va t = (pa', t') ; saturated (typ_sat_tlb t) \<rbrakk> \<Longrightarrow>
      state.more t' = state.more t \<and> ASID t' = ASID t \<and> MEM t' = MEM t \<and> TTBR0 t' = TTBR0 t \<and>  saturated (typ_sat_tlb t')"
  apply (frule sat_state_tlb')
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def saturated_def)
  apply (cases "lookup (tlb_sat_set t) (ASID t) va" )
    apply (clarsimp simp: raise'exception_def split:if_split_asm)+
  done


lemma mmu_wrtie_sat_rel:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s')\<rbrakk>   \<Longrightarrow> 
      s' = s \<lparr> tlb_sat_set:= tlb_sat_set s' , MEM:= MEM s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def Let_def)
  apply (cases "mmu_translate va s" , clarsimp)
  apply (clarsimp split: if_split_asm)
   apply (case_tac " write'mem1 (val, a, sz) b", clarsimp)
   apply (drule write'mem1_rel)
   apply (drule mmu_sat_rel')
   apply (cases s, cases s', case_tac a, case_tac b, case_tac ba)
   apply clarsimp
  apply (clarsimp simp: mmu_translate_tlb_sat_state_ext_def Let_def)
  apply (cases "lookup (tlb_sat_set s \<union> the ` {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) va ")
    apply (clarsimp simp: raise'exception_def  split:if_split_asm) 
   apply (clarsimp simp: raise'exception_def split:if_split_asm)
  apply (clarsimp simp: raise'exception_def split:if_split_asm)
done



lemma mmu_translate_sat_mem_excep:
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p', t') ;
     consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)\<rbrakk>  \<Longrightarrow> MEM s' = MEM t' \<and> exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule (2)  mmu_translate_det_sat_refine, clarsimp simp: Let_def)
 done


lemma mmu_translate_sat_mem_excep':
  "\<lbrakk> mmu_translate va s = (p, s') ; mmu_translate va t = (p', t') ;
     consistent (typ_sat_tlb t) va; tlb_rel_sat (typ_tlb s) (typ_sat_tlb t)\<rbrakk>  \<Longrightarrow> MEM s' = MEM t' \<and> exception s' = exception t'"
  apply (subgoal_tac "tlb_rel_sat (typ_tlb s') (typ_sat_tlb t')")
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule (2)  mmu_translate_sat_refine, clarsimp simp: Let_def)
 done

lemma  mmu_translate_det_sat_pa:
  "\<lbrakk> mmu_translate va s = (pa, s'); tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)  ; consistent (typ_sat_tlb t) va;
         mmu_translate va t = (pa', t')  \<rbrakk> \<Longrightarrow> pa = pa'"
  using mmu_translate_det_sat_refine by fastforce




lemma  mmu_translate_sat_pa:
  "\<lbrakk> mmu_translate va s = (pa, s'); tlb_rel_sat (typ_tlb s) (typ_sat_tlb t)  ; consistent (typ_sat_tlb t) va;
         mmu_translate va t = (pa', t')  \<rbrakk> \<Longrightarrow> pa = pa'"
  using mmu_translate_sat_refine by fastforce


lemma write_mem_det_sat_MEM:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s');  tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t) ; consistent (typ_sat_tlb t) va; 
                   mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> MEM s' = MEM t'"
  apply (frule tlb_rel_satD)
  apply (clarsimp simp:  mmu_write_size_tlb_det_state_ext_def , cases "mmu_translate va s" , clarsimp)
  apply (clarsimp simp:  mmu_write_size_tlb_sat_state_ext_def , cases "mmu_translate va t" , clarsimp)
  apply (subgoal_tac "MEM ba = MEM b \<and>  exception ba = exception b")
   prefer 2
   apply (frule_tac t = t and t' = ba in mmu_translate_sat_mem_excep; simp)
  apply (subgoal_tac "a = aa")
   prefer 2
   apply (frule  mmu_translate_det_sat_pa; simp)
  apply simp
  apply (clarsimp split: if_split_asm)
  apply (case_tac "write'mem1 (val, aa, sz) ba", simp)
  apply (frule_tac t = ba and t' = bb in  write_same_mem, simp, simp)
  by (case_tac bb, cases t', simp)




lemma mmu_write_size_det_sat_state_trun:
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)  ; consistent (typ_sat_tlb t) va;
     mmu_write_size (val,va, sz) t = ((), t')\<rbrakk> \<Longrightarrow> state.truncate t' = state.truncate s'"
  apply (frule (3)  write_mem_det_sat_MEM)
  apply (frule tlb_rel_satD, clarsimp)
  apply (frule write'mem'det1_rel1)
  apply (rotate_tac)
  apply (frule mmu_wrtie_sat_rel)
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (subgoal_tac "exception s' = exception t'")
   apply (cases s, cases t, cases s' , cases t')
   apply (clarsimp simp: state.defs tlb_sat_state.defs)
  apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def mmu_write_size_tlb_det_state_ext_def Let_def)
  apply (case_tac "mmu_translate va t" , case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (subgoal_tac "exception b = exception bb \<and> a = aa")
   apply (clarsimp split: if_split_asm)
   apply (subgoal_tac "MEM b = MEM bb ")
    apply (frule_tac s="bb" and s'="s'" and t = b and t' = ba in write_same_mem_excep ; clarsimp)
   apply (frule_tac s="s" and s'="bb" and t = t and t' = b and p' = aa in mmu_translate_sat_mem_excep ; clarsimp simp: consistent0_def tlb_rel_sat_def)
  apply (rule conjI)
   apply (frule_tac s = "s" and s' = "bb" and t = "t" and t' = "b" in   mmu_translate_excep ; clarsimp simp: tlb_rel_sat_def)
  by (frule_tac t= t and pa' = a and t' = b in mmu_translate_det_sat_pa ; clarsimp simp: tlb_rel_sat_def) +


lemma mmu_write_tlb_subset':
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_tlb s) (typ_sat_tlb t); 
       consistent (typ_sat_tlb t) va;
       mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> tlb_set s' \<subseteq> tlb_sat_set t'"
  apply (frule tlb_rel_satD)
  apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def , cases "mmu_translate va s" , clarsimp)
  apply (clarsimp simp:  mmu_write_size_tlb_sat_state_ext_def , cases "mmu_translate va t" , clarsimp)
  apply (frule_tac t' = ba and s' = b and t = t and s = s and pa' = aa in mmu_translate_subset_rel')
     apply simp
    apply simp
   apply simp
  apply (subgoal_tac "tlb_set b  =  tlb_set s'")
   apply simp
   apply (clarsimp split: if_split_asm)
      apply (case_tac "write'mem1 (val, aa, sz) ba", clarsimp simp:)
      apply (subgoal_tac "state.more bb = state.more ba")
       apply force
      apply (drule write'mem1_eq_TLB)  
      apply (drule write'mem1_eq_TLB)
      apply (clarsimp simp: typ_sat_tlb_def)
     apply force
    apply (case_tac "write'mem1 (val, aa, sz) ba", simp)
    apply (subgoal_tac "state.more ba = state.more b")
     apply force
    apply (drule write'mem1_eq_TLB)  
    apply (clarsimp simp: typ_sat_tlb_def)
   apply force
  apply (clarsimp split: if_split_asm)
   apply (drule write'mem1_eq_TLB)
   apply (cases s' , case_tac b, clarsimp simp:)
  apply (drule write'mem1_eq_TLB)
  by (cases s' , case_tac b, clarsimp simp:)


lemma write_mem_sat_MEM:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s');  tlb_rel_sat (typ_tlb s) (typ_sat_tlb t) ; consistent (typ_sat_tlb t) va; 
                   mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow> MEM s' = MEM t'"
  apply (frule tlb_rel_satD)
  apply (clarsimp simp:  mmu_write_size_tlb_state_ext_def , cases "mmu_translate va s" , clarsimp)
  apply (clarsimp simp:  mmu_write_size_tlb_sat_state_ext_def , cases "mmu_translate va t" , clarsimp)
  apply (subgoal_tac "MEM ba = MEM b \<and>  exception ba = exception b")
   prefer 2
   apply (frule_tac t = t and t' = ba in mmu_translate_sat_mem_excep'; simp)
  apply (subgoal_tac "a = aa")
   prefer 2
   apply (frule  mmu_translate_sat_pa; simp)
  apply simp
  apply (clarsimp split: if_split_asm)
  apply (case_tac "write'mem1 (val, aa, sz) ba", simp)
  apply (frule_tac t = ba and t' = bb in  write_same_mem, simp, simp)
  by (case_tac bb, cases t', simp)

 

lemma mmu_write_size_det_sat_state_trun':
  "\<lbrakk>mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_tlb s) (typ_sat_tlb t)  ; consistent (typ_sat_tlb t) va;
     mmu_write_size (val,va, sz) t = ((), t')\<rbrakk> \<Longrightarrow> state.truncate t' = state.truncate s'"
  apply (frule (3)  write_mem_sat_MEM)
  apply (frule tlb_rel_satD, clarsimp)
  apply (frule write'mem'_rel1)
  apply (rotate_tac)
  apply (frule mmu_wrtie_sat_rel)
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (subgoal_tac "exception s' = exception t'")
   apply (cases s, cases t, cases s' , cases t')
   apply (clarsimp simp: state.defs tlb_sat_state.defs)
  apply (clarsimp simp: mmu_write_size_tlb_sat_state_ext_def mmu_write_size_tlb_state_ext_def Let_def)
  apply (case_tac "mmu_translate va t" , case_tac "write'mem1 (val, a, sz) b" , clarsimp)
  apply (case_tac "mmu_translate va s" , clarsimp)
  apply (subgoal_tac "exception b = exception bb \<and> a = aa")
   apply (clarsimp split: if_split_asm)
   apply (subgoal_tac "MEM b = MEM bb ")
    apply (frule_tac s="bb" and s'="s'" and t = b and t' = ba in write_same_mem_excep ; clarsimp)
   apply (frule_tac s="s" and s'="bb" and t = t and t' = b and p' = aa in mmu_translate_sat_mem_excep' ; clarsimp simp: consistent0_def tlb_rel_sat_def)
  apply (rule conjI)
   apply (frule_tac s = "s" and s' = "bb" and t = "t" and t' = "b" in   mmu_translate_excep' ; clarsimp simp: tlb_rel_sat_def)
  by (frule_tac t= t and pa' = a and t' = b in mmu_translate_sat_pa ; clarsimp simp: tlb_rel_sat_def) +


lemma not_fault_ptable_defined:
  "\<not>is_fault (pt_walk a hp1 rt va) \<Longrightarrow> ptable_lift hp1 rt va \<noteq> None"
  apply (clarsimp simp: pt_walk_def is_fault_def ptable_lift_def lookup_pde_def lookup_pte_def split:option.splits pde.splits pte.splits) 
  by force



lemma asid_unequal_miss':
  " a \<noteq> ASID b \<Longrightarrow>
   lookup (the ` {e \<in> range (pt_walk (ASID b) (MEM bc) (TTBR0 b)). \<not> is_fault e}) a bb = Miss"
  apply (subgoal_tac "entry_set (the ` {e \<in> range (pt_walk (ASID b) (MEM bc) (TTBR0 b)). \<not> is_fault e}) a bb = {}")
  apply (clarsimp simp:  lookup_def entry_set_def) 
  by (clarsimp simp: entry_set_va_set a_va_set_def pt_walk_def is_fault_def entry_range_asid_tags_def split: option.splits pde.splits pte.splits)
  
  




lemma lookup_hit_mis_hit:
  "\<lbrakk>lookup (t \<union> t') a va = Hit x ; lookup t' a va = Miss \<rbrakk> \<Longrightarrow> lookup t a va = Hit x   "
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  apply auto
  apply force
  done


lemma lookup_union_hit_miss_hit :
  "\<lbrakk>lookup (t \<union> t') a va = Hit x ; lookup t' a va \<noteq> Miss \<rbrakk> \<Longrightarrow> lookup t' a va = Hit x   "
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)  
  by force+
  

lemma lookup_union_hit_miss_hit' :
  "\<lbrakk>lookup (t \<union> t') a va = Hit x ; lookup t a va \<noteq> Miss \<rbrakk> \<Longrightarrow> lookup t a va = Hit x   "
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
   by force+

lemma   lookup_union_hit_hit_miss :
  "\<lbrakk>lookup (t \<union> t') a va = Hit x ;  \<forall>x\<in>t. lookup t a va \<noteq> Hit x\<rbrakk> \<Longrightarrow> lookup t a va = Miss   "
 apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
   by force+



lemma lookup_hit_miss_or_hit :
  " lookup (t1 \<union> t2) a va = Hit x \<and> x \<in> t1  \<Longrightarrow> 
              lookup t2 a va = Miss \<or> (lookup t2 a va = Hit x)"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  by force+


lemma not_miss_incon_hit:
  "lookup t a va \<noteq> Miss \<Longrightarrow> lookup t a va = Incon \<or> (\<exists>x\<in>t. lookup t a va = Hit x)"
 apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  by auto

lemma  entry_set_rewrite :
  "{E. (E \<in> t1 \<or> E \<in> t2) \<and> (asid_entry xa, va) \<in> Pair (asid_entry E) ` entry_range E} = {x} \<Longrightarrow>
        x \<in> t1 \<or> x \<in> t2 \<or> (x\<in>t1 \<and> x\<in>t2)"
  by blast


lemma  lookup_not_hit_false:
  "\<lbrakk>lookup (t1 \<union> t2) a va = Hit x; lookup t1 a va \<noteq> Hit x; lookup t2 a va \<noteq> Hit x\<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
          apply safe by blast+



lemma  lookup_not_hit_miss:
  "\<lbrakk>lookup (t1 \<union> t2) a va = Hit x ;   lookup t1 a va \<noteq> Hit x\<rbrakk> \<Longrightarrow> lookup t1 a va = Miss   "
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
   apply safe
       by force+


lemma  lookup_hit_union_cases:
  "(\<exists>x\<in>(t1 \<union> t2). lookup (t1 \<union> t2) a va = Hit x)  \<Longrightarrow>
      ((\<exists>x\<in>t1. lookup t1 a va = Hit x) \<and> lookup t2 a va = Miss)       \<or>
      ((\<exists>x\<in>t2. lookup t2 a va = Hit x)  \<and> lookup t1 a va = Miss)      \<or>
      ((\<exists>x\<in>t1. \<exists>x1\<in>t2.  lookup t1 a va = Hit x  \<and> lookup t2 a va = Hit x1 \<and>  x = x1)) "
  apply (safe ; clarsimp)
         apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm ,force , force, ((safe ; force) [1]))
        apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm , force, force)
       apply (drule_tac x = "x" in bspec , clarsimp)
       apply (drule_tac not_miss_incon_hit , erule disjE ; clarsimp )
       using lookup_hit_miss_or_hit apply force
      apply (frule lookup_union_hit_miss_hit , clarsimp)
      apply (drule_tac x = "x" in bspec ,clarsimp)
      apply (subgoal_tac "x \<in> t2" , clarsimp)
       apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm ; force)
      using lookup_in_tlb apply force
     apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm ;  (safe ; force))
    using lookup_union_hit_hit_miss apply clarsimp
   apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm ; (safe ; force))
  apply (cases " lookup t1 a va = Miss" ; clarsimp)
  apply (frule_tac lookup_union_hit_miss_hit ; clarsimp)
  apply (frule_tac lookup_union_hit_miss_hit' ; clarsimp)
  apply (subgoal_tac "x\<in>t1")
   apply (drule_tac x = "x" in bspec ; clarsimp)
  using lookup_in_tlb by force

   



lemma lookup_hit_union_cases':
  " lookup (t1 \<union> t2) a va = Hit x  \<Longrightarrow>
      (lookup t1 a va = Hit x \<and> lookup t2 a va = Miss)  \<or>
      (lookup t2 a va = Hit x \<and> lookup t1 a va = Miss)  \<or>
      (lookup t1 a va = Hit x  \<and> lookup t2 a va = Hit x) "
  apply (safe , clarsimp)
         apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm , (safe ; force) , force)
         apply auto [1]
         apply (rule_tac x = x in exI)
         apply (safe ; force)
        apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm ; force)
       apply ((drule lookup_not_hit_false ; clarsimp) +) [2]
     apply (drule lookup_union_hit_miss_hit ; clarsimp)
    apply (drule lookup_not_hit_miss ; clarsimp)
   apply (drule lookup_union_hit_miss_hit ; clarsimp)
  by (drule lookup_hit_miss_or_hit' ; clarsimp)




lemma  not_elem_rewrite:
  "(ASID b, bb)
                \<notin> (\<lambda>x. (ASID b, addr_val x)) `
                   {va. \<not> is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) va) \<and> \<not> is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) va) \<and> pt_walk (ASID b) (MEM b) (TTBR0 b) va \<noteq> pt_walk (ASID b) (MEM bc) (TTBR0 b) va \<or>
                        \<not> is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) va) \<and> is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) va)} \<Longrightarrow>
   (is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bb)) \<or> is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) (Addr bb)) \<or> pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bb) = pt_walk (ASID b) (MEM bc) (TTBR0 b) (Addr bb)) \<and>
            (is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) (Addr bb)) \<or> \<not> is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) (Addr bb)))  "
  by force




lemma  not_elem_rewrite':
  "(ASID b, bb)
                \<notin> (\<lambda>x. (ASID b, x)) `
                   {va. \<not> is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) va) \<and> \<not> is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) va) \<and> pt_walk (ASID b) (MEM b) (TTBR0 b) va \<noteq> pt_walk (ASID b) (MEM bc) (TTBR0 b) va \<or>
                        \<not> is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) va) \<and> is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) va)} \<Longrightarrow>
   (is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) bb) \<or> is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) bb) \<or> pt_walk (ASID b) (MEM b) (TTBR0 b) bb = pt_walk (ASID b) (MEM bc) (TTBR0 b) bb) \<and>
            (is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) bb) \<or> \<not> is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) bb))  "
  by force


lemma lookup_range_pt_walk_not_incon:
  "lookup (the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e}) asid va \<noteq> Incon"
  apply (case_tac "\<not>is_fault (pt_walk asid mem ttbr0 va)")
   apply (clarsimp simp: lookup_range_pt_walk_hit)
  apply clarsimp
  apply (subgoal_tac " lookup (the ` {e \<in> pt_walk asid mem ttbr0 ` top. \<not> is_fault e}) asid va = Miss")
   apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  apply (thin_tac "lookup (the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e}) asid va = Incon")
  apply (subgoal_tac "entry_set (the ` {e \<in> range (pt_walk asid mem ttbr0). \<not> is_fault e}) asid va = {}")
   apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  apply (clarsimp simp: entry_set_va_set a_va_set_def)
  apply (drule not_fault_ptable_defined)
  apply (subgoal_tac "pt_walk asid mem ttbr0 va \<noteq> None", simp add: is_fault_def)
  apply (thin_tac "is_fault (pt_walk asid mem ttbr0 va)")
  apply (case_tac "the (pt_walk asid mem ttbr0 xa)")
   apply (clarsimp simp: entry_range_asid_tags_def entry_range_def pt_walk_def is_fault_def)
   apply (case_tac "get_pde mem ttbr0 xa" ; clarsimp simp: ptable_lift_def lookup_pde_def)
   apply (case_tac a ; clarsimp)
   apply (case_tac "get_pte mem x3 xa" ; clarsimp simp: lookup_pte_def)
   apply (case_tac a ; clarsimp)
   apply (subgoal_tac "get_pde mem ttbr0 (Addr x) = get_pde mem ttbr0 xa", simp)
    apply (subgoal_tac " get_pte mem x3 (Addr x) =  get_pte mem x3 xa", simp)
    prefer 2
    apply (clarsimp)
    apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
    apply (subgoal_tac "((addr_val xa >> 20) && mask 12 << 2) =
                         ((x >> 20) && mask 12 << 2) ")
     prefer 2
  using offset_mask_eq_1 apply blast
    apply force
   apply (clarsimp simp:  get_pte_def vaddr_pt_index_def)
   apply (subgoal_tac "(( addr_val xa >> 12) && mask 8 << 2) =
                          (( x >> 12) && mask 8 << 2) ")
    prefer 2
  using offset_mask_eq apply blast
   apply force
  apply (clarsimp simp: entry_range_asid_tags_def entry_range_def pt_walk_def is_fault_def)
  apply (case_tac "get_pde mem ttbr0 xa" ; clarsimp simp: ptable_lift_def lookup_pde_def)
  apply (case_tac a ; clarsimp)
   apply (case_tac "get_pte mem x3 xa" ; clarsimp simp: lookup_pte_def)
   apply (case_tac a ; clarsimp)
  apply (subgoal_tac "get_pde mem ttbr0 (Addr x) = get_pde mem ttbr0 xa", simp)
  apply (clarsimp)
  apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
  apply (subgoal_tac "((addr_val xa >> 20) && mask 12 << 2) = ((x >> 20) && mask 12 << 2)")
   apply force
  using shfit_mask_eq by blast




lemma write_asid_incon_set_rel1:
  "\<lbrakk> saturated (typ_sat_tlb b) ; 
       incon_va_set (typ_sat_tlb b) \<subseteq> iset(tlb_incon_set ba) ;  ptable_tlb_va_incon (typ_sat_tlb b) \<subseteq> iset(tlb_incon_set ba) ; ASID b = ASID bb ; TTBR0 b = TTBR0 bb\<rbrakk> \<Longrightarrow>
      incon_va_set (typ_sat_tlb (bb\<lparr>tlb_sat_set := tlb_sat_set b \<union> the ` {e \<in> range (pt_walk (ASID b) (MEM bc) (TTBR0 b)). \<not> is_fault e}\<rparr>))
            \<subseteq> iset (tlb_incon_set ba) \<union> ptable_comp' (ASID b) (MEM b) (MEM bc) (TTBR0 b) (TTBR0 b)"
  apply (clarsimp)
  apply (clarsimp simp: incon_va_set_def ptable_comp'_def  ptable_tlb_va_incon_def)
  apply (erule disjE)
   apply clarsimp
   apply (drule union_incon_cases1)
   apply (erule disjE)
    apply (clarsimp simp: lookup_range_pt_walk_not_incon)
   apply (erule disjE, clarsimp) apply blast
   apply (erule disjE) apply (clarsimp simp: lookup_range_pt_walk_not_incon)
   apply (erule disjE) apply (clarsimp simp:) apply blast
   apply (erule disjE) apply (clarsimp simp: lookup_range_pt_walk_not_incon)
   apply blast
  apply (erule disjE)
   apply (erule disjE)
    apply (drule union_incon_cases1)
    apply (erule disjE)
     apply (clarsimp simp: lookup_range_pt_walk_not_incon)
    apply (erule disjE, clarsimp) apply blast
    apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon)
    apply (erule disjE, clarsimp) apply blast
    apply (erule disjE)
     apply (clarsimp simp: lookup_range_pt_walk_not_incon)
    apply blast
   apply (drule union_incon_cases1)
   apply (erule disjE)
    apply (clarsimp simp: lookup_range_pt_walk_not_incon)
   apply (erule disjE, clarsimp) 
    apply force
   apply (erule disjE, clarsimp simp: lookup_range_pt_walk_not_incon)
   apply (erule disjE, clarsimp) apply force
   apply (erule disjE, clarsimp  simp: lookup_range_pt_walk_not_incon) 
   apply blast
  apply (erule disjE) apply blast
  apply (drule union_incon_cases1)
  apply (erule disjE)
   apply (clarsimp simp: lookup_range_pt_walk_not_incon)
  apply (erule disjE, clarsimp)
   apply (case_tac "is_fault (pt_walk (ASID bb) (MEM b) (TTBR0 bb) x)")
    apply force
   apply (subgoal_tac "xa = the (pt_walk (ASID bb) (MEM b) (TTBR0 bb) x)")
    apply clarsimp
    apply (clarsimp simp: lookup_range_pt_walk_hit)
   apply (thin_tac "pt_walk (ASID bb) (MEM b) (TTBR0 bb) x = pt_walk (ASID bb) (MEM bc) (TTBR0 bb) x")
   apply (subgoal_tac " lookup (tlb_sat_set b \<union> the ` {e \<in> range (pt_walk (ASID bb) (MEM b) (TTBR0 bb)). \<not> is_fault e}) (ASID bb) x = Hit xa")
    prefer 2
    apply (clarsimp simp: saturated_def)
    apply (metis (no_types, lifting) sup.orderE)
   apply (thin_tac "lookup (tlb_sat_set b) (ASID bb) x = Hit xa")
   apply (drule lookup_hit_union_cases')
   apply (erule disjE, clarsimp)
    apply (clarsimp simp:  lookup_range_pt_walk_hit)
   apply (erule disjE, clarsimp)
    apply (simp add: lookup_range_pt_walk_hit) 
   apply (simp add: lookup_range_pt_walk_hit)
  apply (erule disjE, clarsimp  simp: lookup_range_pt_walk_not_incon)
  apply (erule disjE, clarsimp) apply blast
  apply (erule disjE, clarsimp  simp: lookup_range_pt_walk_not_incon)
  by blast


lemma  lookup_miss_is_fault:
  "lookup (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v = Miss \<Longrightarrow> is_fault (pt_walk a m r v)"
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  apply (drule_tac x = "the (pt_walk a m r v)" in spec)
   using asid_va_entry_range_pt_entry by force

lemma  not_elem_rewrite'':
  "(ASID b, bb)
                 \<notin> Pair (ASID b) `
                {va. \<not> is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) va) \<and>
                     \<not> is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) va) \<and> pt_walk (ASID b) (MEM b) (TTBR0 b) va \<noteq> pt_walk (ASID b) (MEM bc) (TTBR0 b) va \<or>
                     \<not> is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) va) \<and> is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) va)} \<Longrightarrow>
   (is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) bb) \<or> is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) bb) \<or> pt_walk (ASID b) (MEM b) (TTBR0 b) bb = pt_walk (ASID b) (MEM bc) (TTBR0 b) bb) \<and>
            (is_fault (pt_walk (ASID b) (MEM b) (TTBR0 b) bb) \<or> \<not> is_fault (pt_walk (ASID b) (MEM bc) (TTBR0 b) bb))  "
  by force



lemma  lookup_miss_is_fault_intro:
  "is_fault (pt_walk a m r v) \<Longrightarrow> lookup (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v = Miss"
  apply (subgoal_tac  "entry_set (the ` {e \<in> range (pt_walk a m r). \<not> is_fault e}) a v = {}")
   apply (clarsimp simp: lookup_def)
  apply (clarsimp simp: entry_set_va_set)
  apply (clarsimp simp: a_va_set_def)
  apply (subgoal_tac "pt_walk a m r xa = pt_walk a m r v", simp)
  apply (thin_tac "is_fault (pt_walk a m r v)")
  apply (clarsimp simp: entry_range_asid_tags_def entry_range_def pt_walk_def is_fault_def)
  apply (case_tac "get_pde m r xa" ; clarsimp)
  apply (case_tac aa ; clarsimp)
   apply (case_tac "get_pte m x3 xa " ; clarsimp)
   apply (subgoal_tac "get_pde m r xa = get_pde m r v" ; clarsimp)
    apply (subgoal_tac "get_pte m x3 xa = get_pte m x3 v" ; clarsimp)
     apply (case_tac aa ; clarsimp simp: word_extract_def word_bits_def)
     apply (case_tac y, clarsimp)
  using va_offset_higher_bits apply blast
  using va_offset_higher_bits apply blast
    apply (case_tac y, clarsimp)
     apply (case_tac aa; clarsimp)
     apply (clarsimp simp:  get_pte_def vaddr_pt_index_def)
     apply (subgoal_tac "(( addr_val xa >> 12) && mask 8 << 2) =
                          (( x >> 12) && mask 8 << 2) ")
      prefer 2
  using offset_mask_eq apply blast
     apply force
    apply (case_tac y; clarsimp)
    apply (case_tac aa; clarsimp)
   apply (case_tac y; clarsimp)
    apply (case_tac aa; clarsimp)
    apply (clarsimp simp: get_pde_def vaddr_pd_index_def)
    apply (subgoal_tac "((addr_val xa >> 20) && mask 12 << 2) =
                         ((x >> 20) && mask 12 << 2) ")
     prefer 2
  using offset_mask_eq_1 apply blast
    apply force
   apply (case_tac aa; clarsimp)
  apply (case_tac y; clarsimp simp: word_extract_def word_bits_def)
  apply (subgoal_tac "get_pde m r xa = get_pde m r (Addr x)" ; clarsimp simp:  word_extract_def word_bits_def)
   apply (case_tac a ; clarsimp simp: get_pde_def vaddr_pd_index_def)
  using va_offset_higher_bits_1 apply blast
  apply ( clarsimp simp: get_pde_def vaddr_pd_index_def)
  apply (subgoal_tac "((addr_val xa >> 20) && mask 12 << 2) = ((x >> 20) && mask 12 << 2)")
   apply force
  using shfit_mask_eq by blast


lemma  write_asid_incon_set_rel'1:
  "\<lbrakk>saturated (typ_sat_tlb b) ; ASID bb = ASID b; MEM bb = MEM bc; TTBR0 bb = TTBR0 b ;
       incon_va_set (typ_sat_tlb b) \<subseteq> iset (tlb_incon_set ba) ;  ptable_tlb_va_incon (typ_sat_tlb b) \<subseteq> iset(tlb_incon_set ba)\<rbrakk> \<Longrightarrow>
      ptable_tlb_va_incon (typ_sat_tlb (bb\<lparr>tlb_sat_set := tlb_sat_set b \<union> the ` {e \<in> range (pt_walk (ASID b) (MEM bc) (TTBR0 b)). \<not> is_fault e}\<rparr>))
            \<subseteq> iset (tlb_incon_set ba) \<union> ptable_comp' (ASID b) (MEM b) (MEM bc) (TTBR0 b) (TTBR0 b)"
  apply (clarsimp)
  apply (clarsimp simp: ptable_tlb_va_incon_def  incon_va_set_def ptable_comp'_def)
  apply (drule lookup_hit_union_cases')
  apply (erule disjE, blast)
  apply (erule disjE, clarsimp simp: lookup_range_pt_walk_hit lookup_miss_is_fault_intro)  
  by blast
    



lemma lookup_miss_union_equal:
  " lookup t' a v = Miss \<Longrightarrow> lookup (t \<union> t') a v = lookup t a v "
  apply (clarsimp simp: lookup_def entry_set_def split: if_split_asm)
  apply safe
  by force+



lemma lookup_miss_union_miss_miss:
  "\<lbrakk>lookup t a v = Miss;  lookup t' a v = Miss\<rbrakk> \<Longrightarrow> 
           lookup (t \<union> t') a v = Miss"
  apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)
  apply safe
     by auto




lemma mmu_translate_saturated_tlb_unchange:
  "\<lbrakk> mmu_translate va s = (pa, s'); saturated (typ_sat_tlb s) \<rbrakk>
       \<Longrightarrow> tlb_sat_set s' = tlb_sat_set s"
  by (metis (mono_tags, lifting) Collect_cong mmu_translate_sat_TLB_union' sat_state_tlb' tlb_sat_more typ_sat_prim_parameter)


lemma asid_unequal_miss'':
  " a' \<noteq> a \<Longrightarrow>
   lookup (the `{e \<in> range (pt_walk a m r). \<not> is_fault e}) a' v = Miss"
  apply (clarsimp simp:  lookup_def entry_set_def entry_range_asid_tags_def) 
  by force


lemma mmu_write_det_sat_refine:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)  ; consistent (typ_sat_tlb t) va;
        mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow>  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t') "
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (clarsimp simp: write_mmu_sat_saturated )
  apply (rule conjI)
   prefer 2                                                               
   apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in mmu_write_tlb_subset; clarsimp simp: tlb_rel_sat_def)
  apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in mmu_write_size_det_sat_state_trun; clarsimp simp: tlb_rel_sat_def)
  done



lemma mmu_write_non_det_sat_refine:
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s'); tlb_rel_sat (typ_tlb s) (typ_sat_tlb t)  ; consistent (typ_sat_tlb t) va;
        mmu_write_size (val,va, sz) t = ((), t') \<rbrakk> \<Longrightarrow>  tlb_rel_sat (typ_tlb s') (typ_sat_tlb t') "
  apply (clarsimp simp: tlb_rel_sat_def)
  apply (clarsimp simp: write_mmu_sat_saturated )
  apply (rule conjI)
   prefer 2                                                               
   apply (frule_tac s = s and s' = s' and t = t and t' = t' in mmu_write_tlb_subset'; clarsimp simp: tlb_rel_sat_def)
  apply (frule_tac s="s" and s'="s'" and t="t" and t'="t'" in mmu_write_size_det_sat_state_trun'; clarsimp simp: tlb_rel_sat_def)
done





(* refinement between saturated and second abstracted model *)

lemma mmu_translate_incon_unchange':
  "\<lbrakk> mmu_translate va t = (aa, ba)\<rbrakk>  \<Longrightarrow> tlb_incon_set ba = tlb_incon_set t"
  by (clarsimp simp: mmu_translate_tlb_incon_state_ext_def Let_def raise'exception_def split: if_split_asm)


lemma write_refinement_incon_incon_only2':        
  "\<lbrakk> mmu_write_size (val,va, sz) s = ((), s');  va \<notin> iset (tlb_incon_set t);
          tlb_rel_abs (typ_sat_tlb s) (typ_incon t) ;  mmu_write_size (val,va, sz) t = ((), t')  \<rbrakk> \<Longrightarrow> 
                                 tlb_rel_abs (typ_sat_tlb s') (typ_incon t')"  
  apply (frule_tac s = s in tlb_rel_abs2_consistent' ; clarsimp )
  apply (frule_tac tlb_rel_absD , clarsimp)
  apply (clarsimp simp:  mmu_write_size_tlb_sat_state_ext_def  mmu_write_size_tlb_incon_state_ext_def)
  apply (cases "mmu_translate va s" ,cases "mmu_translate va t" , clarsimp)
  apply (frule_tac t=t and pa'= aa and t' = ba in   mmu_translate_sat_abs2_refine)  apply clarsimp+
  apply (clarsimp simp: tlb_rel_abs_def)
  apply (subgoal_tac "exception b = exception ba")
   prefer 2 apply (case_tac b , case_tac ba , clarsimp simp: state.defs)
  apply (clarsimp split: if_split_asm)
  apply (case_tac "write'mem1 (val, aa, sz) b " , case_tac "write'mem1 (val, aa, sz) ba" , clarsimp simp: Let_def)
  apply (subgoal_tac "state.truncate bb = state.truncate bc")
   prefer 2 
  using write_mem_state_trun_equal apply blast
  apply (rule conjI , clarsimp simp: state.defs)
  apply (subgoal_tac "MEM bb = MEM bc  \<and> MEM s = MEM b" , simp)
   apply (subgoal_tac "ASID s = ASID b \<and> TTBR0 s = TTBR0 b" , simp)
    apply (subgoal_tac "saturated (typ_sat_tlb b)")
     prefer 2
  using mmu_translate_sat_sat_no_fault apply blast
    prefer 2
  using mmu_sat_eq_ASID_TTBR0_MEM apply blast
   prefer 2
   apply (rule conjI)
    apply (clarsimp simp: state.defs)
  using mmu_sat_eq_ASID_TTBR0_MEM
   apply blast
  apply (subgoal_tac "ASID b = ASID bb \<and> TTBR0 b = TTBR0 bb")
   apply (simp only: incon_addrs_def)
   apply simp
   apply (rule conjI)
    apply (drule_tac b = b and ba = ba and bc = bc and bb = bb in write_asid_incon_set_rel1; clarsimp)
   apply (rule conjI)
    apply (frule_tac bb = bb and bc = bc and ba = ba and b = b in  write_asid_incon_set_rel'1 ; clarsimp simp: )
   apply (rule conjI)
    apply (clarsimp simp: saturated_def)
   apply (clarsimp simp: snapshot_of_tlb_def)
   apply (subgoal_tac " lookup (tlb_sat_set b \<union> the ` {e \<in> range (pt_walk (ASID bb) (MEM bc) (TTBR0 bb)). \<not> is_fault e}) a v = 
                           lookup (tlb_sat_set b) a v")
    apply clarsimp
    apply (subgoal_tac "tlb_sat_set b = tlb_sat_set s \<and> tlb_incon_set ba = tlb_incon_set t")
     apply clarsimp
    apply (clarsimp simp: mmu_translate_saturated_tlb_unchange mmu_translate_incon_unchange')
  apply (rule lookup_miss_union_equal)
  apply (clarsimp simp: asid_unequal_miss'')
  apply (simp add: write'mem1_eq_ASID_TTBR0)
  done


(* refinement for read theroems *)


lemma mmu_read_sat_const:
  "\<lbrakk> mmu_read_size (va, sz) s = (val, t); saturated (typ_sat_tlb s) \<rbrakk> \<Longrightarrow>
          tlb_sat_set t = tlb_sat_set s"
   apply (clarsimp simp: mmu_read_size_tlb_sat_state_ext_def)
   apply (case_tac "mmu_translate va s", simp)
   apply (subgoal_tac " tlb_sat_set s = tlb_sat_set b ")
    prefer 2
   apply (simp add: mmu_translate_saturated_tlb_unchange)
   apply clarsimp
    apply (clarsimp simp: mem_read1_def)
    apply (clarsimp split: if_split_asm)
       apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
      apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
     apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
    apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
   by (clarsimp simp: raise'exception_def split: option.splits if_split_asm)



lemma  mem_read1_consistent_tlb_rel_non_det:
  " \<lbrakk>mem_read1 (a, sz) s = (val, s');   mem_read1 (a, sz) t = (val, t'); 
               consistent0 (MEM t) (ASID t) (TTBR0 t) (tlb_sat_set t) va; tlb_rel_sat (typ_tlb s) (typ_sat_tlb t)\<rbrakk>
              \<Longrightarrow> consistent0 (MEM t') (ASID t') (TTBR0 t') (tlb_sat_set t') va \<and> tlb_rel_sat (typ_tlb s') (typ_sat_tlb t')"
  apply (rule conjI)
   apply (subgoal_tac "MEM t = MEM t' \<and> ASID t = ASID t' \<and> TTBR0 t = TTBR0 t' \<and> tlb_sat_set t = tlb_sat_set t'")
    apply (clarsimp simp: consistent0_def)
   prefer 2
   apply (subgoal_tac " exception s' =  exception t'")
    apply (drule mem1_read_exception)
    apply (drule mem1_read_exception)
    apply (clarsimp simp: tlb_rel_sat_def)
    apply (clarsimp simp: saturated_def  state.truncate_def)
    apply (cases s', cases t')
    apply clarsimp
   apply (subgoal_tac "MEM s = MEM t \<and> exception s = exception t")
    apply (thin_tac " consistent0 (MEM t) (ASID t) (TTBR0 t) (tlb_sat_set t) va")    
    apply (thin_tac "tlb_rel_sat (typ_tlb s) (typ_sat_tlb t)")
    apply (clarsimp simp: mem_read1_def)
    apply (clarsimp split: if_split_asm)
        apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
       apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
      apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
     subgoal
     by (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
    apply (clarsimp simp: raise'exception_def split: option.splits if_split_asm)
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule mem1_read_exception)
  apply (drule mem1_read_exception)
  apply (cases t, cases t' , clarsimp)
  done


lemma mmu_read_non_det_sat_refine:
  "\<lbrakk> mmu_read_size (va, sz) s = (val, s'); tlb_rel_sat (typ_tlb s) (typ_sat_tlb t);
         consistent (typ_sat_tlb t) va; mmu_read_size (va, sz) t = (val, t') \<rbrakk> \<Longrightarrow>  
                     consistent (typ_sat_tlb t') va \<and>  tlb_rel_sat (typ_tlb s') (typ_sat_tlb t') "
  apply (clarsimp simp: mmu_read_size_tlb_sat_state_ext_def 
                   mmu_read_size_tlb_state_ext_def Let_def)
  apply (cases "mmu_translate va s", cases "mmu_translate va t", clarsimp)
  apply (drule_tac t = t in mmu_translate_sat_refine ; clarsimp simp: Let_def mem_read1_consistent_tlb_rel_non_det)
  done


lemma  mem_read1_consistent_tlb_rel:
  " \<lbrakk>mem_read1 (a, sz) s = (val, s');   mem_read1 (a, sz) t = (val, t'); 
               consistent0 (MEM t) (ASID t) (TTBR0 t) (tlb_sat_set t) va; tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)\<rbrakk>
              \<Longrightarrow> consistent0 (MEM t') (ASID t') (TTBR0 t') (tlb_sat_set t') va \<and> tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t')"
  apply (rule conjI)
   apply (subgoal_tac "MEM t = MEM t' \<and> ASID t = ASID t' \<and> TTBR0 t = TTBR0 t' \<and> tlb_sat_set t = tlb_sat_set t'")
    apply (clarsimp simp: consistent0_def)
   prefer 2
   apply (subgoal_tac " exception s' =  exception t'")
    apply (drule mem1_read_exception)
    apply (drule mem1_read_exception)
    apply (clarsimp simp: tlb_rel_sat_def)
    apply (clarsimp simp: saturated_def  state.truncate_def)
    apply (cases s', cases t')
    apply clarsimp
   apply (subgoal_tac "MEM s = MEM t \<and> exception s = exception t")
    apply (thin_tac " consistent0 (MEM t) (ASID t) (TTBR0 t) (tlb_sat_set t) va")    
    apply (thin_tac "tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)")
    apply (clarsimp simp: mem_read1_def)
    apply (clarsimp split: if_split_asm)
        apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
       apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
      apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
     subgoal
     by (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
    apply (clarsimp simp: raise'exception_def split: option.splits if_split_asm)
   apply (clarsimp simp: tlb_rel_sat_def state.defs)
  apply (drule mem1_read_exception)
  apply (drule mem1_read_exception)
  apply (cases t, cases t' , clarsimp)
  done


lemma mmu_read_det_sat_refine:
  "\<lbrakk> mmu_read_size (va, sz) s = (val, s'); tlb_rel_sat (typ_det_tlb s) (typ_sat_tlb t)  ;
        consistent (typ_sat_tlb t) va; mmu_read_size (va, sz) t = (val, t') \<rbrakk> \<Longrightarrow>  
                     consistent (typ_sat_tlb t') va \<and>  tlb_rel_sat (typ_det_tlb s') (typ_sat_tlb t') "
  apply (clarsimp simp: mmu_read_size_tlb_sat_state_ext_def 
      mmu_read_size_tlb_det_state_ext_def Let_def)
  apply (cases "mmu_translate va s", cases "mmu_translate va t", clarsimp)
  apply (drule_tac t = t in mmu_translate_det_sat_refine ; clarsimp simp: Let_def  mem_read1_consistent_tlb_rel)
  done



lemma  mem_read1_consistent_invar_rel2:
  "\<lbrakk>mem_read1 (a, sz) s = (val, s'); mem_read1 (a, sz) t = (val, t'); 
             va \<notin> iset (tlb_incon_set t); tlb_rel_abs (typ_sat_tlb  s) (typ_incon t)\<rbrakk>
              \<Longrightarrow>  va \<notin> iset (tlb_incon_set t') \<and>  tlb_rel_abs (typ_sat_tlb  s') (typ_incon t')"
  apply (rule conjI)
   apply (subgoal_tac "ASID t = ASID t' \<and> iset (tlb_incon_set t) = iset (tlb_incon_set t')")
    apply clarsimp
   apply (drule mem1_read_exception)
   apply (drule mem1_read_exception)
   apply (cases t, cases t')
   apply clarsimp
  apply (subgoal_tac "exception s' =  exception t'")
   apply (drule mem1_read_exception)
   apply (drule mem1_read_exception)
   apply (clarsimp simp: tlb_rel_abs_def)
   apply (rule conjI)
    apply (clarsimp simp: state.defs)
    apply (cases s', cases t')
    apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp: incon_addrs_def incon_va_set_def ptable_tlb_va_incon_def)
    apply (cases s', cases t')
    apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp:  saturated_def)
   apply (cases s', cases t')
   apply clarsimp
   apply (subgoal_tac "MEM s = MEM t \<and> exception s = exception t")
    apply (thin_tac " va \<notin> iset (tlb_incon_set t)")    
    apply (thin_tac " tlb_rel_abs (typ_sat_tlb s) (typ_incon t)")
    apply (clarsimp simp: mem_read1_def)
    apply (clarsimp split: if_split_asm)
       apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
      apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
     apply (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
    subgoal
    by (clarsimp simp: mem1_def raise'exception_def split: option.splits if_split_asm)
   apply (clarsimp simp: raise'exception_def split: option.splits if_split_asm)
  apply (clarsimp simp: tlb_rel_abs_def state.defs)
  done




end