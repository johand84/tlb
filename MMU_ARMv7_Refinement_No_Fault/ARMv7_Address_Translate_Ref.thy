theory ARMv7_Address_Translate_Ref

imports  ARMv7_TLB_Ref_Func

begin               



instantiation tlb_state_ext :: (type) mmu   
begin
  definition   
  "(mmu_translate v :: ('a tlb_state_scheme \<Rightarrow> _))
  = do {
  update_state (\<lambda>s. s\<lparr> tlb_set := tlb_set s - tlb_evict (typ_tlb s) \<rparr>);
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     tlb   <- read_state tlb_set;
          case lookup tlb asid (addr_val v) of
            Hit entry \<Rightarrow> if is_fault entry
              then raise'exception(PAGE_FAULT ''more info'') 
                else return (Addr (va_to_pa (addr_val v) entry))
          | Miss \<Rightarrow> let entry = pt_walk asid mem ttbr0 v in
              if is_fault entry
                then raise'exception (PAGE_FAULT ''more info'')
                  else do {
                    update_state (\<lambda>s. s\<lparr> tlb_set := tlb \<union> {entry} \<rparr>);
                    return (Addr (va_to_pa (addr_val v) entry))
                  }
          | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
   }"

thm mmu_translate_tlb_state_ext_def
(* print_context *)                      
  instance ..
end


instantiation tlb_det_state_ext :: (type) mmu    
begin
definition   
 "(mmu_translate v :: ('a tlb_det_state_scheme \<Rightarrow> _))
  = do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     tlb   <- read_state tlb_det_set;
          case lookup tlb asid (addr_val v) of
            Hit entry \<Rightarrow> if is_fault entry
              then raise'exception(PAGE_FAULT ''more info'') 
                else return (Addr (va_to_pa (addr_val v) entry))
          | Miss \<Rightarrow> let entry = pt_walk asid mem ttbr0 v in
              if is_fault entry
                then raise'exception (PAGE_FAULT ''more info'')
                  else do {
                    update_state (\<lambda>s. s\<lparr> tlb_det_set := tlb \<union> {entry} \<rparr>);
                    return (Addr (va_to_pa (addr_val v) entry))
                  }
          | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
   }"

  instance ..
end



instantiation tlb_sat_no_flt_state_ext :: (type) mmu    
begin
definition   
 "(mmu_translate v :: ('a tlb_sat_no_flt_state_scheme \<Rightarrow> _))
 = do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     let all_non_fault_entries = {e\<in>pt_walk asid mem ttbr0 ` UNIV. \<not>is_fault e};
     tlb0   <- read_state tlb_sat_no_flt_set;
     let tlb = tlb0 \<union> all_non_fault_entries;  (* there can be fault entries in the tlb0, and of there are , they should not be 
                                                  in the all non fault entries *)
     update_state (\<lambda>s. s\<lparr> tlb_sat_no_flt_set := tlb \<rparr>);
          case lookup tlb asid (addr_val v) of
            Hit entry \<Rightarrow> if is_fault entry 
              then raise'exception (PAGE_FAULT ''more info'')    (* it can be possible because there can be a fault entry in the tlb0 already *)
                else return (Addr (va_to_pa (addr_val v) entry))
          | Miss \<Rightarrow> raise'exception (PAGE_FAULT ''more info'')
          | Incon \<Rightarrow> raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
   }" 
   
  instance ..
end


(* should we use history or not, for translation *)


instantiation tlb_incon_state'_ext :: (type) mmu    
begin
definition   
 "(mmu_translate v :: ('a tlb_incon_state'_scheme \<Rightarrow> _))
  = do {
     mem   <- read_state MEM;
     asid  <- read_state ASID;
     ttbr0 <- read_state TTBR0;
     tlb_incon_set <- read_state tlb_incon_set';
     if (asid , v) \<in> incon_set tlb_incon_set
       then raise'exception (IMPLEMENTATION_DEFINED ''set on fire'')
       else let entry = pt_walk asid mem ttbr0 v in 
             if is_fault entry
              then raise'exception (PAGE_FAULT ''more info'')
              else return (Addr (va_to_pa (addr_val v) entry))
    }"

  instance ..
end


lemma lookup_miss_tlb_subset1:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) (addr_val va) = Miss ; \<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) ;
     mmu_translate va s = (pa, s') \<rbrakk> \<Longrightarrow> 
              tlb_det_set s' = tlb_det_set s \<union> {pt_walk (ASID s) (MEM s) (TTBR0 s) va} "
  by (clarsimp simp add: mmu_translate_tlb_det_state_ext_def Let_def)
  

lemma  lookup_miss_tlb_subset2:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) (addr_val va) = Miss ; is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va) ;
     mmu_translate va s = (pa, s') \<rbrakk> \<Longrightarrow> 
              tlb_det_set s' = tlb_det_set s "
  apply (clarsimp simp add: mmu_translate_tlb_det_state_ext_def Let_def)
  apply (clarsimp simp:raise'exception_def split: if_split_asm)
done
  
lemma lookup_miss_tlb_subset:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) (addr_val va) = Miss ; mmu_translate va s = (pa, s')\<rbrakk> \<Longrightarrow> 
           tlb_det_set s' = tlb_det_set s  \<or> tlb_det_set s' = tlb_det_set s \<union> {pt_walk (ASID s) (MEM s) (TTBR0 s) va} "
  apply (cases "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)" )
   apply (drule (2) lookup_miss_tlb_subset2 , clarsimp)
  apply (drule (2) lookup_miss_tlb_subset1 , clarsimp)
done 

lemma lookup_incon_tlb_equal:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) (addr_val va) = Incon ; mmu_translate va s = (pa, s')  \<rbrakk> \<Longrightarrow> 
        tlb_det_set s' = tlb_det_set s"
  by (clarsimp simp add: mmu_translate_tlb_det_state_ext_def Let_def raise'exception_def split:if_split_asm)
 

lemma lookup_hit_tlb_equal:
  "\<lbrakk>lookup (tlb_det_set s) (ASID s) (addr_val va) = Hit x ; mmu_translate va s = (pa, s') \<rbrakk> \<Longrightarrow>  tlb_det_set s' = tlb_det_set s "
  by (clarsimp simp add: mmu_translate_tlb_det_state_ext_def Let_def raise'exception_def split:if_split_asm)

(* important *)
lemma mmu_translate_tlbs_rel:
  "\<lbrakk> mmu_translate va s = (pa, s') \<rbrakk> \<Longrightarrow>
       tlb_det_set s' = tlb_det_set s \<or>  tlb_det_set s' = tlb_det_set s \<union> {pt_walk (ASID s) (MEM s) (TTBR0 s) va} "
  apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va)")
    apply (drule (2)lookup_miss_tlb_subset)
   apply (rule disjI1)
   apply (drule (2) lookup_incon_tlb_equal)
  apply (rule disjI1)
  apply (drule (2) lookup_hit_tlb_equal)
done  


lemma mmu_det_rel:
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> tlb_det_set := tlb_det_set s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def Let_def  split:lookup_type.splits)
    apply (clarsimp simp: raise'exception_def split:if_split_asm)+
done


lemma mmu_rel:
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> tlb_set := tlb_set s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def Let_def  split:lookup_type.splits)
    apply (clarsimp simp: raise'exception_def split:if_split_asm)+
done


lemma mmu_det_eq_ASID_TTBR0_MEM:
  "\<lbrakk> mmu_translate va (s::'a tlb_det_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>
                      MEM s = MEM s'"
   apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def Let_def)
   apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va) ")
   by (clarsimp simp:Let_def raise'exception_def split: if_split_asm)+
  


lemma mmu_eq_ASID_TTBR0_MEM:
  "\<lbrakk> mmu_translate va (s::'a tlb_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>
                      MEM s = MEM s'"
   apply (clarsimp simp: mmu_translate_tlb_state_ext_def Let_def)
   apply (cases "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va) ")
   by (clarsimp simp:Let_def raise'exception_def split: if_split_asm)+
  

(* add the mmu_translate refinements here *)



lemma  mmu_translate_det_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_det_tlb t) va;  tlb_rel (typ_det_tlb s) (typ_det_tlb t)\<rbrakk> \<Longrightarrow>
     let (pa', t') = mmu_translate va t
         in pa' = pa \<and> consistent (typ_det_tlb t') va \<and> tlb_rel (typ_det_tlb s') (typ_det_tlb t')"
  apply (frule (1) tlb_rel_consistent , clarsimp)
  apply (frule tlb_relD , clarsimp)
  apply (subgoal_tac "lookup (tlb_det_set s) (ASID s) (addr_val va) \<le> lookup (tlb_det_set t) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: tlb_mono)
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def split_def Let_def split: if_split_asm)
  apply (cases "lookup (tlb_det_set t) (ASID s) (addr_val va)")
    apply clarsimp
    apply (simp add: Let_def raise'exception_def typ_det_tlb_def state.defs tlb_rel_def split: if_split_asm)
     apply (cases s, cases t, clarsimp)
    apply (cases s, cases t)
    apply (clarsimp simp: no_faults_def)
    apply fastforce
   apply (simp add: consistent0_def )
  apply clarsimp
  apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va)"; clarsimp)
   apply (simp add: consistent0_def Let_def tlb_rel_def no_faults_def
                    lookup_in_tlb split: if_split_asm)
   apply clarsimp
   apply (drule lookup_in_tlb)
   apply (simp add: typ_det_tlb_def state.defs)
  apply (clarsimp split: if_split_asm simp: tlb_rel_def no_faults_def)
  using lookup_in_tlb apply blast
done


(* refinement between eviction and deterministic TLB lookups *)
lemma  mmu_translate_non_det_det_refine:
  "\<lbrakk> mmu_translate va s = (pa, s');  consistent (typ_det_tlb t) va; tlb_rel (typ_tlb s) (typ_det_tlb t)  \<rbrakk> \<Longrightarrow>
    let (pa', t') = mmu_translate va t
     in pa' = pa  \<and> consistent (typ_det_tlb t') va \<and> tlb_rel (typ_tlb s') (typ_det_tlb t')"
  apply (frule (1) tlb_rel_consistent , clarsimp)
  apply (frule tlb_relD , clarsimp)
  apply (subgoal_tac "tlb_set s - tlb_evict (typ_tlb s) \<subseteq> tlb_set s")
   prefer 2
   apply blast
  apply (subgoal_tac "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va) \<le> lookup (tlb_det_set t) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: tlb_mono)
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def mmu_translate_tlb_det_state_ext_def split_def Let_def split: if_split_asm)
  apply (cases "lookup (tlb_det_set t) (ASID s) (addr_val va)")
    apply clarsimp
    apply (simp add: Let_def raise'exception_def typ_det_tlb_def typ_tlb_def state.defs tlb_rel_def split: if_split_asm)
      apply (cases s, cases t, clarsimp simp: no_faults_def)
      apply fastforce
     apply (cases s, cases t ,clarsimp simp: no_faults_def)
     apply fastforce
    apply (cases s, cases t, clarsimp simp: no_faults_def)
    apply fastforce
   apply (simp add: consistent0_def )
  apply clarsimp
  apply (cases "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va)"; clarsimp)
   apply (simp add: consistent0_def Let_def tlb_rel_def no_faults_def
                     lookup_in_tlb split: if_split_asm)
   apply clarsimp
   apply (drule lookup_in_tlb)
   apply (simp add: typ_det_tlb_def state.defs)
  apply (clarsimp split: if_split_asm simp: tlb_rel_def typ_tlb_def typ_det_tlb_def state.defs no_faults_def)
   using lookup_in_tlb apply blast
  using lookup_in_tlb apply blast
done



lemma mmu_translate_det_sat_no_flt_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_no_flt_tlb t) va; tlb_rel_sat_no_flt (typ_det_tlb s) (typ_sat_no_flt_tlb t)  \<rbrakk> \<Longrightarrow>
         let (pa', t') = mmu_translate va t
         in pa' = pa \<and> consistent (typ_sat_no_flt_tlb t') va \<and> tlb_rel_sat_no_flt (typ_det_tlb s') (typ_sat_no_flt_tlb t')"
  apply (frule (1) tlb_rel_sat_no_flt_consistent , clarsimp)
  apply (frule tlb_rel_no_flt_satD , clarsimp)
  apply (subgoal_tac "lookup (tlb_det_set s) (ASID s) (addr_val va) \<le> lookup (tlb_sat_no_flt_set t \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: saturated_no_flt_def sup.absorb1 tlb_mono tlb_rel_sat_no_flt_def)
  apply (clarsimp simp: mmu_translate_tlb_det_state_ext_def  mmu_translate_tlb_sat_no_flt_state_ext_def split_def Let_def)
  apply (subgoal_tac "tlb_sat_no_flt_set t = tlb_sat_no_flt_set t \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
   prefer 2
   apply (fastforce simp: tlb_rel_sat_no_flt_def saturated_no_flt_def)
  apply (cases "lookup (tlb_sat_no_flt_set t \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val va)")
    apply (clarsimp simp: tlb_rel_sat_no_flt_def Let_def)
    apply (subgoal_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
     apply (clarsimp simp: raise'exception_def  saturated_no_flt_def state.defs split: if_split_asm)
    apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)
    apply force
   apply (clarsimp simp: consistent0_def)
  apply clarsimp
  apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
   prefer 2
   apply (clarsimp simp: consistent0_def)
  apply (cases "lookup (tlb_det_set s) (ASID s) (addr_val va)"; clarsimp)
   apply (clarsimp simp: Let_def)
   apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
    prefer 2
    apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def lookup_in_tlb)
   apply (clarsimp simp: tlb_rel_sat_no_flt_def typ_sat_no_flt_tlb_def typ_det_tlb_def state.defs lookup_in_tlb raise'exception_def split: if_split_asm)
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   apply clarsimp
  apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def lookup_in_tlb)
done




lemma mmu_translate_sat_no_flt_refine:
  "\<lbrakk> mmu_translate va s = (pa, s'); consistent (typ_sat_no_flt_tlb t) va; tlb_rel_sat_no_flt (typ_tlb s) (typ_sat_no_flt_tlb t)  \<rbrakk> \<Longrightarrow>
         let (pa', t') = mmu_translate va t
         in pa' = pa \<and> consistent (typ_sat_no_flt_tlb t') va \<and> tlb_rel_sat_no_flt (typ_tlb s') (typ_sat_no_flt_tlb t')"
  apply (frule (1) tlb_rel_sat_no_flt_consistent , clarsimp)
  apply (frule tlb_rel_no_flt_satD , clarsimp)
  apply (subgoal_tac "tlb_set s - tlb_evict (typ_tlb s) \<subseteq> tlb_set s")
   prefer 2
   apply blast
  apply (subgoal_tac "lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va) \<le> lookup (tlb_sat_no_flt_set t \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val va)")
   prefer 2
   apply (simp add: saturated_no_flt_def sup.absorb1 tlb_mono tlb_rel_sat_no_flt_def)
  apply (clarsimp simp: mmu_translate_tlb_state_ext_def  mmu_translate_tlb_sat_no_flt_state_ext_def split_def Let_def)
  apply (subgoal_tac "tlb_sat_no_flt_set t = tlb_sat_no_flt_set t \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
   prefer 2
   apply (fastforce simp: tlb_rel_sat_no_flt_def saturated_no_flt_def)
  apply (cases "lookup (tlb_sat_no_flt_set t \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}) (ASID s) (addr_val va)")
    apply (clarsimp simp: tlb_rel_sat_no_flt_def Let_def)
    apply (subgoal_tac "is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
     apply (clarsimp simp: raise'exception_def  saturated_no_flt_def state.defs split: if_split_asm ; force)
    apply (clarsimp simp: lookup_def entry_set_def entry_range_asid_tags_def split: if_split_asm)
    apply force
   apply (clarsimp simp: consistent0_def)
  apply clarsimp
  apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
   prefer 2
   apply (clarsimp simp: consistent0_def)
  apply (cases " lookup (tlb_set s - tlb_evict (typ_tlb s)) (ASID s) (addr_val va)"; clarsimp)
   apply (clarsimp simp: Let_def)
   apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
    prefer 2
    apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def lookup_in_tlb)
   apply (clarsimp simp: tlb_rel_sat_no_flt_def typ_sat_no_flt_tlb_def typ_tlb_def state.defs lookup_in_tlb raise'exception_def split: if_split_asm , force)
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   apply (clarsimp simp:  tlb_rel_sat_no_flt_def  typ_tlb_def state.defs , force)
  apply (clarsimp simp: tlb_rel_sat_no_flt_def no_faults_def lookup_in_tlb)
done



(* have refinement between flt and incon *)


lemma mmu_translate_sa_consistent':
  "\<lbrakk> mmu_translate va s = (pa, s');  consistent (typ_sat_no_flt_tlb s) va ; saturated_no_flt (typ_sat_no_flt_tlb s) ; 
                no_faults (tlb_sat_no_flt_set s)\<rbrakk>  \<Longrightarrow>  
                   consistent (typ_sat_no_flt_tlb s') va"
  apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e \<in> range (pt_walk (ASID s) (MEM s) (TTBR0 s)). \<not> is_fault e}")
   prefer 2
   apply (fastforce simp: saturated_no_flt_def)
  apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def Let_def  split:lookup_type.splits)
    apply (clarsimp simp: raise'exception_def split:if_split_asm)+
done


lemma mmu_sat_rel':
  "\<lbrakk> mmu_translate va s = (p, s') \<rbrakk>  \<Longrightarrow> s' = s \<lparr> tlb_sat_no_flt_set := tlb_sat_no_flt_set s' , exception:= exception s' \<rparr>"
  apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def Let_def  split:lookup_type.splits)
    apply (clarsimp simp: raise'exception_def split:if_split_asm)+
done


lemma mmu_translate_abs_rel':
  "\<lbrakk>  mmu_translate va t = (pa', t')\<rbrakk>  \<Longrightarrow> (t'::'a tlb_incon_state'_scheme) = t\<lparr>exception := exception t'\<rparr>"
  by (clarsimp simp: mmu_translate_tlb_incon_state'_ext_def Let_def raise'exception_def split: if_split_asm)


lemma mmu_translate_sat_TLB_union':
  "mmu_translate v s = (p,t) \<Longrightarrow> 
      tlb_sat_no_flt_set t = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}"
  apply (clarsimp simp:  mmu_translate_tlb_sat_no_flt_state_ext_def Let_def)
  apply (cases "lookup (tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val v)")
    apply (clarsimp simp:raise'exception_def split:if_split_asm) +
done


lemma mmu_sat_no_flt_eq_ASID_TTBR0_MEM:
  "\<lbrakk> mmu_translate va (s::'a tlb_sat_no_flt_state_scheme) = (pa , s') \<rbrakk>  \<Longrightarrow> ASID s = ASID s' \<and> TTBR0 s = TTBR0 s' \<and>
                     MEM s = MEM s'"
  apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def Let_def)
  apply (cases "lookup (tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val va) ")
    by (clarsimp simp:raise'exception_def split: if_split_asm)+


lemma not_member_incon_consistent':
  "\<lbrakk>(ASID s ,va) \<notin>  asid_va_incon_tlb_mem (typ_sat_no_flt_tlb s) \<rbrakk> \<Longrightarrow> 
         consistent (typ_sat_no_flt_tlb s) va"
  apply (clarsimp simp: asid_va_incon_tlb_mem_def asid_va_incon_def asid_va_hit_incon_def)
  apply (clarsimp simp: lookup_def consistent0_def split: if_split_asm)
  done




lemma tlb_snapshot_sat_same  [simp]:
  "\<lbrakk> mmu_translate va s = (pa, s'); 
       saturated_no_flt  (typ_sat_no_flt_tlb s) ; no_faults (tlb_sat_no_flt_set s) \<rbrakk> \<Longrightarrow> 
                  snapshot_of_tlb (tlb_sat_no_flt_set s') =  snapshot_of_tlb (tlb_sat_no_flt_set s)"
  apply (subgoal_tac "tlb_sat_no_flt_set s' = tlb_sat_no_flt_set s")
    apply (clarsimp simp: snapshot_of_tlb_def)
   using mmu_translate_sat_TLB_union' sat_state_tlb' by fastforce
  


lemma tlb_snapshot_sat_same':
  "\<lbrakk>  mmu_translate va t = (pa', t')  \<rbrakk> \<Longrightarrow> 
           tlb_snapshot (tlb_incon_set' t') =  tlb_snapshot (tlb_incon_set' t)"
  by (clarsimp simp: mmu_translate_tlb_incon_state'_ext_def raise'exception_def Let_def split:if_split_asm)
  

lemma tlb_rel_abs_consistent' [simp]:
  "\<lbrakk>(ASID t, va) \<notin> incon_set (tlb_incon_set' t) ;   tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk>  \<Longrightarrow> 
           consistent (typ_sat_no_flt_tlb s) va " 
  apply (rule not_member_incon_consistent' ; clarsimp)
  apply (clarsimp simp: tlb_rel_abs'_def)
  apply (subgoal_tac "ASID s = ASID t" , simp)
   apply blast
  apply (cases s , cases t , clarsimp simp: state.defs)
done

lemma mmu_translate_sat_abs_refine':
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
          (ASID t,  va) \<notin> incon_set (tlb_incon_set' t) ; tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> 
            tlb_rel_abs'  (typ_sat_no_flt_tlb s') (typ_incon' t')"
  apply (frule_tac s = s in tlb_rel_abs_consistent' ; clarsimp )
   apply (frule tlb_rel'_absD , clarsimp)
  apply (frule_tac mmu_translate_sa_consistent' ; clarsimp simp: tlb_rel_abs'_def asid_va_incon_tlb_mem_def asid_va_hit_incon_def)
  (* TLB is not changing as s is already saturated *)
  apply (subgoal_tac "s' = s\<lparr>exception := exception s'\<rparr> \<and> t' = t\<lparr>exception := exception t'\<rparr>")
   apply (subgoal_tac "exception t' = exception s'")
    apply (cases t, cases t, cases s, cases s', clarsimp simp: state.defs saturated_no_flt_def)
   prefer 2
   apply (frule mmu_translate_abs_rel', clarsimp)
   apply (subgoal_tac "tlb_sat_no_flt_set s' = tlb_sat_no_flt_set s")
    apply (drule mmu_sat_rel', clarsimp)
   using mmu_translate_sat_TLB_union' sat_state_tlb' apply fastforce
  apply (subgoal_tac "tlb_sat_no_flt_set s' = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e} \<and> ASID s' = ASID s  \<and> 
                                              MEM s' = MEM s \<and> TTBR0 s' = TTBR0 s")
   apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def split_def Let_def)
   apply (cases "lookup (tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val va)")
     apply clarsimp
     apply (frule lookup_saturated_no_flt_miss_is_fault)
     apply (clarsimp simp: mmu_translate_tlb_incon_state'_ext_def raise'exception_def split:if_split_asm)
    apply (clarsimp simp: consistent0_def)
   apply clarsimp
   apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
    prefer 2
    apply (clarsimp simp: consistent0_def)
   apply clarsimp
   apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
    prefer 2
    apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
     prefer 2
     apply (fastforce simp: saturated_no_flt_def)
    apply clarsimp
    apply (simp only: no_faults_def lookup_in_tlb)
   apply clarsimp
  apply (clarsimp simp: mmu_translate_tlb_incon_state'_ext_def Let_def)
  apply (clarsimp simp: mmu_translate_sat_TLB_union' mmu_sat_no_flt_eq_ASID_TTBR0_MEM)
done


lemma mmu_translate_sat_abs_refine_pa':
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
          (ASID t, va) \<notin> incon_set (tlb_incon_set' t) ; tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> 
                                          pa = pa'"
  apply (frule_tac s = s in tlb_rel_abs_consistent' ; clarsimp )
  apply (frule tlb_rel'_absD , clarsimp)
  apply (clarsimp simp: mmu_translate_tlb_incon_state'_ext_def  Let_def)
  apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def split_def Let_def)
  apply (cases "lookup (tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val va)")
    apply clarsimp
    apply (frule lookup_saturated_no_flt_miss_is_fault)
    apply (clarsimp simp: raise'exception_def split:if_split_asm)
   apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
    prefer 2
    apply (fastforce simp: saturated_no_flt_def)
   apply clarsimp
   apply (clarsimp simp: consistent0_def)
  apply clarsimp
  apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
   prefer 2
   apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
    prefer 2
    apply (fastforce simp: saturated_no_flt_def)
   apply (clarsimp simp: consistent0_def)
  apply clarsimp
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
    prefer 2
    apply (fastforce simp: saturated_no_flt_def)
   apply clarsimp
   apply (simp only: no_faults_def lookup_in_tlb)
  apply clarsimp
 done



lemma mmu_translate_sat_abs_refine_consistency:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
          (ASID t, va) \<notin> incon_set (tlb_incon_set' t) ; tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> 
                                 (ASID t',  va) \<notin> incon_set (tlb_incon_set' t')"
  apply (frule_tac s = s in tlb_rel_abs_consistent' ; clarsimp )
  apply (frule tlb_rel'_absD , clarsimp)
  apply (clarsimp simp: mmu_translate_tlb_incon_state'_ext_def  Let_def)
  apply (clarsimp simp: mmu_translate_tlb_sat_no_flt_state_ext_def split_def Let_def)
  apply (cases "lookup (tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}) (ASID s) (addr_val va)")
    apply clarsimp
    apply (frule lookup_saturated_no_flt_miss_is_fault)
    apply (clarsimp simp: raise'exception_def split:if_split_asm)
   apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
    prefer 2
    apply (fastforce simp: saturated_no_flt_def)
   apply clarsimp
   apply (clarsimp simp: consistent0_def)
  apply clarsimp
  apply (subgoal_tac "x3 = pt_walk (ASID s) (MEM s) (TTBR0 s) va")
   prefer 2
   apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
    prefer 2
    apply (fastforce simp: saturated_no_flt_def)
   apply (clarsimp simp: consistent0_def)
  apply clarsimp
  apply (subgoal_tac "\<not>is_fault (pt_walk (ASID s) (MEM s) (TTBR0 s) va)")
   prefer 2
   apply (subgoal_tac "tlb_sat_no_flt_set s = tlb_sat_no_flt_set s \<union> {e\<in>pt_walk (ASID s) (MEM s) (TTBR0 s) ` UNIV. \<not> is_fault e}")
    prefer 2
    apply (fastforce simp: saturated_no_flt_def)
   apply clarsimp
   apply (simp only: no_faults_def lookup_in_tlb)
  apply clarsimp
 done



lemma mmu_translate_sat_no_flt_abs_refine:
  "\<lbrakk> mmu_translate va s = (pa, s');  mmu_translate va t = (pa', t') ;
          (ASID t,  va) \<notin> incon_set(tlb_incon_set' t) ; tlb_rel_abs' (typ_sat_no_flt_tlb s) (typ_incon' t) \<rbrakk> \<Longrightarrow> 
                              pa = pa' \<and>  (ASID t',  va) \<notin> incon_set(tlb_incon_set' t') \<and> tlb_rel_abs'  (typ_sat_no_flt_tlb s') (typ_incon' t')"
  by (clarsimp simp: mmu_translate_sat_abs_refine_pa' mmu_translate_sat_abs_refine' mmu_translate_sat_abs_refine_consistency)

end