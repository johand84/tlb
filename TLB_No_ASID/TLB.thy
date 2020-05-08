theory TLB
imports
  "HOL-Word.Word"
  TLB_COMP.MMU_Prg_Logic
  L3_LIBJ.L3_Lib
begin

type_synonym tlb = "tlb_entry set"


(* polymorphic lookup type   *)

datatype 'e lookup_type  =  Miss  | Incon  |  Hit 'e

instantiation lookup_type :: (_) order
begin
  definition
    less_eq_lookup_type: "e \<le> e' \<equiv> e' = Incon \<or> e' = e \<or> e = Miss"

  definition
    less_lookup_type: "e < (e'::'a lookup_type) \<equiv> e \<le> e' \<and> e \<noteq> e'"

  instance
     by intro_classes (auto simp add: less_lookup_type less_eq_lookup_type)
end

class entry_op = 
  fixes range_of  ::  "'a \<Rightarrow> vaddr set"

begin

  
definition
  entry_set :: "'a set \<Rightarrow> vaddr \<Rightarrow> 'a set"
where
  "entry_set t v \<equiv> {e\<in>t. v : range_of e}"

end


definition
  lookup :: "(vaddr \<Rightarrow> 'a set ) \<Rightarrow> vaddr \<Rightarrow> 'a lookup_type"
where
   "lookup t v \<equiv> if t v = {} then Miss
                       else if \<exists>x. t v = {x} then Hit (the_elem (t v))
                       else Incon"

(* access a lookup as 
   "lookup' t v \<equiv> lookup (entry_set t) v"
*)


(* Address translation  *)

fun
  va_to_pa :: "vaddr \<Rightarrow> tlb_entry \<Rightarrow> paddr"
where
  "va_to_pa va (EntrySmall a vba pba fl)   = Addr ((ucast pba << 12) OR (addr_val va AND mask 12))"
| "va_to_pa va (EntrySection a vba pba fl) = Addr ((ucast pba << 20) OR (addr_val va AND mask 20))"



instantiation tlb_entry ::  entry_op
begin
definition
  "range_of (e :: tlb_entry) \<equiv>
                     case e of EntrySmall a vba pba fl   \<Rightarrow> Addr ` {(ucast vba) << 12 ..
                                                                    ((ucast vba) << 12) + (2^12 - 1)}
                             | EntrySection a vba pba fl \<Rightarrow>  Addr ` {(ucast vba) << 20 ..
                                                                      ((ucast vba) << 20) + (2^20 - 1)}"

instance ..
end



(* page table walk interface *)


definition
  pt_walk :: "asid \<Rightarrow> (paddr \<rightharpoonup> 8 word) \<Rightarrow> paddr \<Rightarrow> vaddr \<Rightarrow>  tlb_entry option"
where
  "pt_walk a hp rt v \<equiv>
      case get_pde hp rt v
       of None                 \<Rightarrow> None
       | Some InvalidPDE       \<Rightarrow> None
       | Some ReservedPDE      \<Rightarrow> None
       | Some (SectionPDE bpa perms) \<Rightarrow> Some (EntrySection (tag_conv a (to_tlb_flags perms))  (ucast (addr_val v >> 20) :: 12 word)
                                      ((word_extract 31 20 (addr_val bpa)):: 12 word) 
                                       (to_tlb_flags perms))
       | Some (PageTablePDE p) \<Rightarrow>
               (case get_pte hp p v
                 of None                     \<Rightarrow> None
                 |  Some InvalidPTE          \<Rightarrow> None
                 |  Some (SmallPagePTE bpa perms) \<Rightarrow> Some(EntrySmall (tag_conv a (to_tlb_flags perms)) (ucast (addr_val v >> 12) :: 20 word)
                                                     ((word_extract 31 12 (addr_val bpa)):: 20 word) 
                                                     (to_tlb_flags perms)))"

(* Flush operations *)

datatype flush_type = FlushTLB
                    | Flushvarange "vaddr set"
                    | FlushASID asid 
                    | FlushASIDvarange  asid "vaddr set" 

definition
  flush_tlb :: "tlb  \<Rightarrow> tlb"
where
  "flush_tlb t  \<equiv> {}"

definition
  flush_tlb_vset :: "tlb \<Rightarrow> vaddr set \<Rightarrow> tlb"
where
  "flush_tlb_vset t vset =  t - (\<Union>v\<in>vset. {e \<in> t. v \<in> range_of e})"

(* consistency polymorphic defs *)

definition
  consistent0 :: "(vaddr \<Rightarrow> 'b lookup_type) \<Rightarrow> (vaddr \<Rightarrow> 'b option) \<Rightarrow> vaddr \<Rightarrow> bool"
where
  "consistent0  lukup ptwalk  va \<equiv>
            (lukup va = Hit (the (ptwalk va)) \<and> \<not>is_fault (ptwalk va)) \<or>  lukup va = Miss"



lemma consistent_not_Incon_imp:
  "consistent0  lukup ptwalk va \<Longrightarrow>
     lukup va \<noteq> Incon \<and> (\<forall>e. lukup va = Hit e \<longrightarrow> e = the (ptwalk va) \<and> ptwalk va \<noteq> None)"
  apply (clarsimp simp: consistent0_def is_fault_def) 
  by force

lemma consistent_not_Incon':
  "consistent0  lukup ptwalk va =
  (lukup va \<noteq> Incon \<and> (\<forall>e. lukup va = Hit e \<longrightarrow> e = the (ptwalk va) \<and> ptwalk va \<noteq> None))"
  by ((cases "lukup va"); simp add: consistent0_def is_fault_def)
  


end
