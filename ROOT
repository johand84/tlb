chapter AFP

session Word_Lib (AFP) in "Word_Lib" = "HOL-Word" +
  options [timeout = 300]
  sessions "HOL-Library"
  theories
    Word_Lemmas_32
    Word_Lemmas_64
  document_files
    "root.tex"

chapter TLB


session L3_LIBJ = Word_Lib +
  theories
    "L3_Library/L3_Lib"


session PTABLE_TLBJ = L3_LIBJ +
  theories
    "Page_Tables/PageTable_seL4"
	"Logic/MMU_Prg_Logic"



session TLBJ = PTABLE_TLBJ +
  theories
    "TLB_No_ASID/Simp_Lemmas"
    "TLB_No_ASID/ARM_Monadic"


session TLB_ASID_REFJ = TLBJ +
  theories
    "TLB_ASID/Simp_Lemmas_ASIDs"


session TLB_PDC_REFJ = TLB_ASID_REFJ +
  theories
    "TLB_PDC/Paper_Defs_machine_Inter"
    "Logic/Page_Table_Ops"

session MMU_DEFS = TLB_ASID_REFJ +
  theories
    "TLB_PDC/MMU_Instants_TLB_PDC"

session TLB_COMP = MMU_DEFS +
  theories
    "Logic/Logic"


(*session CASE_STUDYJJ = TLB_ASID_REFJ +
  theories
    "Case_Study/Page_Table_Ops"

*)
