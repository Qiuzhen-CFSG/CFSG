module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Inner

/-!
# The concrete A₅ factor for the J₂ fixer calculation

The subgroup below is the simple direct factor in the checked centralizer
`C_J₂(a) ≃ E₄ × A₅`, mapped back into the unchanged degree-100 carrier.
Its embedding is fixed by `J2Inner.a_centralizer_equiv`; the checked words
are exposed by `J2Inner.a_centralizer_equiv_symm_simple`.

Source: Aschbacher–Smith, 16.1.5(8) and the J₂ case of 16.3.5,
combined manuscript of 1 March 2004, printed pp.1172 and 1178–1179.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Janko
open Subgroup
open Sporadic.LeechRelated.J2
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims

/-- The actual simple direct factor of the noncentral representative centralizer. -/
noncomputable def representativeA5 : Subgroup Carrier :=
  ((⊥ : Subgroup E4).prod (⊤ : Subgroup A5)).map
    ((centralizer ({GeneratorPair.a} : Set Carrier)).subtype.comp
      J2Inner.a_centralizer_equiv.symm.toMonoidHom)

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Janko
