module

public import CFSG.Quasithin.Chapter15.Section01.CaseI.ComponentModels
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.Components

/-! The source 14.1.6 adapter for the literal 15.1.20 component prefix.

This extension retains the global local-family hypothesis required by the
existing `local_component_le_partner` producer. -/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.ComponentModels
open Chapter1 Chapter15.Section03 Chapter15.Section03.InitialSource
universe u
variable {G : Type u} [Group G] [Finite G]

/--
The source 14.1.6 argument proving `L not≤ M`, with all original subgroup
maps explicit.  The local-family premise is kept because it is the precise
hypothesis used by the existing producer `local_component_le_partner`.
-/
theorem source20_not_le_M_of_global_local
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc G1 MZ L : Subgroup G}
    (hunique : maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hMZ : MZ = G1 ⊓ Mc)
    (hLglobal : L ∈ Chapter1.L G (T : Subgroup G))
    (hLG1 : L ≤ G1)
    (hLout : ¬ L ≤ MZ) :
    ¬ L ≤ M := by
  intro hLM
  have hLMc : L ≤ Mc :=
    local_component_le_partner hA hC hG T hempty hunique hLglobal
  apply hLout
  rw [hMZ]
  exact le_inf hLG1 hLMc


end CFSG.Quasithin.Chapter15.Section01.ComponentModels
