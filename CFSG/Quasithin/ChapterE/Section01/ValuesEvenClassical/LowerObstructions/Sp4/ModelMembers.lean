module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.Sp4.Family
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.Sp4.ECaseReduction
public import Theory.SpecificGroups.SymplecticFour.ElementaryCoreRankGap

/-!
# Applying the intrinsic symplectic rank gap to actual E-members

The genuine inclusion equivalence Sp₄(q)' ≃ Sp₄(q), for q > 2, identifies
the supplied normal derived-model subgroup with the matrix carrier. Apply
the intrinsic two-core reduction to the actual normal intersection with K.
This excludes every member of the maximum-elementary family from E_(f−1),
with both independent local matrix calculations discharged.

The conditional local-facts API is retained alongside the unconditional
`not_member`. This module imports the two children, never their parent
`Sp4`, so the ambient lower-obstruction assembly can consume it without a cycle.

Source: Aschbacher--Smith, E.1.2, E.1.5 and E.1.14(1), printed pp.210,214.
-/

public section

open Subgroup
open Theory.SpecificGroups.SymplecticFour

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.Sp4Lower

/-- The actual family has no E_(f−1)-member once the two concrete local
calculations are supplied. Final discharge belongs to the model assembly. -/
theorem not_member_of_local_facts
    {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [Finite F]
    (hplane : ElementaryCoreRankGap.PlaneImageBound F)
    (hsl : ElementaryCoreRankGap.RankOneCoreControl F)
    (L : Subgroup G) [L.Normal] {f : ℕ} (hf : 1 < f)
    (hF : Nat.card F = 2 ^ f) (e : L ≃* commutator (Sp F))
    {T A K : Subgroup G} (hA : A ∈ family L f) :
    ¬ IsEMemberAt (f - 1) T A K := by
  let d : L ≃* Sp F := e.trans (EvenTwoRank.derivedEquiv hF (by omega))
  apply not_member_of_coreRankGap L d (by omega) ?_ hA.1 hA.2.2
  intro H _ _ j hj B hB hc hr
  let _ := hB
  exact ElementaryCoreRankGap.le_core_of_rank_lt_of_local_facts
    hplane hsl hF j hj B hc hr

/-- Every maximum elementary subgroup of the normal derived symplectic model
is excluded from E_(f−1), with no additional local model assumptions. -/
theorem not_member
    {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [Finite F]
    (L : Subgroup G) [L.Normal] {f : ℕ} (hf : 1 < f)
    (hF : Nat.card F = 2 ^ f) (e : L ≃* commutator (Sp F))
    {T A K : Subgroup G} (hA : A ∈ family L f) :
    ¬ IsEMemberAt (f - 1) T A K := by
  let d : L ≃* Sp F := e.trans (EvenTwoRank.derivedEquiv hF (by omega))
  apply not_member_of_coreRankGap L d (by omega) ?_ hA.1 hA.2.2
  intro H _ _ j hj B hB hc hr
  let _ := hB
  exact ElementaryCoreRankGap.le_core_of_rank_lt hF j hj B hc hr

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.Sp4Lower
