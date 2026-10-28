module
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.Configurations
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Core

/-!
# Witnesses for the ambient reciprocal escape

The witness predicate retains every clause of the original normalized
PushingUpCase, including the representative formula for the core quotient.
The escape conclusion adds the literal preimage of F*(H/O₂(H)); the
reciprocal conclusion records the actual contrary branch with C.2.3 in M.
These are output predicates, not additional source hypotheses.

Source: Aschbacher--Smith, 4.2.5--10, printed pp.609--610.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl Chapter1.RadicalExclusions
variable {G : Type*} [Group G] [Finite G]

/-- All clauses of PushingUpCase at a fixed triple of witnesses. -/
@[expose] def Witness (L V A J H W : Subgroup G) : Prop :=
    J ∈ muStar (normalizer (L : Set G)) L
      (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
    PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
    H ⊓ normalizer (L : Set G) < H ∧ V ≤ J.pCoreIn 2 ∧
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let MH := H ⊓ normalizer (L : Set G)
    let X := ChapterA.Section04.twoSectionCentralizer (conjugateSpanBy LH MH) H
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H MH LH (J.pCoreIn 2) W ∧
    (L : Set G) = (LH : Set G) * (L.pCoreIn 2 : Set G) ∧
    (LH.subgroupOf MH).Normal ∧
    V = ⁅V,LH⁆ ∧ V ≤ LH ∧
    (∃ e : (LH ⧸ pCore 2 LH) ≃* (L ⧸ pCore 2 L),
      ∀ i : LH, e (QuotientGroup.mk' (pCore 2 LH) i) =
        QuotientGroup.mk' (pCore 2 L)
          (inclusion ((map_subtype_le _).trans inf_le_left) i)) ∧
    pPrimeCore 2 H = ⊥ ∧ IsPRadical 2 ((J.pCoreIn 2).subgroupOf H) ∧
    ChapterC.IsSylowInNormalClosure (J.pCoreIn 2) MH ∧
    generalizedFitting X = pCore 2 X ∧
    (∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = J.pCoreIn 2) ∧
    Nat.card V ≤ Nat.card W ∧
    ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
      V.map (MulAut.conj (c : G)).toMonoidHom ≤ W

/-- The required escape, with the same witnesses as the original configuration. -/
@[expose] def EscapeCase (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H

/-- The contrary branch after 4.2.6--8, with the original maps and relative groups. -/
@[expose] def ReciprocalCase (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ((generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H →
      let M := normalizer (L : Set G)
      (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype = L ∧
      (L.subgroupOf H).IsCComponent ∧
      normalizer (L.subgroupOf H : Set H) = M.subgroupOf H ∧
      (M.subgroupOf H).index = 2 ∧
      conjugateSpanBy L H ≤ H ⊓ M ∧
      normalizer (conjugateSpanBy L H : Set G) = H ∧
      H.pCoreIn 2 = (H ⊓ M).pCoreIn 2 ∧
      PushingUpSetup KnownSimple.IsKnownSimple M (H.pCoreIn 2) (H ⊓ M) ∧
      M.pCoreIn 2 ≤ H.pCoreIn 2 ∧
      ¬ (generalizedFitting (M ⧸ pCore 2 M)).comap
        (QuotientGroup.mk' (pCore 2 M)) ≤ H.subgroupOf M)

end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
