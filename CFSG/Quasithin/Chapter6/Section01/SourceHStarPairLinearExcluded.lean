module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarLinearExcluded
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PairedLift
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedGenerationSource

/-!
# The paired nonbinary linear H-star obstruction

The original generation-one hypothesis excludes the nonbinary natural pair
using genuine elementary lifts and the literal centralizer quotient. The
binary pair makes the original group solvable. Applied to the existing
nonsolvable source classification, only the single marked symmetric-five
row and the marked symmetric-five pair remain. All paired auxiliary
premises are discharged by the actual source factor record.

Source: Aschbacher--Smith 6.1.1 and E.2.3, printed pp.665--669 and 216--217.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterE.ValuesEvenClassical

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- A literal pair of nonbinary rank-one factors cannot occur in the original
generation-one H-star member, once the source factor lifts are present. -/
theorem hstar_pair_linear_not_isEGenerated
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    {Q : Type*} [Group Q] [Finite Q]
    (q : H →* Q) (hq : Function.Surjective q)
    (hker : (T.subtype hH.1.1.2 : Subgroup H) ⊓ q.ker = pCore 2 H)
    (hcore : pCore 2 Q = ⊥)
    (Y : Subgroup Q) [Y.Normal]
    (L' : Fin 2 → Subgroup Q) (P : ∀ i, Sylow 2 (L' i))
    (hLY : ∀ i, L' i ≤ Y)
    (hP : ∀ i, (P i : Subgroup (L' i)).map (L' i).subtype =
      (T.subtype hH.1.1.2 : Subgroup H).map q ⊓ L' i)
    (hspan : (T.subtype hH.1.1.2 : Subgroup H).map q ⊓ Y =
      ⨆ i, (P i : Subgroup (L' i)).map (L' i).subtype)
    (hcomm : IsMulCommutative
      ((T.subtype hH.1.1.2 : Subgroup H).map q ⊓ Y : Subgroup Q))
    (hproper : ∀ i (D : Subgroup (L' i)),
      (P i : Subgroup (L' i)) ≤ D → D ≠ ⊤ →
        D ≤ normalizer (P i : Set (L' i)))
    (hperm : ∀ g : Q, ∀ i, ∃ j,
      (L' i).map (MulAut.conj g).toMonoidHom = L' j)
    (hLs : ∀ i, IsSimpleGroup (L' i))
    (hLn : ∀ i, ¬ Group.IsSolvable (L' i))
    (hcard : ∀ i j, Nat.card (P i) = Nat.card (P j))
    (hr : ∀ i, 1 < Group.rank (P i))
    (hlift : ∀ i, ∃ A : Subgroup H, IsElementaryAbelian 2 A ∧
      A ≤ (T.subtype hH.1.1.2 : Subgroup H) ∧
      A.map q = (P i : Subgroup (L' i)).map (L' i).subtype) :
    False := by
  have hgen : IsEGenerated 1 H := by
    have hg := h.generation_one H hH
    simpa only [hg] using
      isEGenerated_generationParameter_of_pos
        (show 0 < generationParameter H by omega)
  have hnot := PairLift.not_isEGenerated_of_pair_lifts
    q hq (T.subtype hH.1.1.2) hker hcore Y L' P hLY hP hspan hcomm
    hproper hperm hLs hLn hcard 1 hr hlift
  exact hnot hgen


open Representation Representation.BinaryOffender
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
open ChapterE.ThompsonAction

/-- The original nonsolvable H-star omega orbit has only the marked
symmetric-five rows: the single natural SL₂ and both linear-pair sizes
are excluded from the literal source classification. -/
theorem e23_nonsolvable_symmetric_five_rows
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hns : ¬ Group.IsSolvable H) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI : U.Normal := (RankOneGeneric.Input.hstar_omega_orbit_reduced
      (h.rankOneInput hout) (h.maximal_eq_normalizer_L ▸ hH)).normal
    letI : IsElementaryAbelian 2 U := (RankOneGeneric.Input.hstar_omega_orbit_reduced
      (h.rankOneInput hout) (h.maximal_eq_normalizer_L ▸ hH)).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let α : Representation (ZMod 2) (H ⧸ C) (Additive U) :=
      NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let Y : Subgroup (H ⧸ C) := offenderSubgroup α
    let σ : Representation (ZMod 2) Y (Additive U) := α.comp Y.subtype
    (IsQuasisimple (generalizedFitting Y) ∧
      ∃ c : ProjectiveLine.QuasisimpleSourceConclusion σ (generalizedFitting Y),
        Nonempty (MarkedActionEquiv c.sectionData.action
          (offenderSubgroup c.sectionData.action) (generalizedFitting Y)
          (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))) ∨
      ∃ d : SourceTwoFactorCase σ,
        Nonempty (d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5))) := by
  let hi := h.rankOneInput hout
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) :=
    h.maximal_eq_normalizer_L ▸ hH
  let S := T.subtype hH.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := hi.hstar_omega_orbit_reduced hH'
  let := hU.normal
  let := hU.elementary
  have hp := hi.hstar_minimal_parabolic hH'
  have hj := hi.hstar_thompson_moves_omega_orbit hH' hZH
  have hgen : IsEGenerated 1 H := by
    have hg := h.generation_one H hH
    simpa only [hg] using isEGenerated_generationParameter_of_pos
      (show 0 < generationParameter H by omega)
  rcases h.e23_nonsolvable_symmetric_or_pair hout hH hZH hns with hs | ⟨d,_,_⟩
  · exact Or.inl hs
  · refine Or.inr ⟨d,?_⟩
    exact (source_pair_of_isEGenerated_one S hp U hU hj _
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hgen d).resolve_left hns

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
