module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingStarSixExclusion
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.DualExtensions.Reduction
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.Alternating.OddCentralCovers

/-!
# Natural permutation coordinates on the full original star quotient

Ratio one transfers offender generation to the moved quotient. Its marked
S₅ or S₇ action therefore gives a symmetric group inside the star group.
The actual alternating automorphism embedding bounds that star group by
the same symmetric group, so the offender subgroup is the whole star group.
The resulting equivalence retains the original alternating component and
intertwines the literal moved-section action. For the five-letter row,
the Schur multiplier and source center bound also make the original
core-to-star map injective.

Source: Aschbacher--Smith B.5.1, C.2.7(a--b), printed pp.99--103,145--147;
used in original 15.2.23, pp.1116--1117.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {I X R N : Subgroup G}

/-- The marked natural row generates the whole original star quotient. -/
theorem natural_permutation_offender_eq_top
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (hCJ : starImage X R X ≤ offenderSubgroup (starRepresentation X R))
    (s : MovedSection ((starRepresentation X R).comp (offenderSubgroup (starRepresentation X R)).subtype)
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))))
    {n : ℕ} (hn : n = 5 ∨ n = 7)
    (a : MarkedActionEquiv s.action (offenderSubgroup s.action)
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R)))
      (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n)))
    (hr : quadraticRatio s.action = 1) :
    offenderSubgroup (starRepresentation X R) = ⊤ := by
  let J := offenderSubgroup (starRepresentation X R)
  let L := (starImage X R X).subgroupOf J
  let : (X.subgroupOf (X ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer h.normalizes)
  let : (starImage X R X).Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  let : L.Normal := inferInstance
  have ht := ExtensionConsequences.DualExtensions.section_generated s hr
    (offenderSubgroup_restrict_eq_top (starRepresentation X R))
  have hc : Nat.card J = Nat.card (Equiv.Perm (Fin n)) := by
    rw [←Nat.card_congr a.action.groupEquiv.toEquiv,ht,card_top]
  let e := (subgroupOfEquivOfLe hCJ).symm.trans a.subgroupEquiv
  obtain ⟨f,hf,_⟩ := alternating_star_embedding h (by omega) (by omega) e
  apply J.eq_top_of_card_eq
  apply Nat.le_antisymm (card_le_card_group J)
  rw [hc]
  exact Nat.card_le_card_of_injective f hf

/-- Full natural coordinates with the same original component marking. -/
theorem natural_permutation_star_coordinates
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (hCJ : starImage X R X ≤ offenderSubgroup (starRepresentation X R))
    (s : MovedSection ((starRepresentation X R).comp (offenderSubgroup (starRepresentation X R)).subtype)
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R))))
    {n : ℕ} (hn : n = 5 ∨ n = 7)
    (a : MarkedActionEquiv s.action (offenderSubgroup s.action)
      ((starImage X R X).subgroupOf (offenderSubgroup (starRepresentation X R)))
      (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n)))
    (hr : quadraticRatio s.action = 1) :
    ∃ e : StarQuotient X R ≃* Equiv.Perm (Fin n),
      (∀ x : starImage X R X,
        e x = (a.subgroupEquiv ((subgroupOfEquivOfLe hCJ).symm x) : Equiv.Perm (Fin n))) ∧
      (∀ j : offenderSubgroup (starRepresentation X R),
        ∀ v : s.space.toSubmodule ⧸ s.central.toSubmodule,
        a.action.linearEquiv (s.central.quotientRepresentation j v) =
          BinaryPermutation.naturalRepresentation (Fin n) (e j) (a.action.linearEquiv v)) := by
  let J := offenderSubgroup (starRepresentation X R)
  let L := (starImage X R X).subgroupOf J
  let : (X.subgroupOf (X ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer h.normalizes)
  let : (starImage X R X).Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  let : L.Normal := inferInstance
  have ht := ExtensionConsequences.DualExtensions.section_generated s hr
    (offenderSubgroup_restrict_eq_top (starRepresentation X R))
  have hJ := natural_permutation_offender_eq_top h hCJ s hn a hr
  let j : J ≃* StarQuotient X R := (MulEquiv.subgroupCongr hJ).trans topEquiv
  let b : offenderSubgroup s.action ≃* J := (MulEquiv.subgroupCongr ht).trans topEquiv
  let e := j.symm.trans (b.symm.trans a.action.groupEquiv)
  refine ⟨e,?_,?_⟩
  · intro x
    exact a.compatible ((subgroupOfEquivOfLe hCJ).symm x)
  · intro x v
    exact a.action.intertwines (b.symm x) v

/-- The five-letter row has no central kernel in the original core quotient. -/
theorem alternatingFive_coreToStar_injective
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (e : starImage X R X ≃* alternatingGroup (Fin 5)) :
    Function.Injective (coreToStar h.normalizes) := by
  let : IsQuasisimple (X ⧸ pCore 2 X) := h.quasisimple
  let f : PerfectCentralCovering.Cover (X ⧸ pCore 2 X) (alternatingGroup (Fin 5)) := {
    toMonoidHom := e.toMonoidHom.comp (coreToStar h.normalizes)
    surjective := e.surjective.comp (coreToStar_surjective h.normalizes)
    isPerfect := h.quasisimple.toIsPerfect
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      exact coreToStar_ker_central_from_source h }
  let a := f.quotientCenterEquiv.trans
    ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
      QuotientGroup.quotientBot)
  have hd := GLS3.Chapter5.OddCentralCovers.center_card_dvd_two_of_nonexceptional
    5 (by decide) (by decide) (by decide) a
  have hc : Nat.card (center (X ⧸ pCore 2 X)) = 1 := by
    rcases coreQuotient_center_card_from_source h with hh | hh
    · exact hh
    · rw [hh] at hd
      norm_num at hd
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact bot_unique ((coreToStar_ker_central_from_source h).trans_eq ((eq_bot_iff_card _).mpr hc))

end CFSG.Quasithin.ChapterC.C27Source
