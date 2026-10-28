module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RadicalMarking
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.StarSylow
public import Theory.GroupTheory.PCoreProduct
public import Theory.Representation.BinaryRadicalFlag.PositiveRank
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality

/-!
# The marked binary parabolic and the unrestricted L₅(2) row

When the actual J(R)* lies in X*, Thompson normalizer control identifies
M_X* with the normalizer of R* intersect X*. If this normalizer were a
two-group, that intersection would be Sylow and C.1.29 would make X a
forbidden chi-zero block. Its canonical binary flag therefore has positive
semisimple rank. We transport the full flag stabilizer through the literal
SL-to-PSL quotient, retaining the original star map and marked subgroup.

For L₅(2), its order exceeds every exceptional outer actor in the complete
B.5.1 moved-section conclusion. This derives J(R)* ≤ X* and discharges
the placement premise. The final consumer applies the result to the same
selected escaping component, R = O₂(M intersect I) and NI = M intersect I.
No small-Sylow bound, preselected flag or terminal-model exclusion is used.

Source: Aschbacher--Smith, C.2.7(3)(h), pp.145--147, and the component
reduction in original 15.2.23, pp.1116--1117; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}

/-- The actual inner Thompson marking determines a proper positive-rank
binary flag. The premise must be derived for the row being used. -/
theorem binary_marked_parabolic_of_thompson_inner
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hM : M ≤ normalizer (R : Set G)) (hc : ¬ ChapterC.IsChiBlock K)
    (hi : starImage K R (elementaryAbelianMaxJ R) ≤ starImage K R K)
    {n : ℕ} (hn : 2 ≤ n) (e : starImage K R K ≃* SL(n,ZMod 2)) :
    IsBinaryPositiveRankParabolic
      ((starM K R M).subgroupOf (starImage K R K)) n := by
  let : NeZero n := ⟨by omega⟩
  let C := starImage K R K
  let U := (starImage K R R).subgroupOf C
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  obtain ⟨hr,heq⟩ := marked_radical_normalizer h hM hi
  have hnot : ¬ IsPGroup 2 (normalizer (U : Set C)) := by
    intro hp
    have hself : normalizer (U : Set C) = U :=
      (pCoreIn_eq_self_of_isPGroup 2 _ hp).symm.trans hr.2
    obtain ⟨S,hS⟩ := exists_sylow_eq_of_isPGroup_of_normalizer_eq U hr.isPGroup hself
    exact star_radical_not_sylow h hc ⟨S,hS.le⟩
  have hr' := hr.map_equiv e
  have hnot' : ¬ IsPGroup 2 (normalizer (U.map e.toMonoidHom : Set SL(n,ZMod 2))) := by
    intro hp
    apply hnot
    have hp' : IsPGroup 2 ((normalizer (U : Set C)).map e.toMonoidHom) := by
      rwa [map_equiv_normalizer_eq]
    exact hp'.of_injective (Subgroup.equivMapOfInjective
      (normalizer (U : Set C)) e.toMonoidHom e.injective).toMonoidHom
      (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).injective
  let ρ := Representation.specialLinearNatural (k := ZMod 2) n
  have hρ : Function.Injective ρ := by
    intro g j hh
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    exact LinearMap.congr_fun hh
  obtain ⟨k,W,hk,hbound,hs,hproper,hflag⟩ :=
    Representation.BinaryRadical.exists_positiveRank_flag_normalizer ρ hρ _ hr' hnot'
  let f : LinearFlag (ZMod 2) n k := ⟨W,fun i => (hproper i).1,fun i => (hproper i).2,hs⟩
  let q := QuotientGroup.mk' (center SL(n,ZMod 2))
  let eqp := (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < n)).symm
  refine ⟨e.trans eqp,k,hk,?_,f,?_⟩
  · simpa using hbound
  · change ((starM K R M).subgroupOf C).map (q.comp e.toMonoidHom) = f.stabilizer.map q
    rw [←map_map,heq,map_equiv_normalizer_eq,hflag]
    congr 1
    change (⨅ i, Representation.BinaryRadical.stabilizer ρ (W i)) =
      ⨅ i, linearStabilizer (W i)
    apply iInf_congr
    intro i
    ext g
    rw [linearStabilizer,Subgroup.mem_comap,Submodule.stabilizer_coe,
      MulAction.mem_stabilizer_set]
    rfl

/-- For L₅(2), the full B.5.1 source itself puts J(R)* in the component:
its order exceeds every exceptional outer actor. -/
theorem linearFive_marked_parabolic
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hM : M ≤ normalizer (R : Set G)) (hc : ¬ ChapterC.IsChiBlock K)
    (e : starImage K R K ≃* SL(5,ZMod 2)) :
    IsBinaryPositiveRankParabolic
      ((starM K R M).subgroupOf (starImage K R K)) 5 := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  have hlarge : 40320 < Nat.card (starImage K R K) := by
    rw [Nat.card_congr e.toEquiv,BinaryLinear.card_SL]
    norm_num [BinaryLinear.order,Fin.prod_univ_succ]
  exact binary_marked_parabolic_of_thompson_inner h hM hc
    (star_thompson_le_component_of_large_order (source_join_input h) hlarge) (by decide) e

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue

namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open ComponentCatalogue
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

include hsource in
/-- The literal selected L₅(2) row yields C.2.7(h), with its marked
positive-rank parabolic; no Thompson-placement or flag premise remains. -/
theorem normalized_component_linearFive
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* SL(5,ZMod 2)) :
    LinearAlternative X ((M ⊓ I).pCoreIn 2) (M ⊓ I) := by
  refine .binaryLinear 5 (Or.inr rfl) ?_
  apply linearFive_marked_parabolic
    (normalized_component_input (hsource := hsource) hI hcore s) ?_
    (s.toSelected.not_chi hno) e
  exact (M ⊓ I).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (M ⊓ I) (pCore 2 (M ⊓ I : Subgroup G)))

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
