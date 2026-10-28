module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.BinaryResidual
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearFlags
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.BinaryFlags
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# Both binary rows on the original escaping component

The actual central core-to-star map is injective in the L₄(2) and L₅(2)
rows: their Schur multipliers are two-groups and X/O₂(X) has trivial
two-core. Cubic rank and the outer two-group then give X = O^{3′}(I).

The original S intersects the subnormal X in a Sylow two-subgroup, so
its star image lies in the literal marking (NI ∩ X)*. If that marking
were a two-group, its preimage would be normal in NI and lie in O₂(NI).
The star-Sylow lifting theorem and C.1.29 would make X a forbidden
chi-zero block. The proper marked Sylow overgroup therefore gives a
positive-rank binary parabolic, including every interior-node flag.
No Thompson-image containment or small-Sylow bound is required.

Source: Aschbacher--Smith C.2.7(3)(h), printed pp.145--147, and
original 15.2.23, printed pp.1116--1117; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher PerfectCentralCovering
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding TerminalLinear
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G] {I X R N : Subgroup G}

/-- The literal core-to-star map has trivial kernel in either binary row. -/
theorem binary_model_coreToStar_injective
    (h : Input KnownSimple.IsKnownSimple I R N X)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : starImage X R X ≃* SL(n,ZMod 2)) :
    Function.Injective (coreToStar h.normalizes) := by
  let a := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < n)).symm
  let Q := X ⧸ pCore 2 X
  let : IsQuasisimple Q := h.quasisimple
  let f := coreToStar h.normalizes
  let c : Cover Q PSL(n,ZMod 2) := {
    toMonoidHom := a.toMonoidHom.comp f
    surjective := a.surjective.comp (coreToStar_surjective h.normalizes)
    isPerfect := inferInstance
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
      exact coreToStar_ker_central_from_source h }
  let : Group.IsPerfect PSL(n,ZMod 2) := Group.IsPerfect.ofSurjective c.surjective
  have hp : IsPGroup 2 (universalProjection PSL(n,ZMod 2)).ker := by
    rcases hn with h | h <;> subst n
    · exact (IsPGroup.of_card (show Nat.card (Multiplicative (ZMod 2)) = 2 ^ 1 by simp)).of_equiv
        (Matrix.PSL4Two.schurMultiplierEquivTwo (ZMod 2) (by simp) (MulEquiv.refl _)).symm
    · rw [Theory.SpecificGroups.PSL5Two.UniversalCover.field_universalProjection_ker_eq_bot
        (ZMod 2) (by simp)]
      exact IsPGroup.of_subsingleton 2 _
  have hf := c.injective_of_pCore_eq_bot_of_universal_pGroup
    (universalCover PSL(n,ZMod 2)) universalCover_isUniversal hp
    (pCore_quotient_pCore_eq_bot 2)
  exact fun x y hh => hf (congrArg a hh)

/-- The equivalence induced by the original core-to-star map. -/
noncomputable def binary_model_coreStarEquiv
    (h : Input KnownSimple.IsKnownSimple I R N X)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : starImage X R X ≃* SL(n,ZMod 2)) :
    (X ⧸ pCore 2 X) ≃* starImage X R X :=
  MulEquiv.ofBijective (coreToStar h.normalizes)
    ⟨binary_model_coreToStar_injective h hn e,coreToStar_surjective h.normalizes⟩

variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include hsource in
/-- The unmarked binary star model already identifies the original cubic residual. -/
theorem binary_model_eq_threeResidual
    (hI : PlaneEscapes Mc ZS I)
    (h : Input KnownSimple.IsKnownSimple I R N X)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (a : starImage X R X ≃* SL(n,ZMod 2)) :
    X = (primeToResidual 3 I).map I.subtype := by
  let Y := X.subgroupOf I
  let eY : Y ≃* X := subgroupOfEquivOfLe h.component.1
  let eQ : (Y ⧸ pCore 2 Y) ≃* (X ⧸ pCore 2 X) :=
    QuotientGroup.congr _ _ eY (pCore_map_iso 2 eY)
  let e : (Y ⧸ pCore 2 Y) ≃* SL(n,ZMod 2) :=
    (eQ.trans (binary_model_coreStarEquiv h hn a)).trans a
  let : IsQuasisimple (X ⧸ pCore 2 X) := h.quasisimple
  let : IsQuasisimple (Y ⧸ pCore 2 Y) := IsQuasisimple.of_mulEquiv eQ.symm
  have hz : center (Y ⧸ pCore 2 Y) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have he := ((centerCongr e) ⟨x,hx⟩).property
    change e x ∈ center SL(n,ZMod 2) at he
    rw [BinaryLinear.OuterCyclic.binary_center_eq_bot (by omega),mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hr : 2 ≤ primeRank 3 (Y ⧸ pCore 2 Y) := by
    rw [primeRank_congr 3 e]
    exact Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank (by omega)
  have ho : IsPGroup 2 (MulAut.Outer (Y ⧸ pCore 2 Y)) :=
    (BinaryLinear.OuterCyclic.sl_outer_isTwoGroup hn).of_equiv
      (MulAut.outerCongr e).symm
  have hY := h.component.2.eq_primeToResidual_three_of_rank_outer_two hz hr
    ((Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
      3 Nat.prime_three (by decide)) ho
  have hh := congrArg (Subgroup.map I.subtype) hY
  rwa [map_subgroupOf_eq_of_le h.component.1] at hh


include d in
private theorem original_star_sylow
    (hI : PlaneEscapes Mc ZS I)
    (h : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X) :
    ∃ Q : Sylow 2 (starImage X ((M ⊓ I).pCoreIn 2) X),
      (Q : Subgroup _) ≤ (starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
        (starImage X ((M ⊓ I).pCoreIn 2) X) := by
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (d.sylow_in_escape hI) h.component.1 h.component.2.subnormal
  let R := (M ⊓ I).pCoreIn 2
  refine ⟨P.mapSurjective (toStarImage_surjective X R),?_⟩
  rintro y ⟨x,hx,rfl⟩
  have hxS : (x : G) ∈ planeSylow T ZS :=
    (hP.le.trans inf_le_left) (mem_map_of_mem X.subtype hx)
  have hxM : (x : G) ∈ M := hsource.maximal.1.2 hxS.1
  exact mem_map_of_mem (QuotientGroup.mk' (starKernel X R))
    (show (x : G) ∈ (M ⊓ I) ⊓ X from ⟨⟨hxM,h.component.1 x.property⟩,x.property⟩)

include hsource in
private theorem binary_model_marking_not_two
    (hI : PlaneEscapes Mc ZS I)
    (h : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X)
    (hno : ¬ ChapterC.IsChiBlock X)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* SL(n,ZMod 2))
    (Q : Sylow 2 (starImage X ((M ⊓ I).pCoreIn 2) X))
    (hQ : (Q : Subgroup _) ≤ (starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
      (starImage X ((M ⊓ I).pCoreIn 2) X)) :
    ¬ IsPGroup 2 ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
      (starImage X ((M ⊓ I).pCoreIn 2) X)) := by
  intro hp
  let R := (M ⊓ I).pCoreIn 2
  let C := starImage X R X
  let P := (starM X R (M ⊓ I)).subgroupOf C
  let D := (M ⊓ I) ⊓ X
  let q := toStarImage X R
  have hinj := binary_model_coreToStar_injective h hn e
  have hker : q.ker = pCore 2 X := by
    ext x
    change q x = 1 ↔ x ∈ pCore 2 X
    constructor
    · intro hx
      apply (QuotientGroup.eq_one_iff x).mp
      change QuotientGroup.mk' (pCore 2 X) x = 1
      apply hinj
      rw [map_one,coreToStar_mk]
      exact hx
    · intro hx
      have he : QuotientGroup.mk' (pCore 2 X) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      change toStarImage X R x = 1
      rw [←coreToStar_mk h.normalizes,he,map_one]
  have hkp : IsPGroup 2 q.ker := by rw [hker]; exact pCore_isPGroup
  have hpre : IsPGroup 2 (P.comap q) := hp.comap_of_ker_isPGroup q hkp
  let j : D →* P.comap q := (inclusion (show D ≤ X from inf_le_right)).codRestrict _ (by
    intro x
    exact mem_map_of_mem (QuotientGroup.mk' (starKernel X R)) x.property)
  have hD : IsPGroup 2 D := hpre.of_injective j (by
    intro a b hab
    exact Subtype.ext (congrArg (fun y : P.comap q => (y.val : G)) hab))
  have hX : I ≤ normalizer (X : Set G) := by
    rw [binary_model_eq_threeResidual (hsource := hsource) hI h hn e]
    exact I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (primeToResidual 3 I))
  have hDnorm : M ⊓ I ≤ normalizer (D : Set G) :=
    (le_inf (M ⊓ I).le_normalizer (inf_le_right.trans hX)).trans
      inf_normalizer_le_normalizer_inf
  have hDR : D ≤ R := le_pCoreIn_of_normalizes hD inf_le_left hDnorm
  have hPR : P ≤ (starImage X R R).subgroupOf C := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hx
    exact ⟨y,hDR hy,he⟩
  let : (X.subgroupOf (X ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  obtain ⟨S,hS⟩ := radical_sylow_of_star_component_sylow (source_join_input h) Q
    (map_le_iff_le_comap.mpr (hQ.trans hPR))
  apply hno
  apply (source_chiZero_of_sylow_input h ?_).2.chi
  exact ⟨S,by rw [hS,map_subgroupOf_eq_of_le le_sup_right]⟩

include d in
/-- Construct the actual positive-rank marked binary parabolic from the original
Sylow intersection and the source no-chi conclusion. -/
theorem binary_model_marked_parabolic
    (hI : PlaneEscapes Mc ZS I)
    (h : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X)
    (hno : ¬ ChapterC.IsChiBlock X)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* SL(n,ZMod 2)) :
    IsBinaryPositiveRankParabolic
      ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
        (starImage X ((M ⊓ I).pCoreIn 2) X)) n := by
  obtain ⟨Q,hQ⟩ := original_star_sylow d hI h
  have hp := binary_model_marking_not_two (hsource := hsource) hI h hno hn e Q hQ
  have hproper : (starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
      (starImage X ((M ⊓ I).pCoreIn 2) X) ≠ ⊤ := by
    intro ht
    exact (star_thompson_intersection_from_source h).2.not_ge (subgroupOf_eq_top.mp ht)
  rcases hn with rfl | rfl
  · exact binaryPositiveRank_of_sylow_overgroup (m := 3) e _ Q hQ hproper hp
  · exact binaryPositiveRank_of_sylow_overgroup (m := 4) e _ Q hQ hproper hp

include d in
/-- Apply the marked binary reduction to the same selected X, R and NI. -/
theorem normalized_component_binary
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* SL(n,ZMod 2)) :
    LinearAlternative X ((M ⊓ I).pCoreIn 2) (M ⊓ I) :=
  .binaryLinear n hn (binary_model_marked_parabolic d hI
    (normalized_component_input (hsource := hsource) hI hcore s) (s.toSelected.not_chi hno) hn e)

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
