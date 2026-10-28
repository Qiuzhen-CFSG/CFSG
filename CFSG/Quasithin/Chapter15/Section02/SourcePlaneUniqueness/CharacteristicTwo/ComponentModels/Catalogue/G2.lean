module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearThreeDegree
public import Theory.SpecificGroups.G2Even.MarkedCover
public import Theory.SpecificGroups.G2.SolvableSylowNormalizer
public import Theory.SpecificGroups.G2Even.RadicalNormalizers
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank

/-!
# Exclusion of the original nonbinary G₂ component

The two-primary covering kernel vanishes in X/O₂(X), identifying the full
core quotient through the original star projection. The actual large G₂
model puts the Thompson image inside the component, so its two-radical
normalizer lies in the marked NI intersection. The exact root-parabolic
normalizer calculation then places each full Sylow normalizer there too.

The original H is solvable and H intersect X contains a full Sylow subgroup
of X. Its G₂ image lies in that Sylow normalizer. The quotient kernel is
O₂(X), already in NI, so H intersect X lies in NI. But cubic rank two in K
forces a cubic in K intersect X, whereas K intersect M is a two-group.
This excludes every nonbinary field, including degree two, on the same
X, R and NI. No KS containment or MS classification is used.

Source: Aschbacher--Smith C.2.7, pp.145--147 and original 15.2.23,
pp.1116--1117; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G] {I X R N : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private noncomputable def g2Cover
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (e : starImage X R X ≃* Atlas.G2.Model F) :
    Cover (X ⧸ pCore 2 X) (Atlas.G2.Model F) where
  toMonoidHom := e.toMonoidHom.comp (coreToStar h.normalizes)
  surjective := e.surjective.comp (coreToStar_surjective h.normalizes)
  isPerfect := h.quasisimple.toIsPerfect
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact coreToStar_ker_central_from_source h

/-- The actual star projection identifies the entire nonbinary G₂ core quotient. -/
noncomputable def g2CoreEquiv
    (h : Input KnownSimple.IsKnownSimple I R N X)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : starImage X R X ≃* Atlas.G2.Model F) :
    (X ⧸ pCore 2 X) ≃* Atlas.G2.Model F := by
  let : IsQuasisimple (X ⧸ pCore 2 X) := h.quasisimple
  let : Fact (2 < Nat.card F) := ⟨by
    rw [hF]
    exact (by norm_num : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide : 1 < 2) hn⟩
  let f := g2Cover h e
  have hi : Function.Injective f.toMonoidHom :=
    (universalQuasisimpleCover_isUniversal (Atlas.G2.Model F)).injective_of_pGroup_kernel
      (Atlas.G2.FiniteCover.universalKernel_isPGroup_of_card_pow hF hn)
      f.toCovering (pCore_quotient_pCore_eq_bot 2)
  exact MulEquiv.ofBijective f.toMonoidHom ⟨hi,f.surjective⟩

omit [CharP F 2] in
/-- Compatibility with the original projection from X. -/
theorem g2CoreEquiv_mk
    (h : Input KnownSimple.IsKnownSimple I R N X)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : starImage X R X ≃* Atlas.G2.Model F) (x : X) :
    g2CoreEquiv h hn hF e (QuotientGroup.mk' (pCore 2 X) x) =
      e (toStarImage X R x) := by
  change e (coreToStar h.normalizes (QuotientGroup.mk' (pCore 2 X) x)) = _
  rw [coreToStar_mk]

/-- The original NI image contains the full normalizer of each Sylow it contains. -/
theorem g2_star_sylow_normalizer_le
    (h : Input KnownSimple.IsKnownSimple I R N X)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : starImage X R X ≃* Atlas.G2.Model F)
    (Q : Sylow 2 (Atlas.G2.Model F))
    (hQ : (Q : Subgroup (Atlas.G2.Model F)) ≤
      (N.subgroupOf X).map ((g2CoreEquiv h hn hF e).toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 X)))) :
    normalizer (Q : Set (Atlas.G2.Model F)) ≤
      (N.subgroupOf X).map ((g2CoreEquiv h hn hF e).toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 X))) := by
  let q := (g2CoreEquiv h hn hF e).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have he : ((starM X R N).subgroupOf (starImage X R X)).map e.toMonoidHom =
      (N.subgroupOf X).map q := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨k,hk,hky⟩ := hy
      let z : X := ⟨k,hk.2⟩
      have hy' : toStarImage X R z = y := Subtype.ext hky
      refine ⟨z,hk.1,?_⟩
      rw [←hy']
      exact g2CoreEquiv_mk h hn hF e z
    · rintro ⟨z,hz,rfl⟩
      refine ⟨toStarImage X R z,?_,(g2CoreEquiv_mk h hn hF e z).symm⟩
      exact ⟨inclusion (show X ≤ X ⊔ R from le_sup_left) z,⟨hz,z.property⟩,rfl⟩
  have hlarge : 40320 < Nat.card (starImage X R X) := by
    rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model]
    have hq : 4 ≤ Nat.card F := by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hn
    have hh := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hq 6)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 6) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    exact lt_of_lt_of_le (by norm_num : 40320 < 4 ^ 6 * (4 ^ 6 - 1) * (4 ^ 2 - 1)) hh
  obtain ⟨hr,hN⟩ := star_intersection_placement_from_source_of_large_order h hlarge
  apply Atlas.G2.sylow_normalizer_le_of_radical_normalizer_le
    (((starImage X R R).subgroupOf (starImage X R X)).map e.toMonoidHom)
    (hr.map_equiv e) Q _ hQ
  rw [←he,←map_equiv_normalizer_eq]
  exact map_mono hN

variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

private theorem residual_intersection_three_dvd
    (hI : PlaneEscapes Mc ZS I) {A : Subgroup G} (hAI : A ≤ I)
    (hKA : (pResidual 2 H).map H.subtype ≤ normalizer (A : Set G))
    (hthree : 3 ∣ Nat.card A) :
    3 ∣ Nat.card ((pResidual 2 H).map H.subtype ⊓ A : Subgroup G) := by
  let K := (pResidual 2 H).map H.subtype
  have hKI : K ≤ I :=
    (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  obtain ⟨E,hE,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := K) (p := 3)
  let := hE
  let EI := E.map (inclusion hKI)
  let e : E ≃* EI := E.equivMapOfInjective (inclusion hKI) (inclusion_injective hKI)
  let : IsElementaryAbelian 3 EI := IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective
  have hEI : Nat.card EI = 3 ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, hcard, residual_rank_two d]
  have hnorm : EI ≤ normalizer (A.subgroupOf I : Set I) := by
    rw [← subgroupOf_normalizer_eq hAI]
    rintro _ ⟨x,hx,rfl⟩
    exact hKA x.property
  have hAIcard : 3 ∣ Nat.card (A.subgroupOf I) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAI).toEquiv]
    exact hthree
  have hr : primeRank 3 I ≤ 2 :=
    (Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
      3 Nat.prime_three (by decide)
  have hne := Subgroup.inf_ne_bot_of_elementary_plane EI (A.subgroupOf I)
    hnorm hAIcard hEI hr
  have hp : IsPGroup 3 (EI ⊓ A.subgroupOf I : Subgroup I) :=
    (IsElementaryAbelian.isPGroup 3 EI).to_le inf_le_left
  have hd : 3 ∣ Nat.card (EI ⊓ A.subgroupOf I : Subgroup I) := by
    rcases hp.card_eq_or_dvd with h | h
    · exact (hne (card_eq_one.mp h)).elim
    · exact h
  let j : (EI ⊓ A.subgroupOf I : Subgroup I) →* (K ⊓ A : Subgroup G) := {
    toFun := fun x => ⟨x.val.val, by
      obtain ⟨k,hk,he⟩ := x.property.1
      exact ⟨(congrArg Subtype.val he) ▸ k.property,x.property.2⟩⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (K ⊓ A : Subgroup G) => (z : G)) h
  exact hd.trans (card_dvd_of_injective j hj)

private theorem source_local_solvable : Group.IsSolvable H := by
  obtain ⟨e⟩ := d.geometry.quotient
  let : Group.IsSolvable BinaryFourPlus.Wreath := BinaryFourPlus.wreath_isSolvable
  let : Group.IsSolvable (H ⧸ pCore 2 H) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  exact Group.isSolvable_of_ker_le_range
    (pCore 2 H).subtype (QuotientGroup.mk' (pCore 2 H))
    (by rw [QuotientGroup.ker_mk',range_subtype])

private theorem component_sylow_in_plane
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup G}
    (hX : X ∈ Chapter1.cComponentsIn I) :
    ∃ P : Sylow 2 X, (P : Subgroup X) ≤ (planeSylow T ZS).subgroupOf X := by
  obtain ⟨R,hR⟩ := d.sylow_in_escape hI
  obtain ⟨Q,hQ⟩ := R.exists_subgroupOf_eq_of_subnormal (X.subgroupOf I) hX.2.subnormal
  let e := subgroupOfEquivOfLe hX.1
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  rintro x ⟨y,hy,rfl⟩
  have hyR : (y : I) ∈ R := by
    change y ∈ (R : Subgroup I).subgroupOf (X.subgroupOf I)
    rwa [← hQ]
  have hyS : ((y : I) : G) ∈ planeSylow T ZS := hR ▸ mem_map_of_mem I.subtype hyR
  exact hyS

/-- A nonbinary G₂ row cannot occur on the original normalized component. -/
theorem normalized_component_g2_false
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* Atlas.G2.Model F) : False := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  have hlarge : 3 < Nat.card F := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    omega
  let a := g2CoreEquiv h hn hF e
  let f := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hf : Function.Surjective f := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = pCore 2 X := by
    ext x
    change a (QuotientGroup.mk' (pCore 2 X) x) = 1 ↔ _
    rw [a.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  obtain ⟨P,hP⟩ := component_sylow_in_plane d hI selection.component
  let Q := P.mapSurjective hf
  let J := H.subgroupOf X
  let N := (M ⊓ I).subgroupOf X
  have hPN : (P : Subgroup X) ≤ N := by
    intro x hx
    exact ⟨hsource.maximal.1.2 ((hP hx).1),selection.component.1 x.property⟩
  have hPJ : (P : Subgroup X) ≤ J := by
    intro x hx
    exact d.geometry.outside.1.1.2 (hP hx).1
  let : Group.IsSolvable H := source_local_solvable d
  let j : J →* H := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hh
    exact Subtype.ext (Subtype.ext (congrArg (fun z : H => (z : G)) hh))
  let : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective hj
  have hs : Group.IsSolvable (J.map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective J)
  have hJN : J.map f ≤ N.map f :=
    (Atlas.G2.solvable_sylow_overgroup_normalizes (by omega) Q (J.map f)
      (map_mono hPJ) hs).trans
      (g2_star_sylow_normalizer_le h hn hF e Q (map_mono hPN))
  have hkerN : f.ker ≤ N := by
    rw [hker]
    exact ((pCore_isPGroup (p := 2) (G := X)).le_sylow_of_normal P).trans hPN
  have hJN' : J ≤ N := by
    have hh := map_le_iff_le_comap.mp hJN
    rwa [comap_map_eq_self hkerN] at hh
  let K := (pResidual 2 H).map H.subtype
  have hKM : K ⊓ X ≤ K ⊓ M := by
    intro x hx
    have hxH : x ∈ H := (map_subtype_le (pResidual 2 H)) hx.1
    exact ⟨hx.1,(hJN' (show (⟨x,hx.2⟩ : X) ∈ J from hxH)).1⟩
  have ht : IsPGroup 2 (K ⊓ X : Subgroup G) := by
    apply (isPGroup_pCoreIn 2 K).to_le
    rwa [←residual_intersection_eq_core d]
  have hr : 2 ≤ primeRank 3 (Atlas.G2.Model F) :=
    Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2.trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Atlas.G2.Model F)).subtype
        (commutator (Atlas.G2.Model F)).subtype_injective)
  have hthree : 3 ∣ Nat.card X := by
    have hd : 3 ∣ Nat.card (Atlas.G2.Model F) := by
      by_contra hh
      have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hh
      omega
    exact hd.trans (card_dvd_of_surjective f hf)
  have hd := residual_intersection_three_dvd d hI selection.component.1
    selection.residual_normalizes hthree
  obtain ⟨k,hk⟩ := ht.exists_card_eq
  rw [hk] at hd
  exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue

