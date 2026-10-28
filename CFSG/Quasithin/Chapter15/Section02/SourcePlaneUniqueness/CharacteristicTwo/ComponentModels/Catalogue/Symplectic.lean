module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearThreeDegree
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableParity
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SymplecticParabolic
public import Theory.SpecificGroups.SymplecticFour.Sylow.NormalizerParabolic

/-!
# Full core markings and exclusion of the nonbinary symplectic row

The canonical map X/O2(X) to X* is a perfect central cover. The proved
symplectic multiplier theorem makes it an isomorphism for every nonbinary
field. This preserves the original star map on elements and transfers the
actual NI intersection to the point or plane maximal parabolic.

The original K has cubic rank two and normalizes X, so the rank bound in I
forces a cubic in K intersect X. Meanwhile H is solvable and H intersect X
contains a Sylow two-subgroup of X. Its full-core image is consequently a
solvable Sylow overgroup in Sp4(2^n), with a cubic surviving the two-kernel.
The split-torus calculation forces n even. No MS classification, small-Sylow
bound or KS-containment assumption is used for this restriction.

The same original Sylow lies in NI. Its full normalizer is contained in the
marked parabolic, so solvability places the entire image of H intersect X
there. The two-core lies in that Sylow, allowing this containment to lift to
H intersect X ≤ NI. This puts K intersect X in the two-group K intersect M,
contradicting its surviving cubic. Thus every nonbinary degree is excluded.
The other nonlinear rows and full KS placement remain; this module does not
assert the entire C.2.7 catalogue or original 15.2.23.
Source: Aschbacher--Smith C.2.7, pp.145--147, and original 15.2.23,
p.1116; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {I X R N : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private noncomputable def symplecticCover
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (e : starImage X R X ≃* Sp F) : Cover (X ⧸ pCore 2 X) (Sp F) where
  toMonoidHom := e.toMonoidHom.comp (coreToStar h.normalizes)
  surjective := e.surjective.comp (coreToStar_surjective h.normalizes)
  isPerfect := h.quasisimple.toIsPerfect
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact coreToStar_ker_central_from_source h

/-- The original star marking identifies the entire symplectic core quotient. -/
noncomputable def symplecticCoreEquiv
    (h : Input KnownSimple.IsKnownSimple I R N X) (hF : 3 < Nat.card F)
    (e : starImage X R X ≃* Sp F) : (X ⧸ pCore 2 X) ≃* Sp F :=
  CentralCovers.Even.coverEquiv hF (symplecticCover h e)

/-- Compatibility with the literal projection from the original component. -/
theorem symplecticCoreEquiv_mk
    (h : Input KnownSimple.IsKnownSimple I R N X) (hF : 3 < Nat.card F)
    (e : starImage X R X ≃* Sp F) (x : X) :
    symplecticCoreEquiv h hF e (QuotientGroup.mk' (pCore 2 X) x) =
      e (toStarImage X R x) := by
  unfold symplecticCoreEquiv
  rw [CentralCovers.Even.coverEquiv_apply]
  change e (coreToStar h.normalizes (QuotientGroup.mk' (pCore 2 X) x)) = _
  rw [coreToStar_mk]

/-- The marked parabolic transfers through the original full core quotient. -/
theorem symplectic_core_parabolic
    (h : Input KnownSimple.IsKnownSimple I R N X) (hF : 3 < Nat.card F)
    (e : starImage X R X ≃* Sp F) :
    let q := (symplecticCoreEquiv h hF e).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
    ∃ g : Sp F,
      ((N.subgroupOf X).map q).map (MulAut.conj g).toMonoidHom = pointParabolic ∨
      ((N.subgroupOf X).map q).map (MulAut.conj g).toMonoidHom = planeParabolic := by
  intro q
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
      exact symplecticCoreEquiv_mk h hF e z
    · rintro ⟨z,hz,rfl⟩
      refine ⟨toStarImage X R z,?_,(symplecticCoreEquiv_mk h hF e z).symm⟩
      exact ⟨inclusion (show X ≤ X ⊔ R from le_sup_left) z,⟨hz,z.property⟩,rfl⟩
  simpa only [he] using star_symplectic_marked_parabolic_from_source h e (by omega)

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

private theorem component_sylow_in_local
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup G}
    (hX : X ∈ Chapter1.cComponentsIn I) :
    ∃ P : Sylow 2 X, (P : Subgroup X) ≤ H.subgroupOf X := by
  obtain ⟨P,hP⟩ := component_sylow_in_plane d hI hX
  exact ⟨P, hP.trans (fun _ hx =>
    (inf_le_left.trans d.geometry.outside.1.1.2) hx)⟩


/-- Solvability of H and the original cubic rank force even symplectic field degree. -/
theorem normalized_component_symplectic_degree_even
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* Sp F) : Even n := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  have hlarge : 3 < Nat.card F := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    omega
  let eCore := symplecticCoreEquiv h hlarge e
  let f := eCore.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hf : Function.Surjective f := eCore.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ eCore.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hr : 2 ≤ primeRank 3 (Sp F) :=
    Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Sp F)).subtype
        (commutator (Sp F)).subtype_injective)
  have hthree : 3 ∣ Nat.card X := by
    have hd : 3 ∣ Nat.card (Sp F) := by
      by_contra hh
      have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hh
      omega
    exact hd.trans (card_dvd_of_surjective f hf)
  have hd := residual_intersection_three_dvd d hI selection.component.1
    selection.residual_normalizes hthree
  have hd' : 3 ∣ Nat.card (H.subgroupOf X) := by
    have hm := hd.trans (card_dvd_of_le
      (le_inf (inf_le_left.trans (map_subtype_le _)) inf_le_right :
        (pResidual 2 H).map H.subtype ⊓ X ≤ H ⊓ X))
    rwa [←subgroupOf_map_subtype H X,card_map_of_injective X.subtype_injective] at hm
  obtain ⟨P,hP⟩ := component_sylow_in_local d hI selection.component
  let Q := P.mapSurjective hf
  let J := H.subgroupOf X
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
  have hthreeImage : 3 ∣ Nat.card (J.map f) := by
    by_contra hh
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hh
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3) f hk] at hz
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz hd'
  exact solvable_sylow_overgroup_degree_even hn hF Q (J.map f) hs (map_mono hP) hthreeImage


/-- The same original symplectic row has even field degree and a full-core
marking identifying its actual NI intersection with a maximal parabolic. -/
theorem normalized_component_symplectic_marking
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* Sp F) :
    Even n ∧ ∃ a : (X ⧸ pCore 2 X) ≃* Sp F,
      (∀ x : X, a (QuotientGroup.mk' (pCore 2 X) x) =
        e (toStarImage X ((M ⊓ I).pCoreIn 2) x)) ∧
      ∃ g : Sp F,
        (((M ⊓ I).subgroupOf X).map
          (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X)))).map
            (MulAut.conj g).toMonoidHom = pointParabolic ∨
        (((M ⊓ I).subgroupOf X).map
          (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X)))).map
            (MulAut.conj g).toMonoidHom = planeParabolic := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  have hlarge : 3 < Nat.card F := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    omega
  exact ⟨normalized_component_symplectic_degree_even d hI hcore selection hn hF e,
    symplecticCoreEquiv h hlarge e, symplecticCoreEquiv_mk h hlarge e,
    symplectic_core_parabolic h hlarge e⟩


/-- A nonbinary symplectic row cannot occur on the original normalized component. -/
theorem normalized_component_symplectic_false
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* Sp F) : False := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  have hlarge : 3 < Nat.card F := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    omega
  let a := symplecticCoreEquiv h hlarge e
  let f := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hf : Function.Surjective f := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,QuotientGroup.ker_mk']
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
    (solvable_sylow_overgroup_normalizes (by omega) Q (J.map f) hs (map_mono hPJ)).trans
      (normalizer_le_marked_parabolic hF hn.le Q (N.map f) (map_mono hPN)
        (symplectic_core_parabolic h hlarge e))
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
  have hr : 2 ≤ primeRank 3 (Sp F) :=
    Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Sp F)).subtype
        (commutator (Sp F)).subtype_injective)
  have hthree : 3 ∣ Nat.card X := by
    have hd : 3 ∣ Nat.card (Sp F) := by
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
