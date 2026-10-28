module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.Nonbinary
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.CoreQuotient

/-!
# Binary field recognition before the MS classification

The full core quotient and the marked parabolic suffice for the degree-one
argument in original 15.2.23. Even degree gives a cubic scalar center whose
rank adds to that of the original K. For odd degree greater than one, the
solvable Sylow overgroup H intersect X has order prime to three, whereas
quasithinness forces a cubic intersection with K.

This extracts the argument in LinearThree/{Descent,Intersection,Nonbinary}
with only the core model in place of the MS description. The established
full-field APIs are preserved. No C.1.34 module alternative is used here;
its small-field classification can therefore be applied afterwards.

Source: Aschbacher--Smith, original 15.2.23, printed p.1116;
refs/quasithin.pdf.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue.LinearThreeDegree
open PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

private structure CoreModel {G : Type*} [Group G]
    (M I X : Subgroup G) (n : ℕ) (F : Type) [Field F] [Finite F] : Prop where
  input : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X
  positive : 1 ≤ n
  field_card : Nat.card F = 2 ^ n
  parabolic : IsLinearMaximalParabolic
    ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
      (starImage X ((M ⊓ I).pCoreIn 2) X)) 3 F
  model : Nonempty ((X ⧸ pCore 2 X) ≃* SL(3,F))

variable {G : Type*} [Group G] [Finite G]
variable {M I X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]

/-- The two displayed SL₃ models force the canonical quotient map to be bijective. -/
private theorem CoreModel.coreToStar_bijective (b : CoreModel M I X n F) :
    Function.Bijective (coreToStar b.input.normalizes) := by
  obtain ⟨e⟩ := b.model
  obtain ⟨e', _⟩ := b.parabolic
  exact (Nat.bijective_iff_surjective_and_card _).mpr
    ⟨coreToStar_surjective b.input.normalizes,
      (Nat.card_congr e.toEquiv).trans (Nat.card_congr e'.toEquiv).symm⟩

/-- The canonical identification of the core quotient with the star component. -/
private noncomputable def CoreModel.coreStarEquiv (b : CoreModel M I X n F) :
    (X ⧸ pCore 2 X) ≃* starImage X ((M ⊓ I).pCoreIn 2) X :=
  MulEquiv.ofBijective (coreToStar b.input.normalizes) b.coreToStar_bijective

omit [Finite G] in
private theorem map_intersection_toStar (R : Subgroup G) (hXI : X ≤ I) :
    ((M ⊓ X).subgroupOf X).map (toStarImage X R) =
      (starM X R (M ⊓ I)).subgroupOf (starImage X R X) := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,mem_sup_left x.property⟩,⟨⟨hx.1,hXI hx.2⟩,hx.2⟩,rfl⟩
  · rintro ⟨x,hx,he⟩
    refine ⟨⟨x,hx.2⟩,⟨hx.1.1,hx.2⟩,?_⟩
    exact Subtype.ext he

/-- The original M ∩ X maps to the marked star parabolic. -/
private theorem CoreModel.coreStarEquiv_map_intersection (b : CoreModel M I X n F) :
    (((M ⊓ X).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
      b.coreStarEquiv.toMonoidHom =
        (starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
          (starImage X ((M ⊓ I).pCoreIn 2) X) := by
  rw [map_map]
  exact map_intersection_toStar _ b.input.component.1

/-- Transfer the marked parabolic through the canonical core-to-star map. -/
private theorem CoreModel.core_parabolic (b : CoreModel M I X n F) :
    IsLinearMaximalParabolic
      (((M ⊓ X).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) 3 F := by
  obtain ⟨e,W,hn,hp,he⟩ := b.parabolic
  refine ⟨b.coreStarEquiv.trans e,W,hn,hp,?_⟩
  change (((M ⊓ X).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
    (e.toMonoidHom.comp b.coreStarEquiv.toMonoidHom) = _
  rw [← map_map, b.coreStarEquiv_map_intersection, he]

omit [Finite F] in
private theorem center_le_linearStabilizer (W : Submodule F (Fin 3 → F)) :
    center SL(3,F) ≤ linearStabilizer W := by
  intro g hg
  obtain ⟨r,hr,hg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  change Matrix.SpecialLinearGroup.toLin' g ∈ MulAction.stabilizer _ W
  rw [Submodule.mem_stabilizer_submodule_iff_map_eq]
  change W.map (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) F)) = W
  rw [← hg]
  have hr0 : r ≠ 0 := by
    intro he
    subst r
    norm_num at hr
  apply le_antisymm
  · rintro v ⟨w,hw,rfl⟩
    simpa [Matrix.toLin'_apply, Matrix.scalar_apply, Matrix.diagonal_const_mulVec] using W.smul_mem r hw
  · intro w hw
    refine ⟨r⁻¹ • w,W.smul_mem _ hw,?_⟩
    ext i
    simp [Matrix.toLin'_apply, Matrix.scalar_apply, Matrix.diagonal_const_mulVec, hr0]

/-- The scalar center lies in the image of the original M ∩ X. -/
private theorem CoreModel.quotient_center_le_intersection (b : CoreModel M I X n F) :
    center (X ⧸ pCore 2 X) ≤
      ((M ⊓ X).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)) := by
  obtain ⟨e,W,_,_,he⟩ := b.core_parabolic
  intro x hx
  apply (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
  rw [he]
  exact center_le_linearStabilizer W ((centerCongr e ⟨x,hx⟩).property)

variable {T : Sylow 2 G} {Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include d in
/-- Subnormal core containment lifts the scalar-center inclusion to X. -/
private theorem CoreModel.central_preimage_le_intersection (b : CoreModel M I X n F)
    (hI : PlaneEscapes Mc ZS I) : centralCorePreimage X ≤ M ⊓ X := by
  have hcore : X.pCoreIn 2 ≤ M :=
    (pCoreAmbient_mono_of_isSubnormalIn X I 2 b.input.component.1
      b.input.component.2.subnormal).trans
        ((d.core_le_plane hI).trans (inf_le_left.trans hsource.maximal.1.2))
  have hk : pCore 2 X ≤ (M ⊓ X).subgroupOf X :=
    fun x hx => ⟨hcore (mem_map_of_mem X.subtype hx),x.property⟩
  rintro z ⟨x,hx,rfl⟩
  have hm := b.quotient_center_le_intersection hx
  have hpre := comap_map_eq_self (f := QuotientGroup.mk' (pCore 2 X))
    (show (QuotientGroup.mk' (pCore 2 X)).ker ≤ (M ⊓ X).subgroupOf X by
      rwa [QuotientGroup.ker_mk'])
  exact (show x ∈ (M ⊓ X).subgroupOf X from hpre ▸ hm)

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue.LinearThreeDegree

namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue.LinearThreeDegree
open PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree
open Subgroup Theory.GroupTheory
open Chapter1.RadicalExclusions.ModelReduction
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]

private theorem central_preimage_commutator {X K : Subgroup G}
    (hK : IsPPerfect 2 K) (hn : K ≤ normalizer (X : Set G))
    (hc : Nat.card (center (X ⧸ pCore 2 X)) = 3) :
    ⁅centralCorePreimage X,K⁆ ≤ X.pCoreIn 2 := by
  let a : K →* MulAut (X ⧸ pCore 2 X) :=
    (quotientAut (pCore 2 X)).comp (X.normalizerMonoidHom.comp (inclusion hn))
  let z := (MulAut.characteristic (center (X ⧸ pCore 2 X))).comp a
  have hz := hK.hom_eq_one_of_isPGroup
    (aut_two_of_card_one_or_three _ (Or.inr hc)) z
  have hk : ∀ (k : K) (x : centralPreimage (pCore 2 X)),
      a k (QuotientGroup.mk' (pCore 2 X) x.val) =
        QuotientGroup.mk' (pCore 2 X) x.val := by
    intro k x
    exact congrArg Subtype.val (DFunLike.congr_fun
      (DFunLike.congr_fun hz k) ⟨QuotientGroup.mk' (pCore 2 X) x.val,x.property⟩)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro k hkK x hx
  obtain ⟨v,hv,rfl⟩ := hx
  let k' : normalizer (X : Set G) := ⟨k,hn hkK⟩
  have he := hk ⟨k,hkK⟩ ⟨v,hv⟩
  change quotientAut (pCore 2 X) (X.normalizerMonoidHom k')
    (QuotientGroup.mk' (pCore 2 X) v) = QuotientGroup.mk' (pCore 2 X) v at he
  rw [quotientAut_apply_mk] at he
  have hm : X.normalizerMonoidHom k' v * v⁻¹ ∈ pCore 2 X := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 X) (X.normalizerMonoidHom k' v * v⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  exact mem_map_of_mem X.subtype hm

variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Even field degree contradicts quasithinness via mutually normalizing
K and the central preimage, with their genuine two-group intersection. -/
private theorem CoreModel.not_even {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : CoreModel M I X n F) (hI : PlaneEscapes Mc ZS I) : ¬ Even n := by
  intro hn
  let K := (pResidual 2 H).map H.subtype
  let C := centralCorePreimage X
  have hKX : K ≤ normalizer (X : Set G) := by
    have hh := d.residual_normalizes_component hI b.input.component.2
    rwa [map_subgroupOf_eq_of_le b.input.component.1] at hh
  have hCX : C ≤ X := map_subtype_le _
  have hCI : C ≤ I := hCX.trans b.input.component.1
  have hKI : K ≤ I :=
    (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  obtain ⟨e⟩ := b.model
  have hz : Nat.card (center (X ⧸ pCore 2 X)) = 3 := by
    rw [Nat.card_congr (centerCongr e).toEquiv]
    apply Matrix.SL3.card_center_eq_three_of_ne_bot F
    intro he
    apply (Matrix.SL3.center_eq_bot_iff_card_mod_three F).mp he
    rw [b.field_card,Nat.BinaryTorusParity.two_pow_mod_three,
      if_pos (Nat.even_iff.mp hn)]
  have hpK : IsPPerfect 2 K := isPPerfect_embedded_pResidual 2 H
  have hc : ⁅C,K⁆ ≤ X.pCoreIn 2 := central_preimage_commutator hpK hKX hz
  have hQS : X.pCoreIn 2 ≤ planeSylow T ZS :=
    (pCoreAmbient_mono_of_isSubnormalIn X I 2 b.input.component.1
      b.input.component.2.subnormal).trans (d.core_le_plane hI)
  have hSK : planeSylow T ZS ≤ normalizer (K : Set G) :=
    (inf_le_left.trans d.geometry.outside.1.1.2).trans
      (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H)))
  have heK : (pResidual 2 K).map K.subtype = K := by
    rw [(pResidual_eq_top_iff 2 K).mpr hpK,← MonoidHom.range_eq_map,range_subtype]
  have hCK : C ≤ normalizer (K : Set G) := by
    have hh := normalizes_residual_of_commutator_le_two C (planeSylow T ZS) K
      (X.pCoreIn 2) hSK hQS (isPGroup_pCoreIn 2 X)
      (hCX.trans (X.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))
      (by simpa only [heK] using hc)
    simpa only [heK] using hh
  have hKC : K ≤ normalizer (C : Set G) := hKX.trans
    (normalizer_le_normalizer_characteristic_image X (centralPreimage (pCore 2 X)))
  have hCM : C ≤ M := (b.central_preimage_le_intersection d hI).trans inf_le_left
  have htwo : IsPGroup 2 (K ⊓ C : Subgroup G) := by
    apply (isPGroup_pCoreIn 2 K).to_le
    rw [← residual_intersection_eq_core d]
    exact inf_le_inf_left K hCM
  have hrank := primeRank_add_le_of_normalizes_of_twoGroup_intersection (by decide : Odd 3)
    K C hKC hCK htwo
  have hu : primeRank 3 (K ⊔ C : Subgroup G) ≤ 2 :=
    (primeRank_mono 3 (sup_le hKI hCI)).trans
      ((Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
        3 Nat.prime_three (by decide))
  have hCpos : 1 ≤ primeRank 3 C := by
    have hd : 3 ∣ Nat.card C := by
      have hh := (centralPreimage (pCore 2 X)).card_map_dvd (QuotientGroup.mk' (pCore 2 X))
      rw [map_centralPreimage,hz] at hh
      simpa only [C,centralCorePreimage,card_map_of_injective X.subtype_injective] using hh
    by_contra hh
    have hzero : primeRank 3 C = 0 := by omega
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp hzero hd
  have hrK : primeRank 3 K = 2 := residual_rank_two d
  omega

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue.LinearThreeDegree


open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue.LinearThreeDegree
open PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include d in
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

include d in
/-- The original rank-two residual meets X in a subgroup of order divisible by three. -/
private theorem CoreModel.residual_component_intersection_three_dvd
    {X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : CoreModel M I X n F) (hI : PlaneEscapes Mc ZS I) :
    3 ∣ Nat.card ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G) := by
  have hKX : (pResidual 2 H).map H.subtype ≤ normalizer (X : Set G) := by
    have hh := d.residual_normalizes_component hI b.input.component.2
    rwa [map_subgroupOf_eq_of_le b.input.component.1] at hh
  apply residual_intersection_three_dvd d hI b.input.component.1 hKX
  obtain ⟨e⟩ := b.model
  have hd : 3 ∣ Nat.card (X ⧸ pCore 2 X) := by
    rw [Nat.card_congr e.toEquiv]
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using b.field_card)
    exact Theory.SpecificGroups.three_dvd_card_sl_three F
  exact hd.trans (by simpa only [index_eq_card] using (pCore 2 X).index_dvd_card)

include d in
/-- The same cubic intersection lies in the actual C_X(ZS). -/
private theorem CoreModel.residual_centralizer_intersection_three_dvd
    {X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : CoreModel M I X n F) (hI : PlaneEscapes Mc ZS I) :
    3 ∣ Nat.card ((pResidual 2 H).map H.subtype ⊓
      (X ⊓ centralizer (ZS : Set G)) : Subgroup G) := by
  have he : (pResidual 2 H).map H.subtype ⊓ (X ⊓ centralizer (ZS : Set G)) =
      (pResidual 2 H).map H.subtype ⊓ X := by
    apply le_antisymm (inf_le_inf_left _ inf_le_left)
    exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans d.residual_centralizes))
  rw [he]
  exact b.residual_component_intersection_three_dvd d hI

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue.LinearThreeDegree


open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue.LinearThreeDegree
open PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

private theorem source_local_solvable : Group.IsSolvable H := by
  obtain ⟨e⟩ := d.geometry.quotient
  let : Group.IsSolvable BinaryFourPlus.Wreath := BinaryFourPlus.wreath_isSolvable
  let : Group.IsSolvable (H ⧸ pCore 2 H) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  exact Group.isSolvable_of_ker_le_range
    (pCore 2 H).subtype (QuotientGroup.mk' (pCore 2 H))
    (by rw [QuotientGroup.ker_mk',range_subtype])

private theorem component_sylow_in_local
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup G}
    (hX : X ∈ Chapter1.cComponentsIn I) :
    ∃ P : Sylow 2 X, (P : Subgroup X) ≤ H.subgroupOf X := by
  obtain ⟨R,hR⟩ := d.sylow_in_escape hI
  obtain ⟨Q,hQ⟩ := R.exists_subgroupOf_eq_of_subnormal (X.subgroupOf I) hX.2.subnormal
  let e := subgroupOfEquivOfLe hX.1
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  rintro x ⟨y,hy,rfl⟩
  have hyR : (y : I) ∈ R := by
    change y ∈ (R : Subgroup I).subgroupOf (X.subgroupOf I)
    rwa [← hQ]
  have hyS : ((y : I) : G) ∈ planeSylow T ZS := hR ▸ mem_map_of_mem I.subtype hyR
  exact (inf_le_left.trans d.geometry.outside.1.1.2) hyS

/-- The actual H ∩ X has order prime to three when the field degree is odd and greater than one. -/
private theorem CoreModel.local_intersection_threePrime_of_large_odd
    {X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : CoreModel M I X n F) (hI : PlaneEscapes Mc ZS I)
    (hn : 1 < n) (ho : Odd n) : ¬ 3 ∣ Nat.card (H.subgroupOf X) := by
  obtain ⟨e⟩ := b.model
  have hZ : center SL(3,F) = ⊥ := by
    apply (Matrix.SL3.center_eq_bot_iff_card_mod_three F).mpr
    rw [b.field_card,Nat.BinaryTorusParity.two_pow_mod_three,
      if_neg (by simpa only [Nat.even_iff] using (Nat.not_even_iff_odd.mpr ho))]
    decide
  let e' := e.trans (Matrix.SL3.equivProjectiveOfCenterEqBot F hZ)
  let f := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hf : Function.Surjective f := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e'.injective, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨P,hP⟩ := component_sylow_in_local d hI b.input.component
  let Q := P.mapSurjective hf
  let J := H.subgroupOf X
  let : Group.IsSolvable H := source_local_solvable d
  let j : J →* H := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : H => (z : G)) h
  let : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective hj
  let : Group.IsSolvable (J.map f) := Group.isSolvable_of_surjective (f.subgroupMap_surjective J)
  have hN : J.map f ≤ normalizer (Q : Set PSL(3,F)) :=
    Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le
      F (by omega) b.field_card Q (J.map f) inferInstance (map_mono hP)
  have hnot := Matrix.PSL3.LinearThree.BorelStructure.three_not_dvd_card_sylowNormalizer_of_odd
    F ho b.field_card Q
  have hr : primeRank 3 (J.map f) = 0 :=
    PrimeRank.eq_zero_iff_not_dvd_card.mpr (fun hd => hnot (hd.trans (card_dvd_of_le hN)))
  rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3) f hk] at hr
  exact PrimeRank.eq_zero_iff_not_dvd_card.mp hr

/-- The original C.2.7(g) branch must be binary; no opposite-parabolic
or scalar-capture premise is added to the source hypotheses. -/
private theorem CoreModel.degree_eq_one
    {X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : CoreModel M I X n F) (hI : PlaneEscapes Mc ZS I) : n = 1 := by
  by_contra hne
  have hn : 1 < n := by have hp := b.positive; omega
  have ho : Odd n := Nat.not_even_iff_odd.mp (b.not_even d hI)
  have hd := b.residual_centralizer_intersection_three_dvd d hI
  have hle : (pResidual 2 H).map H.subtype ⊓ (X ⊓ centralizer (ZS : Set G)) ≤ H ⊓ X :=
    le_inf (inf_le_left.trans (map_subtype_le _)) (inf_le_right.trans inf_le_left)
  have hd' : 3 ∣ Nat.card (H ⊓ X : Subgroup G) := hd.trans (card_dvd_of_le hle)
  have he : Nat.card (H.subgroupOf X) = Nat.card (H ⊓ X : Subgroup G) := by
    rw [← card_map_of_injective (K := H.subgroupOf X) X.subtype_injective, subgroupOf_map_subtype]
  exact b.local_intersection_threePrime_of_large_odd d hI hn ho (he.symm ▸ hd')

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue.LinearThreeDegree

namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Subgroup Theory.GroupTheory PlaneUniquenessPreceding
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

/-- The original linear-three row has degree one before applying C.1.34.
Only the full core model and the literal marked parabolic are required. -/
theorem linearThree_degree_eq_one_of_core_model
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I)
    (h : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X)
    (n : ℕ) (F : Type) [Field F] [Finite F]
    (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hp : IsLinearMaximalParabolic
      ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
        (starImage X ((M ⊓ I).pCoreIn 2) X)) 3 F)
    (e : (X ⧸ pCore 2 X) ≃* SL(3,F)) : n = 1 :=
  LinearThreeDegree.CoreModel.degree_eq_one d ⟨h,hn,hF,hp,⟨e⟩⟩ hI

/-- Full core recognition discharges the model premise on the same original
component, so the marked star parabolic already forces the binary field. -/
theorem linearThree_degree_eq_one_of_star_parabolic
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I)
    (h : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X)
    (n : ℕ) (F : Type) [Field F] [Finite F]
    (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hp : IsLinearMaximalParabolic
      ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
        (starImage X ((M ⊓ I).pCoreIn 2) X)) 3 F) : n = 1 := by
  have hpar := hp
  obtain ⟨e, _⟩ := hp
  exact linearThree_degree_eq_one_of_core_model d hI h n F hn hF hpar
    (linearThreeCoreEquiv h e)

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
