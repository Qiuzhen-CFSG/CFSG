module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree

public import Theory.GroupTheory.SmallFittingResidual
public import Theory.GroupTheory.PrimeRankNormalPair
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# Field parity in the original linear-three component branch

The full SL₃ model makes the canonical core-to-star map an isomorphism.
Consequently the original M ∩ X parabolic contains the scalar-center
preimage. For even field degree that preimage has positive 3-rank.
The two-perfect K centralizes its cubic quotient, so it and K normalize
each other. Their intersection lies in K ∩ M = O₂(K); their ranks therefore
add, contradicting the ambient bound m₃(I) ≤ 2.

This proves odd field degree from the literal Branch and preceding source
hypotheses, without asserting the false containment of the whole central
preimage in K. The opposite-parabolic and binary exclusions remain to be
proved in the final branch assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
15.2.23, printed p.1116; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

variable {G : Type*} [Group G] [Finite G]
variable {M I X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]

/-- The two displayed SL₃ models force the canonical quotient map to be bijective. -/
theorem Branch.coreToStar_bijective (b : Branch M I X n F) :
    Function.Bijective (coreToStar b.input.normalizes) := by
  obtain ⟨e⟩ := b.ms.1.model
  obtain ⟨e', _⟩ := b.parabolic
  exact (Nat.bijective_iff_surjective_and_card _).mpr
    ⟨coreToStar_surjective b.input.normalizes,
      (Nat.card_congr e.toEquiv).trans (Nat.card_congr e'.toEquiv).symm⟩

/-- The canonical identification of the core quotient with the star component. -/
noncomputable def Branch.coreStarEquiv (b : Branch M I X n F) :
    (X ⧸ pCore 2 X) ≃* starImage X ((M ⊓ I).pCoreIn 2) X :=
  MulEquiv.ofBijective (coreToStar b.input.normalizes) b.coreToStar_bijective

/-- The identification preserves the original quotient maps. -/
theorem Branch.coreStarEquiv_mk (b : Branch M I X n F) (x : X) :
    b.coreStarEquiv (QuotientGroup.mk' (pCore 2 X) x) =
      toStarImage X ((M ⊓ I).pCoreIn 2) x := by rfl

/-- On X, the actual star kernel is exactly O₂(X). -/
theorem Branch.toStarImage_ker (b : Branch M I X n F) :
    (toStarImage X ((M ⊓ I).pCoreIn 2)).ker = pCore 2 X := by
  apply le_antisymm
  · intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply b.coreToStar_bijective.1
    change coreToStar b.input.normalizes (QuotientGroup.mk' (pCore 2 X) x) =
      coreToStar b.input.normalizes 1
    rw [coreToStar_mk, map_one]
    exact hx
  · exact core_le_toStarImage_ker b.input.normalizes

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
theorem Branch.coreStarEquiv_map_intersection (b : Branch M I X n F) :
    (((M ⊓ X).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
      b.coreStarEquiv.toMonoidHom =
        (starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
          (starImage X ((M ⊓ I).pCoreIn 2) X) := by
  rw [map_map]
  exact map_intersection_toStar _ b.input.component.1

/-- Transfer the marked parabolic through the canonical core-to-star map. -/
theorem Branch.core_parabolic (b : Branch M I X n F) :
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
theorem Branch.quotient_center_le_intersection (b : Branch M I X n F) :
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
theorem Branch.central_preimage_le_intersection (b : Branch M I X n F)
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

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree

namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
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

/-- The original K = O²(H) has 3-rank two, by its actual wreath quotient. -/
theorem residual_rank_two :
    primeRank 3 ((pResidual 2 H).map H.subtype) = 2 := by
  obtain ⟨e⟩ := d.geometry.quotient
  let ew := RegularWreathProduct.congr SLTwoPermThree.sl2Two_equiv_perm_three.some.symm
    (MulEquiv.refl (Multiplicative (ZMod 2)))
  obtain ⟨er⟩ := WreathTwoResidual.residual_core_quotient_equiv_elementaryNine (e.trans ew)
  rw [← primeRank_congr 3 ((pResidual 2 H).equivMapOfInjective
    H.subtype H.subtype_injective),
    ← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 (pResidual 2 H)) pCore_isPGroup,
    primeRank_congr 3 er]
  let : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) := {
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      apply Multiplicative.toAdd.injective
      ext i
      change (3 : ℕ) • x.toAdd i = 0
      exact (show ∀ a : ZMod 3, (3 : ℕ) • a = 0 by decide +kernel) _ }
  rw [← IsElementaryAbelian.log_card_eq_primeRank (p := 3)]
  norm_num [Nat.card_eq_fintype_card]

/-- Even field degree contradicts quasithinness via mutually normalizing
K and the central preimage, with their genuine two-group intersection. -/
theorem Branch.not_even {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : Branch M I X n F) (hI : PlaneEscapes Mc ZS I) : ¬ Even n := by
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
  obtain ⟨e⟩ := b.ms.1.model
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

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
