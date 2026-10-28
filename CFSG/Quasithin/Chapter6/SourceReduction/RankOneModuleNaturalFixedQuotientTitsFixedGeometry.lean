module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientTitsCoreProduct
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourHyperplaneFullReduced
public import Theory.GroupTheory.Commutator.RelativeGeneration
import Mathlib.Tactic.FinCases

/-!
# The original Tits core and the fixed space of the original inner Sylow

The full original cores satisfy `R ⊔ Q = S`, and the full Hermitian module
is `B = Ω₁Z(Q)`. Thus `C_B(R) = Ω₁Z(S)`. The same product also places all
inner-Sylow displacements in `R`. The full Hermitian upper-root action
puts its fixed line inside these displacements, so `Ω₁Z(S) ≤ Ω₁Z(R)`.
Consequently the actual Tits component centralizes the original inner
Sylow omega-center. No actor or quotient kernel is replaced.

Source: Aschbacher--Smith 6.1.4, printed pp.665--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
attribute [local instance] SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

private theorem original_core_centralizes_full_module
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n) :
    reducedSubgroup (L ⊔ (T : Subgroup G)) ≤
      centralizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) := by
  intro b hb
  rw [h.reduced_enlargement_eq_omega_core] at hb
  exact ((mem_omegaOneCenterAmbient_iff _ _).mp hb).2.2

omit [Finite G] in
private theorem original_core_le_sylow :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
  simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
    (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] using
    pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

/-- Fixed points of the actual Tits core on the full Hermitian module are
exactly the omega-center of the original inner Sylow. -/
theorem original_hermitian_tits_inner_omega_eq_fixed
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) :
    omegaOneCenterAmbient
        (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) =
      reducedSubgroup (L ⊔ (T : Subgroup G)) ⊓
        centralizer ((K ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) := by
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let R := (K ⊔ (T : Subgroup G)).pCoreIn 2
  let S := ((T : Subgroup G) ⊓ L) ⊔ Q
  have hBQ : B = omegaOneCenterAmbient Q := h.reduced_enlargement_eq_omega_core
  have hBQl : B ≤ Q := by
    intro b hb
    exact ((mem_omegaOneCenterAmbient_iff Q b).mp (hBQ ▸ hb)).1
  have hST : S ≤ (T : Subgroup G) := sup_le inf_le_left original_core_le_sylow
  have hBS : B ≤ S := hBQl.trans le_sup_right
  have hRS : R ⊔ Q = S := original_hermitian_tits_core_sup_original_core
    h hout hm hM₁ hCM₁ hK hnot hqK e
  have hRT : R ≤ S := hRS ▸ le_sup_left
  have hC : (T : Subgroup G) ⊓ centralizer (B : Set G) = Q :=
    full_reduced_hermitian_sylow_centralizer h hm
  apply le_antisymm
  · intro z hz
    obtain ⟨hzS,hz2,hzC⟩ := (mem_omegaOneCenterAmbient_iff S z).mp hz
    have hzCQ : z ∈ centralizer (Q : Set G) :=
      (centralizer_le (show Q ≤ S from le_sup_right)) hzC
    have hzQ : z ∈ Q := hC.le ⟨hST hzS,(centralizer_le hBS) hzC⟩
    have hzB : z ∈ B := by
      rw [hBQ]
      exact (mem_omegaOneCenterAmbient_iff Q z).mpr
        ⟨hzQ,hz2,hzCQ⟩
    exact ⟨hzB,(centralizer_le hRT) hzC⟩
  · have hfixed : B ⊓ centralizer (R : Set G) ≤ centralizer (S : Set G) := by
      rw [←hRS]
      apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp inf_le_right)
        (le_centralizer_iff.mp (inf_le_left.trans (original_core_centralizes_full_module h)))
    intro b hb
    have hbΩ : b ∈ omegaOneCenterAmbient Q := hBQ ▸ hb.1
    exact (mem_omegaOneCenterAmbient_iff S b).mpr
      ⟨hBS hb.1,((mem_omegaOneCenterAmbient_iff Q b).mp hbΩ).2.1,hfixed hb⟩

/-- All displacements of the full module by the actual inner Sylow lie
in the full Tits core. -/
theorem original_hermitian_tits_inner_displacement_le_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) :
    ⁅reducedSubgroup (L ⊔ (T : Subgroup G)),
      ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2⁆ ≤
      (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let J := K ⊔ (T : Subgroup G)
  let R := J.pCoreIn 2
  have hJR : J ≤ normalizer (R : Set G) := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hBJ : B ≤ J :=
    (h.reduced_enlargement.rankOneInput hout).reduced_le_sylow.trans le_sup_right
  have hBR : ⁅R,B⁆ ≤ R := le_normalizer_iff_commutator_le_left.mp (hBJ.trans hJR)
  have hQB : ⁅Q,B⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact le_centralizer_iff.mp (original_core_centralizes_full_module h)
  rw [←original_hermitian_tits_core_sup_original_core h hout hm hM₁ hCM₁ hK hnot hqK e,
    commutator_comm]
  exact commutator_sup_le_of_relative_normal J R Q B R hJR (pCoreIn_le 2 J)
    (original_core_le_sylow.trans le_sup_right) hBR (hQB.le.trans bot_le)

open OrthogonalFourMinus.FiniteModel OrthogonalFourMinus.RankOne
open OrthogonalFourMinus.HermitianEquiv Representation.BinaryOffender
open Matrix.SpecialLinearGroup

private theorem upper_fixed_is_root_difference (Z : Space 2)
    (hZ : Z ∈ fixedSpace (SL2.BinarySmall.hermitian 2) (upperUnipotent (Field 2))) :
    ∃ Y : Space 2, rootDifference 2 1 Y = Z := by
  obtain ⟨hb,hz⟩ := (mem_fixedSpace_upper_iff 2 Z).mp hZ
  let a : fixedField 2 := ⟨Z.val 0 0,entry_fixed 2 Z 0⟩
  obtain ⟨Y,hY⟩ := traceFunctional_surjective 2 a
  refine ⟨offDiagonal 2 (Y.val 0 1),?_⟩
  apply Subtype.ext
  have htrace := congrArg Subtype.val hY
  have htrace' : Y.val 0 1 + Y.val 1 0 = Z.val 0 0 := htrace
  have hz' : Z.val 1 0 = 0 := by rw [←entry_conjugate 2 Z 1 0,hz,map_zero]
  rw [rootDifference_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offDiagonal,coordinates_symm_val,hb,hz,hz',map_one,
      entry_conjugate 2 Y 1 0,add_comm,htrace']

/-- The actual inner Sylow omega-center is contained in the omega-center
of the full original Tits core. -/
theorem original_hermitian_tits_inner_omega_le_core_omega
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) :
    omegaOneCenterAmbient
        (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) ≤
      omegaOneCenterAmbient ((K ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  let R := (K ⊔ (T : Subgroup G)).pCoreIn 2
  let S := ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hRS : R ≤ S := original_hermitian_tits_core_le_inner_sylow
    h hout hm hM₁ hCM₁ hK hnot hqK e
  have hΩ : omegaOneCenterAmbient S = B ⊓ centralizer (R : Set G) :=
    original_hermitian_tits_inner_omega_eq_fixed h hout hm hM₁ hCM₁ hK hnot hqK e
  have hdisp : ⁅S,B⁆ ≤ R := by
    rw [commutator_comm]
    exact original_hermitian_tits_inner_displacement_le_core
      h hout hm hM₁ hCM₁ hK hnot hqK e
  obtain ⟨q,f,W,_,_,hf,hS,hmem,_,_⟩ :=
    original_hermitian_tits_kernel_coordinates h hout hm hM₁ hCM₁ hK hnot hqK e
  have hroot (Y : Space 2) : rootDifference 2 1 Y ∈ W := by
    have hu : upper 2 1 ∈ ((T : Subgroup G).subgroupOf L).map q := by
      rw [hS]
      exact (mem_upperUnipotent _ _).mpr ⟨1,rfl⟩
    obtain ⟨l,hl,hlq⟩ := hu
    obtain ⟨b,hb⟩ := f.surjective (Multiplicative.ofAdd Y)
    let db : B := B.normalizerMonoidHom ⟨l,hm.normalizes l.property⟩ b
    have hdb : (db * b⁻¹ : B).val ∈ R :=
      hdisp (commutator_mem_commutator
        (show (l : G) ∈ S from mem_sup_left ⟨hl,l.property⟩) b.property)
    have hw := (hmem (db*b⁻¹)).mpr hdb
    have he := hf l b
    change (f db).toAdd = action 2 (q l) (f b).toAdd at he
    rw [hlq] at he
    change action 2 (upper 2 1) Y - Y ∈ W
    have hfb : (f b).toAdd = Y := congrArg Multiplicative.toAdd hb
    simpa only [map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg,he,hfb] using hw
  intro z hz
  obtain ⟨hzS,hz2,hzC⟩ := (mem_omegaOneCenterAmbient_iff S z).mp hz
  have hzB : z ∈ B := (hΩ.le hz).1
  let zb : B := ⟨z,hzB⟩
  have hfixed : (f zb).toAdd ∈ fixedSpace (SL2.BinarySmall.hermitian 2)
      (upperUnipotent (Field 2)) := by
    intro u
    have hu : u.val ∈ ((T : Subgroup G).subgroupOf L).map q := hS.symm ▸ u.property
    obtain ⟨l,hl,hlq⟩ := hu
    have hlS : (l : G) ∈ S := mem_sup_left ⟨hl,l.property⟩
    have he : B.normalizerMonoidHom ⟨l,hm.normalizes l.property⟩ zb = zb := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hzC) l hlS)
    have ha := hf l zb
    rw [he,hlq] at ha
    exact ha.symm
  obtain ⟨Y,hY⟩ := upper_fixed_is_root_difference (f zb).toAdd hfixed
  have hzR : z ∈ R := (hmem zb).mp (hY ▸ hroot Y)
  exact (mem_omegaOneCenterAmbient_iff R z).mpr
    ⟨hzR,hz2,(centralizer_le hRS) hzC⟩

/-- The same outside Tits component centralizes the original inner Sylow
omega-center, through the full original core. -/
theorem original_hermitian_tits_component_centralizes_inner_omega
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) :
    ⁅omegaOneCenterAmbient
      (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2),K⁆ = ⊥ := by
  apply bot_unique
  exact (commutator_mono
    (original_hermitian_tits_inner_omega_le_core_omega h hout hm hM₁ hCM₁ hK hnot hqK e)
    le_rfl).trans_eq
      (original_hermitian_tits_component_centralizes_omega h hout hm hM₁ hCM₁ hK hnot hqK e)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
