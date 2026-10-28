module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryKernel

/-!
# Residual control of the conjugate displacement

Once the local-component argument establishes O²(N_L(U)) normal in N_G(U),
its commutator with C_G(U) lies in the kernel of its natural action on U,
which is its intrinsic two-core. That core centralizes the original layer
and its normalizer closure. Consequently the residual preserves [A,B] for
every A centralizing U: its conjugation changes A only by elements which
act trivially on B. This supplies the normalization calculation for the
conjugate line in source 6.1.14(5).

Relative normality is an explicit remaining premise of the contained-branch
owner qt-d-1222-rankone-recognition-natural-contained.
Source: Aschbacher–Smith, 6.1.14(5), printed p.671.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {L M B U : Subgroup G} {n : ℕ}

/-- Relative normality forces every centralizer commutator into the residual's
actual action kernel; no Sylow lift is needed for this consequence. -/
theorem field_fixedSpace_centralizer_commutator
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) (hn : 2 < n)
    (hN : ((fieldLocalResidual L U).subgroupOf (normalizer (U : Set G))).Normal) :
    ⁅centralizer (U : Set G), fieldLocalResidual L U⁆ ≤ (fieldLocalResidual L U).pCoreIn 2 := by
  have hR : fieldLocalResidual L U ≤ normalizer (U : Set G) :=
    (map_subtype_le _).trans inf_le_right
  have hNR := (normal_subgroupOf_iff_le_normalizer hR).mp hN
  have hNC : normalizer (U : Set G) ≤ normalizer (centralizer (U : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (U : Set G))).mp
      (normal_subgroupOf_centralizer_normalizer (U : Set G))
  obtain ⟨m, _, _, hRU⟩ := field_fixedSpace_natural hn hnatural hfield hUne
  obtain ⟨F, _, _, _, _, hmodel⟩ := hRU
  rw [← hmodel.centralizer_eq_core (Representation.specialLinearNatural_injective 2)]
  exact le_inf (le_normalizer_iff_commutator_le_right.mp
    ((Subgroup.centralizer_le_normalizer _).trans hNR))
    (le_normalizer_iff_commutator_le_left.mp (hR.trans hNC))

/-- On the entire normalizer closure, the centralizer of U commutes with the
residual action, once the source local-component argument proves normality. -/
theorem field_fixedSpace_centralizer_commutator_closure
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) (hn : 2 < n)
    (hN : ((fieldLocalResidual L U).subgroupOf (normalizer (U : Set G))).Normal) :
    ⁅centralizer (U : Set G), fieldLocalResidual L U⁆ ≤
      centralizer (fieldModuleClosure B U : Set G) :=
  (field_fixedSpace_centralizer_commutator hnatural hfield hUne hn hN).trans
    (field_fixedSpace_core_centralizes_closure hnatural hfield hUne hn hN)
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open scoped commutatorElement
universe u
variable {G : Type u} [Group G]

/-- Commuting actions modulo the pointwise kernel preserve displacement. -/
theorem normalizes_displacement_of_commutator_centralizes
    (K A B : Subgroup G) (hKB : K ≤ normalizer (B : Set G))
    (hAK : ⁅A, K⁆ ≤ centralizer (B : Set G)) :
    K ≤ normalizer (⁅A, B⁆ : Subgroup G) := by
  apply le_normalizer_closure_iff.mpr
  rintro k hk _ ⟨a, ha, b, hb, rfl⟩
  let b' := k * b * k⁻¹
  have hb' : b' ∈ B := (mem_normalizer_iff.mp (hKB hk) b).mp hb
  have hc : ⁅a⁻¹, k⁆ ∈ centralizer (B : Set G) :=
    hAK (commutator_mem_commutator (A.inv_mem ha) hk)
  have hcb : ⁅⁅a⁻¹, k⁆, b'⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (mem_centralizer_iff.mp hc b' hb').symm
  have he : k * ⁅a, b⁆ * k⁻¹ = ⁅a, b'⁆ := by
    calc
      k * ⁅a, b⁆ * k⁻¹ = ⁅k * a * k⁻¹, b'⁆ := by
        exact map_commutatorElement (MulAut.conj k).toMonoidHom a b
      _ = ⁅a * ⁅a⁻¹, k⁆, b'⁆ := by congr 1; simp [commutatorElement_def, mul_assoc]
      _ = ⁅a, b'⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul, hcb]
        simp
  rw [he]
  exact commutator_mem_commutator ha hb'

variable [Finite G] {L M B U A : Subgroup G} {n : ℕ}

/-- The local-component normality premise makes the residual preserve the
literal commutator with every subgroup centralizing U. -/
theorem field_fixedSpace_residual_normalizes_displacement
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) (hn : 2 < n)
    (hN : ((fieldLocalResidual L U).subgroupOf (normalizer (U : Set G))).Normal)
    (hA : A ≤ centralizer (U : Set G)) :
    fieldLocalResidual L U ≤ normalizer (⁅A, B⁆ : Subgroup G) := by
  have hKL : fieldLocalResidual L U ≤ L := (map_subtype_le _).trans inf_le_left
  have hLB : L ≤ normalizer (B : Set G) := by
    obtain ⟨_, _, _, _, _, hmodel⟩ := hnatural
    exact hmodel.normalizes
  apply normalizes_displacement_of_commutator_centralizes _ _ _ (hKL.trans hLB)
  exact ((commutator_mono hA le_rfl).trans
    (field_fixedSpace_centralizer_commutator hnatural hfield hUne hn hN)).trans
      (field_fixedSpace_core_centralizes hnatural hfield hUne hn).2
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
