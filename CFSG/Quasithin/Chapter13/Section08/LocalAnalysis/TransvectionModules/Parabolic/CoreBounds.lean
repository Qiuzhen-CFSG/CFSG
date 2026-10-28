module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# The two local cores in 13.8.6

The conjugate-span description of I₂ and the identity O²(I₂) = L₂ from
13.5.4 make L₂ normal in G₂ = N_G(V₂). Its centralizer identity first gives
[K₂,L₂] ≤ O₂(L₂). Sylow containment places O₂(L₂) in C_H(V₂), hence it
normalizes the literal K₂ = O²(C_H(V₂)). Since K₂ is two-perfect, it is the
two-residual of K₂ O₂(L₂). This product is normalized by L₂, so L₂ normalizes
K₂. The commutator is consequently a normal two-subgroup of K₂ as well.

The final result uses the standing Sylow subgroup and G₁ = N_G(V₁), and
feeds this derived local normality into the conjugate-span calculation of
`Basic`. Normality is relative to the indicated local group throughout.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.5.4,
printed p.916, and the proof of 13.8.6(2),(3), printed p.948. These are
conditional deductions from the displayed earlier identities; this module
does not assert the recognition or rank clauses of 13.8.6.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

private theorem residual_normalizer (E Q A : Subgroup G) (hE : IsPPerfect 2 E) (hpQ : IsPGroup 2 Q)
    (hQE : Q ≤ normalizer (E : Set G)) (hAQ : A ≤ normalizer (Q : Set G))
    (hc : ⁅E, A⁆ ≤ Q) : A ≤ normalizer (E : Set G) := by
  have hAJ : A ≤ normalizer ((E ⊔ Q : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro a ha x hx
    have hm : (E ⊔ Q).map (MulAut.conj a).toMonoidHom ≤ E ⊔ Q := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨y, hy, rfl⟩
        have hay : ⁅a, y⁆ ∈ Q := by
          rw [commutator_comm] at hc
          exact hc (commutator_mem_commutator ha hy)
        have hh := (E ⊔ Q).mul_mem ((show Q ≤ E ⊔ Q from le_sup_right) hay)
          ((show E ≤ E ⊔ Q from le_sup_left) hy)
        change a * y * a⁻¹ ∈ E ⊔ Q
        simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
      · rintro _ ⟨y, hy, rfl⟩
        exact (show Q ≤ E ⊔ Q from le_sup_right)
          ((mem_normalizer_iff.mp (hAQ ha) y).mp hy)
    exact hm (mem_map_of_mem _ hx)
  have he := embedded_pResidual_join_pGroup E Q hE hpQ hQE
  rw [← he]
  exact hAJ.trans (normalizer_le_normalizer_characteristic_image _ _)

private theorem core_le_sylow (T : Sylow 2 G) (P : Subgroup G) (hT : (T : Subgroup G) ≤ P) :
    P.pCoreIn 2 ≤ T := by
  have h := pCoreIn_le_sylow P (T.subtype hT)
  rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le hT] at h

/-- The conjugate-span and residual identities in 13.5.4(1),(6) imply local normality. -/
theorem local_normality (I₂ L₂ Q₁ V₂ : Subgroup G)
    (hI : I₂ = conjugateSpanBy Q₁ (normalizer (V₂ : Set G)))
    (hres : L₂ = (pResidual 2 I₂).map I₂.subtype) :
    normalizer (V₂ : Set G) ≤ normalizer (L₂ : Set G) := by
  rw [hres]
  apply le_trans _ (normalizer_le_normalizer_characteristic_image I₂ (pResidual 2 I₂))
  rw [hI]
  exact le_normalizer_conjugateSpanBy _ _

/-- Both core bounds, including the residual-normality step for the first core. -/
theorem core_bounds [Finite G] (T : Sylow 2 G) (H I₂ L₂ Q₁ V₂ : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (hT₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hQ : Q₁ ≤ normalizer (V₂ : Set G))
    (hI : I₂ = conjugateSpanBy Q₁ (normalizer (V₂ : Set G)))
    (hres : L₂ = (pResidual 2 I₂).map I₂.subtype)
    (hcentral : I₂ ⊓ centralizer (V₂ : Set G) = I₂.pCoreIn 2) :
    ⁅Source.K2 H V₂, L₂⁆ ≤ (Source.K2 H V₂).pCoreIn 2 ⊓ L₂.pCoreIn 2 := by
  let C := H ⊓ centralizer (V₂ : Set G)
  let E := Source.K2 H V₂
  have hI₂ : I₂ ≤ normalizer (V₂ : Set G) := by
    rw [hI]
    exact conjugateSpanBy_le_self hQ
  have hL₂ : L₂ ≤ I₂ := hres ▸ map_subtype_le _
  have hLn := local_normality I₂ L₂ Q₁ V₂ hI hres
  have hEn : E ≤ normalizer (L₂ : Set G) :=
    ((Source.K2_le_centralizer H V₂).trans inf_le_right).trans
      ((centralizer_le_normalizer _).trans hLn)
  have hEc : E ≤ centralizer (V₂ : Set G) :=
    (Source.K2_le_centralizer H V₂).trans inf_le_right
  have hLc : L₂ ≤ normalizer (centralizer (V₂ : Set G) : Set G) :=
    (hL₂.trans hI₂).trans
      ((normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (V₂ : Set G))).mp
        inferInstance)
  have hcL : ⁅E, L₂⁆ ≤ L₂ := le_normalizer_iff_commutator_le_right.mp hEn
  have hcC : ⁅E, L₂⁆ ≤ centralizer (V₂ : Set G) :=
    (commutator_mono hEc le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hLc)
  have hci : ⁅E, L₂⁆ ≤ I₂.pCoreIn 2 := by
    rw [← hcentral]
    exact le_inf (hcL.trans hL₂) hcC
  have hcp : IsPGroup 2 (⁅E, L₂⁆ : Subgroup G) := (isPGroup_pCoreIn 2 I₂).to_le hci
  have hc : ⁅E, L₂⁆ ≤ L₂.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hcp hcL (normalizer_commutator_ge_right _ _)
  have hQn : normalizer (V₂ : Set G) ≤ normalizer (L₂.pCoreIn 2 : Set G) :=
    hLn.trans (normalizer_le_normalizer_characteristic_image L₂ (pCore 2 L₂))
  have hQG₂ : L₂.pCoreIn 2 ≤ normalizer (V₂ : Set G) :=
    (pCoreIn_le 2 L₂).trans (hL₂.trans hI₂)
  have hQT : L₂.pCoreIn 2 ≤ T :=
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L₂) hQG₂ hQn).trans
      (core_le_sylow T _ hT₂)
  have hQc : L₂.pCoreIn 2 ≤ centralizer (V₂ : Set G) := by
    have hQi : L₂.pCoreIn 2 ≤ I₂.pCoreIn 2 :=
      le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L₂)
        ((pCoreIn_le 2 L₂).trans hL₂) (hI₂.trans hQn)
    rw [← hcentral] at hQi
    exact hQi.trans inf_le_right
  have hQC : L₂.pCoreIn 2 ≤ C := le_inf (hQT.trans hTH) hQc
  have hCE : C ≤ normalizer (E : Set G) :=
    C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C))
  have hLE : L₂ ≤ normalizer (E : Set G) :=
    residual_normalizer E (L₂.pCoreIn 2) L₂
      (isPPerfect_embedded_pResidual 2 C) (isPGroup_pCoreIn 2 L₂)
      (hQC.trans hCE) ((hL₂.trans hI₂).trans hQn) hc
  exact le_inf (le_pCoreIn_of_normalizes hcp
    (le_normalizer_iff_commutator_le_left.mp hLE) (normalizer_commutator_ge_left _ _)) hc

/-- Apply the local calculation with the actual core of G₁ = N_G(V₁), then
instantiate the conjugate-span calculation from `Basic`. The displayed inputs
are earlier local identities, still to be supplied by the source assembly. -/
theorem source_core_bounds_and_generation [Finite G] (T : Sylow 2 G)
    (H L I₂ L₂ V V₁ V₂ V₃ : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H)
    (hT₁ : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hT₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hI : I₂ = conjugateSpanBy ((normalizer (V₁ : Set G)).pCoreIn 2)
      (normalizer (V₂ : Set G)))
    (hres : L₂ = (pResidual 2 I₂).map I₂.subtype)
    (hcentral : I₂ ⊓ centralizer (V₂ : Set G) = I₂.pCoreIn 2)
    (hL : L₂ ≤ L)
    (hgen : V = conjugateSpanBy V₃ L₂) (hcomm : V = ⁅V, L₂⁆) :
    ⁅Source.K2 H V₂, L₂⁆ ≤ (Source.K2 H V₂).pCoreIn 2 ⊓ L₂.pCoreIn 2 ∧
      Source.U2 H V V₂ = ⁅Source.U2 H V V₂, L₂⁆ ∧
      Source.U2 H V V₂ ≤ Source.UL L H V₃ := by
  refine ⟨core_bounds T H I₂ L₂ _ V₂ hTH hT₂
    ((core_le_sylow T _ hT₁).trans hT₂) hI hres hcentral, ?_⟩
  exact source_U2_eq_commutator_le_UL H L L₂ V V₂ V₃ hL
    (local_normality I₂ L₂ _ V₂ hI hres) hgen hcomm

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic
