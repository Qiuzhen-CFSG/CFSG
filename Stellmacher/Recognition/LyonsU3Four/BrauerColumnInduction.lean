module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveSectionSupport
public import Stellmacher.Recognition.LyonsU3Four.CentralizerFiveActionCompatibility
public import Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
public import Theory.GroupTheory.OddKernelCyclicRoots
public import Theory.Character.Induction

/-!
# Transfer of genuine local section columns

Cyclic root support of the actual local columns survives the odd-core quotient,
using the supplied identification of the Sylow subgroup. Completeness of the
ambient ordinary table then gives the final assembly of induction from its
principal and nonprincipal scalar products. The identification of these scalar
products is a separate principal-block restriction calculation.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), p. 381,
Brauer's transfer preceding Lemma 4.
-/

public section
noncomputable section
namespace Stellmacher.Recognition.LyonsU3Four
open scoped BigOperators
open Subgroup ModularBlock PrincipalBlockConstruction
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    {α : FiveComplement →* MulAut S}

/-- Root support survives inflation through the actual odd core of the centralizer. -/
theorem LocalFiveCharacterTable.inflatedSectionClassFunction_eq_zero_of_not_root (T : LocalFiveCharacterTable S α)
    (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    {z : G} (hz : z ∈ centerImage S)
    (e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
      LocalFiveGroup S α)
    (he : ∀ s : S, e (involutionCentralizerQuotientMap S hz s) = SemidirectProduct.inl s)
    (w : QuarticCentralIndex S) (hw : (w.1.1 : G) = z)
    (j : FiveLinearIndex) (a : centralizer ({z} : Set G))
    (ha : z ∉ zpowers (a : G)) :
    T.inflatedSectionClassFunction w (pPrimeCore 2 (centralizer ({z} : Set G))) e j a = 0 := by
  let C := centralizer ({z} : Set G)
  let N := pPrimeCore 2 C
  let zC : C := inclusion (sylow_le_involutionCentralizer S hz) w.1.1
  have hzC : (zC : G) = z := hw
  have hzC2 : zC ^ 2 = 1 := by
    let _ := h.center_elementary
    change (inclusion (sylow_le_involutionCentralizer S hz) w.1.1) ^ 2 = 1
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := 2)
      w.1.1 w.1.property, map_one]
  have hcomm : Commute zC a := by
    apply Subtype.ext
    change (zC : G) * (a : G) = (a : G) * (zC : G)
    rw [hzC]
    exact (mem_centralizer_singleton_iff.mp a.property).symm
  apply T.sectionClassFunction_eq_zero_of_not_root h β hβ hα w j
  intro hx
  have hq : QuotientGroup.mk' N zC ∈ zpowers (QuotientGroup.mk' N a) := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hx
    refine mem_zpowers_iff.mpr ⟨n, e.injective ?_⟩
    rw [map_zpow]
    exact hn.trans (he w.1.1).symm
  have hN : Odd (Nat.card N) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := C))
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp
    ((QuotientGroup.involution_mem_zpowers_iff N hN zC a hzC2 hcomm).mp hq)
  apply ha
  refine mem_zpowers_iff.mpr ⟨n, ?_⟩
  exact (congrArg Subtype.val hn).trans hzC

/-- The induced class function is uniquely determined by its scalar products
with a complete ordinary character family.  This is the abstract uniqueness
step used after the local principal-block trace has identified those scalar
products. -/
private theorem inducedClassFunction_eq_sum_of_scalarProduct
    (H : Subgroup G)
    (b : PrincipalCongruenceBlockData G)
    (Φ : ClassFunction H) (A : b.I → ℂ)
    (hA : ∀ i : b.I,
      scalarProduct G (inducedClassFunction H Φ)
        (ofConjClassFunction (b.chi i)) = A i) :
    inducedClassFunction H Φ =
      ∑ i : b.I, A i • ofConjClassFunction (b.chi i) := by
  classical
  let f : ConjClassFunction G :=
    toConjClassFunction (inducedClassFunction H Φ)
      (inducedClassFunction_isClassFunction H Φ)
  have hf (i : b.I) :
      classFunctionInner f (b.chi i) = A i := by
    dsimp [f]
    rw [classFunctionInner_toConjClassFunction_right]
    exact hA i
  dsimp [f] at hf
  have he := completeFamily_sum_inner_smul_eq b.complete f
  have hpoint (g : G) :
      inducedClassFunction H Φ g =
        ∑ i : b.I, A i * b.chi i (ConjClasses.mk g) := by
    have hg := congrFun he (ConjClasses.mk g)
    dsimp [f] at hg
    rw [toConjClassFunction_apply] at hg
    simp_rw [hf] at hg
    simpa [Pi.smul_apply, smul_eq_mul] using hg.symm
  ext g
  rw [hpoint g]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    ofConjClassFunction_apply]

/-- The full-index form of an ambient involution column.  The two hypotheses
separate principal rows from nonprincipal rows; together they are exactly the
coefficient statement obtained from the local principal projection and
ordinary character orthogonality. -/
theorem inducedClassFunction_eq_iDz_full_column
    (H : Subgroup G) (b : PrincipalCongruenceBlockData G)
    (c : GeneralizedDecompositionData {j // j ∈ b.block}) (i : Fin 5)
    (Φ : ClassFunction H)
    (hblock : ∀ j : {j // j ∈ b.block},
      scalarProduct G (inducedClassFunction H Φ)
        (ofConjClassFunction (b.chi j.val)) = (c.iDz i j : ℂ))
    (hoff : ∀ j : b.I, j ∉ b.block →
      scalarProduct G (inducedClassFunction H Φ)
        (ofConjClassFunction (b.chi j)) = 0) :
    inducedClassFunction H Φ =
      ∑ j : b.I, (if hj : j ∈ b.block then
        (c.iDz i ⟨j, hj⟩ : ℂ) else 0) •
          ofConjClassFunction (b.chi j) := by
  classical
  let A : b.I → ℂ := fun j =>
    if hj : j ∈ b.block then (c.iDz i ⟨j, hj⟩ : ℂ) else 0
  have hA (j : b.I) :
      scalarProduct G (inducedClassFunction H Φ)
        (ofConjClassFunction (b.chi j)) = A j := by
    change scalarProduct G (inducedClassFunction H Φ)
        (ofConjClassFunction (b.chi j)) =
      if hj : j ∈ b.block then (c.iDz i ⟨j, hj⟩ : ℂ) else 0
    by_cases hj : j ∈ b.block
    · rw [dif_pos hj]
      exact hblock ⟨j, hj⟩
    · rw [dif_neg hj]
      exact hoff j hj
  exact inducedClassFunction_eq_sum_of_scalarProduct H b Φ A hA

end Stellmacher.Recognition.LyonsU3Four
