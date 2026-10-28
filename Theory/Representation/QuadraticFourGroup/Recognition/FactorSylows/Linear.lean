module

public import Theory.LinearAlgebra.MatrixTwoCentralizer
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.IntegralDomain

/-!
# Odd p-groups in degree-two determinant-one representations

A finite odd p-group represented faithfully in SL₂ over a characteristic-two
field is cyclic. A nonidentity central element is nonscalar, so the matrix
centralizer theorem makes every group element preserve an eigenline over an
algebraic closure. The action on that line is faithful: a determinant-one
matrix fixing a nonzero vector in characteristic two has square one. Thus
the group embeds in the multiplicative group of a field and is cyclic.

This is the elementary matrix input to GLS, volume 2, Theorem 25.14,
Steps 2--3 (`refs/KGroup/GLS2/ChapterG.tex`), where cyclic odd Sylow subgroups
exclude odd central covering kernels via Lemma 15.12(iv).
-/

open Matrix

namespace Matrix.SL2
variable {F : Type*} [Field F] [CharP F 2]
private theorem sq_eq_one_of_fixed_vector (A : SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) (hv : v ≠ 0)
    (hfix : A.val *ᵥ v = v) : A ^ 2 = 1 := by
  have hd : det (A.val - 1) = 0 := exists_mulVec_eq_zero_iff.mp
    ⟨v, hv, by simpa only [sub_mulVec, one_mulVec, sub_eq_zero] using hfix⟩
  have ha := A.property
  have ht : A.val 0 0 + A.val 1 1 = 0 := by
    simp [det_fin_two] at hd
    simp only [det_fin_two] at ha
    have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
    linear_combination ha - hd + htwo
  have hi : A = A⁻¹ := by
    apply Subtype.ext
    change A.val = adjugate A.val
    rw [adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]
    · exact (eq_neg_of_add_eq_zero_left ht).trans (CharTwo.neg_eq _)
    · exact ((eq_neg_of_add_eq_zero_left ht).trans (CharTwo.neg_eq _)).symm
  rw [pow_two]
  exact (congrArg (· * A) hi).trans (inv_mul_cancel A)

private theorem cyclic_of_injective_of_algClosed [IsAlgClosed F]
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]
    (hP : IsPGroup p P) (hp2 : p ≠ 2)
    (ρ : P →* SpecialLinearGroup (Fin 2) F) (hρ : Function.Injective ρ) :
    IsCyclic P := by
  classical
  rcases subsingleton_or_nontrivial P with hPsub | hPnontriv
  · let := hPsub
    infer_instance
  let := hPnontriv
  let := hP.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center P)
  let A := ρ (z : P)
  have hA : ¬ ∃ a : F, A.val = a • 1 := by
    rintro ⟨a, ha⟩
    have hdet := A.property
    rw [ha, det_smul, det_one, Fintype.card_fin, mul_one] at hdet
    have ha1 : a = 1 := CharTwo.sq_injective (by simpa using hdet)
    have hA1 : A = 1 := Subtype.ext (by simpa [ha1] using ha)
    apply hz
    apply Subtype.ext
    exact hρ (hA1.trans ρ.map_one.symm)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A.val)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hAv : A.val *ᵥ v = μ • v := hv.apply_eq_smul
  have hχ : ∀ x : P, ∃ c : F, (ρ x).val *ᵥ v = c • v := by
    intro x
    have hcomm : A.val * (ρ x).val = (ρ x).val * A.val := by
      have hzcomm := (Subgroup.mem_center_iff.mp z.property x).symm
      have heq : A * ρ x = ρ x * A := by
        simpa only [map_mul] using congrArg ρ hzcomm
      exact congrArg (fun g : SpecialLinearGroup (Fin 2) F => g.val) heq
    obtain ⟨a, b, hab⟩ := exists_eq_smul_one_add_smul_of_commute_two
      A.val (ρ x).val hA hcomm
    refine ⟨a + b * μ, ?_⟩
    rw [hab, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hAv,
      smul_smul, add_smul]
  let χ : P → F := fun x => (hχ x).choose
  have hχspec (x : P) : (ρ x).val *ᵥ v = χ x • v := (hχ x).choose_spec
  let f : P →* F := {
    toFun := χ
    map_one' := by
      apply smul_left_injective F hv.2
      change χ 1 • v = (1 : F) • v
      rw [← hχspec]
      simp
    map_mul' := by
      intro x y
      apply smul_left_injective F hv.2
      change χ (x * y) • v = (χ x * χ y) • v
      rw [← hχspec, map_mul, SpecialLinearGroup.coe_mul, ← mulVec_mulVec,
        hχspec, mulVec_smul, hχspec, smul_smul, mul_comm]
  }
  apply isCyclic_of_injective_ringHom f
  apply (injective_iff_map_eq_one f).mpr
  intro x hx
  have hfix : (ρ x).val *ᵥ v = v := by
    rw [hχspec, show χ x = 1 from hx, one_smul]
  have hsq : x ^ 2 = 1 := hρ (by
    simpa only [map_pow, map_one] using sq_eq_one_of_fixed_vector (ρ x) v hv.2 hfix)
  have hcop := hP.orderOf_coprime (hp.out.odd_of_ne_two hp2).coprime_two_right x
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp
    (by simpa only [hcop.gcd_eq_one] using
      Nat.dvd_gcd (dvd_refl (orderOf x)) (orderOf_dvd_of_pow_eq_one hsq)))

/-- Finite odd p-groups admitting a faithful degree-two determinant-one
representation in characteristic two are cyclic. -/
public theorem odd_pGroup_isCyclic_of_injective
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hp2 : p ≠ 2)
    (ρ : P →* SpecialLinearGroup (Fin 2) F) (hρ : Function.Injective ρ) :
    IsCyclic P := by
  let ι := SpecialLinearGroup.map (n := Fin 2) (algebraMap F (AlgebraicClosure F))
  apply cyclic_of_injective_of_algClosed hP hp2 (ι.comp ρ)
  intro x y hxy
  apply hρ
  apply Subtype.ext
  ext i j
  apply (algebraMap F (AlgebraicClosure F)).injective
  exact congrArg (fun g : SpecialLinearGroup (Fin 2) (AlgebraicClosure F) => g.val i j) hxy

end Matrix.SL2
