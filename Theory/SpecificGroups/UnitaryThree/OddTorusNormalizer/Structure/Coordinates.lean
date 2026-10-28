module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Frames
public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Torus
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Coordinates for orthogonal-frame tori in SU₃

In any orthonormal frame, the full special torus consists exactly of the
matrices `P * diag(a,b,(ab)⁻¹) * P⁻¹`, with `a,b` in the norm-one subgroup
of the matrix field. The explicit parametrization is injective and its range
is the published `specialFrameTorus`; no normalizer or placement assertion
is assumed. Finite-field norm calculations give its two cyclic factors.

Source: GLS4, Chapter 4, Lemma 3.11(b),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603; Huppert II.10.4.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.IdentityGram HermitianForm.EvenInner
namespace UnitaryThree.OddTorusNormalizer
variable {E : Type*} [Field E]

theorem diagonalHom_injective : Function.Injective (diagonalHom (E := E)) := by
  intro a b h
  funext i
  apply Units.ext
  simpa [diagonalHom] using congrArg (fun M : GL (Fin 3) E => M.val i i) h

theorem diagonal_mem_identity_special_iff (J : HermitianForm 3 E) (a : Fin 3 → Eˣ) :
    diagonalHom a ∈ (identityGram J).specialSubgroup ↔
      (∀ i, a i ∈ normOne J) ∧ ∏ i, a i = 1 := by
  rw [HermitianForm.mem_specialSubgroup_iff]
  have hadj : (identityGram J).conjTranspose (diagonalHom a).val =
      Matrix.diagonal (fun i => J.conj (a i : E)) := by
    ext i j
    by_cases h : i = j
    · subst j; simp [HermitianForm.conjTranspose, diagonalHom]
    · simp [HermitianForm.conjTranspose, diagonalHom, h, Ne.symm h]
  rw [identityGram_form, mul_one, hadj]
  change Matrix.diagonal (fun i => J.conj (a i : E)) *
      Matrix.diagonal (fun i => (a i : E)) = 1 ∧ _ ↔ _
  rw [Matrix.diagonal_mul_diagonal]
  have hunit : Matrix.diagonal (fun i => J.conj (a i : E) * (a i : E)) = 1 ↔
      ∀ i, a i ∈ normOne J := by
    constructor
    · intro h i
      have hi := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M i i) h
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at hi
      exact eq_inv_of_mul_eq_one_left hi
    · intro h
      ext i j
      by_cases hij : i = j
      · subst j
        simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        rw [show J.conj (a i : E) = (a i : E)⁻¹ from h i]
        exact inv_mul_cancel₀ (Units.ne_zero _)
      · simp [hij]
  rw [hunit]
  apply and_congr_right
  intro _
  have hdet : GeneralLinearGroup.det (diagonalHom a) = ∏ i, a i := by
    apply Units.ext
    change (Matrix.diagonal (fun i => (a i : E))).det = _
    simp [Matrix.det_diagonal]
  rw [hdet]

@[expose] def pairDiagonal (J : HermitianForm 3 E) :
    (normOne J × normOne J) →* (Fin 3 → Eˣ) where
  toFun x := ![x.1.val, x.2.val, (x.1.val * x.2.val)⁻¹]
  map_one' := by ext i; fin_cases i <;> simp
  map_mul' x y := by
    ext i
    fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]

theorem pairDiagonal_mem (J : HermitianForm 3 E) (x : normOne J × normOne J) :
    diagonalHom (pairDiagonal J x) ∈ (identityGram J).specialSubgroup := by
  rw [diagonal_mem_identity_special_iff]
  constructor
  · intro i
    fin_cases i
    · exact x.1.property
    · exact x.2.property
    · exact (normOne J).inv_mem ((normOne J).mul_mem x.1.property x.2.property)
  · simp [pairDiagonal, Fin.prod_univ_three, mul_assoc]

@[expose] def specialPairHom (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    (normOne J × normOne J) →* J.specialSubgroup :=
  (((MulAut.conj P.val).toMonoidHom.comp diagonalHom).comp
    (pairDiagonal J)).codRestrict J.specialSubgroup (fun x =>
      (special_conjugate_iff J P.val _ P.property).mpr (pairDiagonal_mem J x))

theorem specialPairHom_injective (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    Function.Injective (specialPairHom J P) := by
  intro x y h
  have hh : pairDiagonal J x = pairDiagonal J y :=
    diagonalHom_injective ((MulAut.conj P.val).injective (congrArg Subtype.val h))
  apply Prod.ext
  · apply Subtype.ext
    exact congrFun hh 0
  · apply Subtype.ext
    exact congrFun hh 1

theorem specialPairHom_range (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    (specialPairHom J P).range = specialFrameTorus J P := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨pairDiagonal J y, ?_⟩
    change diagonalHom (pairDiagonal J y) =
      P.val⁻¹ * (P.val * diagonalHom (pairDiagonal J y) * P.val⁻¹) * (P.val⁻¹)⁻¹
    simp [mul_assoc]
  · rintro ⟨a, ha⟩
    have hx : P.val * diagonalHom a * P.val⁻¹ = x.val := by
      change diagonalHom a = P.val⁻¹ * x.val * (P.val⁻¹)⁻¹ at ha
      rw [ha]
      simp [mul_assoc]
    have hmem := (special_conjugate_iff J P.val (diagonalHom a) P.property).mp
      (hx ▸ x.property)
    obtain ⟨hn, hd⟩ := (diagonal_mem_identity_special_iff J a).mp hmem
    have h2 : a 2 = (a 0 * a 1)⁻¹ := by
      rw [Fin.prod_univ_three] at hd
      exact eq_inv_of_mul_eq_one_right hd
    refine ⟨(⟨a 0, hn 0⟩, ⟨a 1, hn 1⟩), ?_⟩
    apply Subtype.ext
    change P.val * diagonalHom (pairDiagonal J _) * P.val⁻¹ = x.val
    rw [show pairDiagonal J (⟨a 0, hn 0⟩, ⟨a 1, hn 1⟩) = a by
      ext i; fin_cases i <;> simp [pairDiagonal, h2]]
    exact hx

@[expose] noncomputable def specialFrameTorusEquivNormOne
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    specialFrameTorus J P ≃* normOne J × normOne J :=
  (MulEquiv.subgroupCongr (specialPairHom_range J P).symm).trans
    (MonoidHom.ofInjective (specialPairHom_injective J P)).symm

noncomputable def normOneEquivZMod [Finite E] (J : HermitianForm 3 E) (q : ℕ)
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    normOne J ≃* Multiplicative (ZMod (q + 1)) := by
  have hc := normOne_card J hcard
    (BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J q hcard hfixed)
  exact (zmodCyclicMulEquiv (inferInstance : IsCyclic (normOne J))).symm.trans
    (MulEquiv.cast (M := fun n => Multiplicative (ZMod n)) hc)

/-- The inverse coordinate equivalence is the explicit conjugated diagonal matrix. -/
@[simp] theorem specialFrameTorusEquivNormOne_symm_val
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (x : normOne J × normOne J) :
    ((specialFrameTorusEquivNormOne J P).symm x).val = specialPairHom J P x := rfl

/-- Both cyclic factors of the actual special frame torus have order `q+1`. -/
noncomputable def specialFrameTorusEquivCyclic [Finite E]
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (q : ℕ)
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    specialFrameTorus J P ≃*
      Multiplicative (ZMod (q + 1)) × Multiplicative (ZMod (q + 1)) :=
  (specialFrameTorusEquivNormOne J P).trans
    ((normOneEquivZMod J q hcard hfixed).prodCongr (normOneEquivZMod J q hcard hfixed))

/-- The special torus has order `(q+1)²`. -/
theorem specialFrameTorus_card [Finite E]
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (q : ℕ)
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    Nat.card (specialFrameTorus J P) = (q + 1) ^ 2 := by
  rw [Nat.card_congr (specialFrameTorusEquivCyclic J P q hcard hfixed).toEquiv,
    Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod, pow_two]

end UnitaryThree.OddTorusNormalizer
