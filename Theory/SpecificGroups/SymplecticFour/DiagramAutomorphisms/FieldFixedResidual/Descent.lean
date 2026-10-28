module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.Basic
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Descent of symplectic matrices fixed by a field automorphism

The fixed coefficient field is the literal subfield of fixed elements.
A fixed symplectic matrix descends entry by entry, and the defining symplectic
identity descends through the injective coefficient inclusion. The resulting
multiplicative equivalence retains that inclusion on every element.
For the half-Frobenius on a field of order 2^(2m), the fixed field has order 2^m.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 16.1.4(4), printed p.1171. This computes the
fixed group before taking the two-residual, so it retains the full binary
fixed group whose derived subgroup is needed in that lemma.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual
open Matrix Subgroup
variable {F : Type*} [Field F]

/-- The literal subfield fixed by the coefficient automorphism. -/
def fixedField (σ : F ≃+* F) : Subfield F := FixedBy.subfield F σ

@[simp] theorem mem_fixedField (σ : F ≃+* F) (x : F) :
    x ∈ fixedField σ ↔ σ x = x := by rfl

/-- Coefficient inclusion of the descended symplectic group. -/
def coefficientInclusion (K : Subfield F) : Sp K →* Sp F where
  toFun g := ⟨g.val.map K.subtype, SymplecticGroup.map_mem g.property K.subtype⟩
  map_one' := by apply Subtype.ext; exact (map_one K.subtype.mapMatrix)
  map_mul' g h := by apply Subtype.ext; exact Matrix.map_mul

@[simp] theorem coefficientInclusion_apply (K : Subfield F) (g : Sp K)
    (i j : Fin 2 ⊕ Fin 2) :
    (coefficientInclusion K g).val i j = (g.val i j : F) := by rfl

theorem coefficientInclusion_injective (K : Subfield F) :
    Function.Injective (coefficientInclusion K) := by
  intro g h he
  apply Subtype.ext
  ext i j
  exact congrArg (fun x : Sp F => x.val i j) he

private theorem descends_mem (K : Subfield F) (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (h : A.map K.subtype ∈ Matrix.symplecticGroup (Fin 2) F) :
    A ∈ Matrix.symplecticGroup (Fin 2) K := by
  rw [SymplecticGroup.mem_iff] at h ⊢
  apply Matrix.map_injective K.subtype.injective
  simpa only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_J] using h

/-- A symplectic matrix is fixed precisely when all its coefficients lie in the fixed field. -/
theorem mem_fixed_iff (σ : F ≃+* F) (g : Sp F) :
    g ∈ (fieldAutomorphism σ).fixedSubgroup ↔ ∀ i j, g.val i j ∈ fixedField σ := by
  rw [MulAut.mem_fixedSubgroup]
  constructor
  · intro h i j
    exact congrArg (fun x : Sp F => x.val i j) h
  · intro h
    apply Subtype.ext
    ext i j
    exact h i j

/-- Descent of the actual fixed matrices along coefficient inclusion. -/
def fixedEquiv (σ : F ≃+* F) : (fieldAutomorphism σ).fixedSubgroup ≃* Sp (fixedField σ) where
  toFun g := ⟨fun i j => ⟨g.val.val i j, (mem_fixed_iff σ g.val).mp g.property i j⟩,
    by exact descends_mem (fixedField σ) _ g.val.property⟩
  invFun g := ⟨coefficientInclusion (fixedField σ) g, (mem_fixed_iff σ _).mpr
    (fun i j => (g.val i j).property)⟩
  left_inv g := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv g := by apply Subtype.ext; rfl
  map_mul' g h := by
    apply (coefficientInclusion_injective (fixedField σ))
    change g.val * h.val = coefficientInclusion (fixedField σ) _
    rw [map_mul]
    rfl

@[simp] theorem fixedEquiv_inclusion (σ : F ≃+* F)
    (g : (fieldAutomorphism σ).fixedSubgroup) :
    coefficientInclusion (fixedField σ) (fixedEquiv σ g) = g.val := by rfl

@[simp] theorem fixedEquiv_symm_coe (σ : F ≃+* F) (g : Sp (fixedField σ)) :
    ((fixedEquiv σ).symm g : Sp F) = coefficientInclusion (fixedField σ) g := by rfl

variable [Finite F] [CharP F 2]

/-- The prescribed half-Frobenius representative. -/
abbrev representative (m : ℕ) : MulAut (Sp F) :=
  fieldAutomorphism ((frobeniusEquiv F 2) ^ m)

/-- Its actual fixed coefficient field. -/
abbrev halfField (m : ℕ) : Subfield F := fixedField ((frobeniusEquiv F 2) ^ m)

theorem card_halfField {m : ℕ} (hm : 1 ≤ m) (hF : Nat.card F = 2 ^ (2 * m)) :
    Nat.card (halfField (F := F) m) = 2 ^ m := by
  apply FiniteField.card_fixed_of_quadratic_frobenius _ 2 m (by omega)
  · rw [hF, ← pow_mul]
    congr 1
    omega
  · intro x
    rw [← iterateFrobeniusEquiv_eq_pow, iterateFrobeniusEquiv_def]

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual
