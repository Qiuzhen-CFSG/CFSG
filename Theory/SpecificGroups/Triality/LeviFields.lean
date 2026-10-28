module
public import Theory.SpecificGroups.Triality.Parameters
public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The two coefficient fields for the triality Levi subgroups

The q-Frobenius fixed subfield of GF(q³) is identified with GF(q). An
embedding exists because the extension degrees divide; its image has q
elements, while X^q-X bounds the fixed field by q. Entrywise application
then identifies SL₂(GF(q)) with exactly the Frobenius-fixed matrices in
SL₂(GF(q³)). No assertion about the Geck root subgroups is assumed here.

Source: GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`), especially the
orbit-length field restriction in Proposition 2.6.2. The cardinality argument
extends the method in `Theory.FieldTheory.QuadraticFrobeniusFixed` to the cubic
coefficient field used by the genuine triality construction.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard

/-- The actual fixed subfield of q-Frobenius in the cubic coefficient field. -/
def fixedField (P : Parameters) : Subfield (ExtensionField P) :=
  FixedBy.subfield (ExtensionField P) (fieldFrobenius P)

@[simp] theorem mem_fixedField (P : Parameters) (x : ExtensionField P) :
    x ∈ fixedField P ↔ fieldFrobenius P x = x := Iff.rfl

theorem card_baseField (P : Parameters) :
    Nat.card (GaloisField P.prime P.exponent) = P.q :=
  GaloisField.card P.prime P.exponent (Nat.ne_of_gt P.exponent_pos)

/-- An embedding of the base field into the specified cubic field. -/
def baseFieldEmbedding (P : Parameters) :
    GaloisField P.prime P.exponent →ₐ[ZMod P.prime] ExtensionField P :=
  Classical.choice (FiniteField.nonempty_algHom_of_finrank_dvd (by
    rw [GaloisField.finrank P.prime (Nat.ne_of_gt P.exponent_pos),
      GaloisField.finrank P.prime (show 3 * P.exponent ≠ 0 by
        exact Nat.mul_ne_zero (by decide) (Nat.ne_of_gt P.exponent_pos))]
    exact dvd_mul_left _ _))

theorem baseFieldEmbedding_fixed (P : Parameters)
    (a : GaloisField P.prime P.exponent) : baseFieldEmbedding P a ∈ fixedField P := by
  let : Fintype (GaloisField P.prime P.exponent) := Fintype.ofFinite _
  rw [mem_fixedField, fieldFrobenius_apply, ← map_pow]
  congr 1
  rw [← card_baseField P]
  simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card a

/-- The base embedding with codomain restricted to the actual fixed field. -/
def baseFixedEmbedding (P : Parameters) :
    GaloisField P.prime P.exponent →+* fixedField P :=
  (baseFieldEmbedding P).toRingHom.codRestrict (fixedField P) (baseFieldEmbedding_fixed P)

theorem card_fixedField (P : Parameters) : Nat.card (fixedField P) = P.q := by
  classical
  let k := fixedField P
  let : Fintype k := Fintype.ofFinite k
  have hlo : P.q ≤ Nat.card k := by
    rw [← card_baseField P]
    exact Nat.card_le_card_of_injective (baseFixedEmbedding P) (baseFixedEmbedding P).injective
  have hhi : Nat.card k ≤ P.q := by
    let f : Polynomial k := Polynomial.X ^ P.q - Polynomial.X
    have hf : f ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero k
      (Nat.ne_of_gt P.exponent_pos) P.prime_prime.one_lt
    have hroot : (Finset.univ : Finset k).val ⊆ f.roots := by
      intro a _
      rw [Polynomial.mem_roots hf]
      simp only [f, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X]
      apply sub_eq_zero.mpr
      apply Subtype.ext
      exact a.property
    have hd := Polynomial.card_le_degree_of_subset_roots hroot
    have hdeg : f.natDegree ≤ P.q := by
      exact (Polynomial.natDegree_sub_le _ _).trans (by
        simp [Nat.one_le_of_lt (lt_of_lt_of_le (by decide : 0 < 2) P.q_ge_two)])
    simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using hd.trans hdeg
  exact le_antisymm hhi hlo

/-- A coefficient-field identification whose codomain is the specified fixed subfield. -/
def baseFieldEquivFixed (P : Parameters) :
    GaloisField P.prime P.exponent ≃+* fixedField P :=
  RingEquiv.ofBijective (baseFixedEmbedding P)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨(baseFixedEmbedding P).injective, (card_baseField P).trans (card_fixedField P).symm⟩)

end Triality.Standard

open Matrix
open scoped MatrixGroups
noncomputable section
namespace Triality.Standard

/-- The induced determinant-one matrix embedding over the base field. -/
def sl2BaseEmbedding (P : Parameters) :
    SL(2, GaloisField P.prime P.exponent) →* SL(2, ExtensionField P) :=
  SpecialLinearGroup.map (baseFieldEmbedding P).toRingHom

theorem sl2BaseEmbedding_injective (P : Parameters) :
    Function.Injective (sl2BaseEmbedding P) := by
  intro A B h
  ext i j
  exact (baseFieldEmbedding P).injective
    (congrArg (fun C : SL(2, ExtensionField P) => C i j) h)

/-- Its image is exactly the matrices fixed by coefficient q-Frobenius. -/
theorem mem_range_sl2BaseEmbedding (P : Parameters) (A : SL(2, ExtensionField P)) :
    A ∈ (sl2BaseEmbedding P).range ↔
      SpecialLinearGroup.map (fieldFrobenius P).toRingHom A = A := by
  constructor
  · rintro ⟨B, rfl⟩
    ext i j
    exact baseFieldEmbedding_fixed P (B i j)
  · intro h
    have hfixed (i j : Fin 2) : A i j ∈ fixedField P :=
      congrArg (fun C : SL(2, ExtensionField P) => C i j) h
    let B : Matrix (Fin 2) (Fin 2) (fixedField P) := fun i j => ⟨A i j, hfixed i j⟩
    have hdet : B.det = 1 := by
      apply (fixedField P).subtype.injective
      rw [(fixedField P).subtype.map_det, map_one]
      exact A.prop
    let C : SL(2, fixedField P) := ⟨B, hdet⟩
    refine ⟨SpecialLinearGroup.map (baseFieldEquivFixed P).symm.toRingHom C, ?_⟩
    ext i j
    exact congrArg Subtype.val
      ((baseFieldEquivFixed P).apply_symm_apply (B i j))

end Triality.Standard
