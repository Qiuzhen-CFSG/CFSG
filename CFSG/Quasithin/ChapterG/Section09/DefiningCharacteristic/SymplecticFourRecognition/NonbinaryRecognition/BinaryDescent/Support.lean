module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.TensorModels
public import Theory.Representation.IrreducibleTraceEquivalence
public import Mathlib.Data.Nat.Periodic

/-!
# Frobenius rotation of the concrete symplectic tensor support

The square of the exceptional graph automorphism is entrywise squaring.
Consequently its power 2n is the identity over a field of order 2^n, and
coefficient Frobenius rotates tensor supports by two positions modulo 2n.
The trace is a product of traces of the four-dimensional factors. Equality
of irreducible characters and the explicit catalogue's uniqueness turn
Frobenius invariance into equality of supports. A support fixed by shift
2s, with n = st, has cardinality at for some natural number a.

This is the support and counting argument of GLS3, Remark 2.8.8, applied
to the concrete Sp₄ models in Examples 2.8.10(d). The absolute catalogue
remains an explicit premise.
-/

@[expose] public section

open Representation Fin.NatCast
open scoped MonoidAlgebra TensorProduct
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary
noncomputable section
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- Even graph powers are the corresponding entrywise Frobenius powers. -/
theorem graphDerived_even_apply (r : ℕ) (g : Derived F) (i j : Coordinate) :
    ((graphDerived F ^ (2*r)) g).val.val i j = (g.val.val i j) ^ (2^r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.mul_succ, Nat.add_comm (2*r), pow_add]
    change ((graphDerived F ^ 2) ((graphDerived F ^ (2*r)) g)).val.val i j = _
    rw [graphDerived_square_apply, ih, ← pow_mul, ← pow_succ]

/-- The graph exponents may be read modulo twice the field degree. -/
theorem graphDerived_pow_field {n : ℕ} (hF : Nat.card F = 2^n) :
    graphDerived F ^ (2*n) = 1 := by
  ext g : 1
  apply Subtype.ext
  apply Subtype.ext
  funext i j
  rw [graphDerived_even_apply, ← hF]
  let : Fintype F := Fintype.ofFinite F
  simpa only [Nat.card_eq_fintype_card, MulAut.one_apply] using
    (FiniteField.pow_card (g.val.val i j))

/-- The tensor trace is the product of the traces of its selected factors. -/
theorem tensorModel_character {E : Type*} [Field E] {n : ℕ}
    (e : F →+* E) (S : Finset (Fin (2*n))) (g : Derived F) :
    (tensorModel e S).character g =
      ∏ j ∈ S, ∑ i : Coordinate, e (((graphDerived F ^ (j : ℕ)) g).val.val i i) := by
  classical
  rw [Representation.character, LinearMap.trace_eq_matrix_trace E (Pi.basisFun E _)]
  change (LinearMap.toMatrix' ((tensorMatrix e S g).mulVecLin)).trace = _
  rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  change (∑ x : S → Coordinate, ∏ j : S,
    e (((graphDerived F ^ (j.val : ℕ)) g).val.val (x j) (x j))) = _
  exact (Fintype.prod_sum (fun (j : S) (i : Coordinate) =>
    e (((graphDerived F ^ (j.val : ℕ)) g).val.val i i))).symm.trans
    (Finset.prod_coe_sort S (fun (j : Fin (2*n)) =>
      ∑ i : Coordinate, e (((graphDerived F ^ (j : ℕ)) g).val.val i i)))

/-- Coefficient maps act on the concrete tensor character. -/
theorem tensorModel_character_comp {E : Type*} [Field E] {n : ℕ}
    (e : F →+* E) (f : E →+* E) (S : Finset (Fin (2*n))) (g : Derived F) :
    (tensorModel (f.comp e) S).character g = f ((tensorModel e S).character g) := by
  classical
  simp only [tensorModel_character, map_prod, map_sum, RingHom.comp_apply]

/-- Ordinary Frobenius advances by two exceptional-graph positions. -/
def rotateSupport {n : ℕ} [NeZero (2*n)] (r : ℕ) (S : Finset (Fin (2*n))) :
    Finset (Fin (2*n)) := S.image (fun j => j + (↑(2*r) : Fin (2*n)))

/-- Rotating support implements coefficient Frobenius on the character. -/
theorem tensorModel_character_rotate {E : Type*} [Field E] [CharP E 2] {n : ℕ}
    [NeZero (2*n)] (hF : Nat.card F = 2^n)
    (e : F →+* E) (r : ℕ) (S : Finset (Fin (2*n))) (g : Derived F) :
    (tensorModel e (rotateSupport r S)).character g =
      (tensorModel e S).character g ^ (2^r) := by
  classical
  let f := iterateFrobenius E 2 r
  have hf (x : E) : f x = x ^ (2^r) := rfl
  rw [← hf, tensorModel_character, tensorModel_character, map_prod]
  rw [rotateSupport, Finset.prod_image (by intros a _ b _ h; exact add_right_cancel h)]
  apply Finset.prod_congr rfl
  intro j _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hp : graphDerived F ^ ((j + (↑(2*r) : Fin (2*n)) : Fin (2*n)) : ℕ) =
      graphDerived F ^ (2*r) * graphDerived F ^ (j : ℕ) := by
    rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod,
      ← pow_eq_pow_mod _ (graphDerived_pow_field hF), Nat.add_comm, pow_add]
  rw [hp]
  change e (((graphDerived F ^ (2*r)) ((graphDerived F ^ (j : ℕ)) g)).val.val i i) = _
  rw [graphDerived_even_apply, map_pow]
  rfl

/-- The defining-field Frobenius fixes every tensor character. -/
theorem tensorModel_character_field_fixed {E : Type*} [Field E] [CharP E 2]
    {n : ℕ} (hF : Nat.card F = 2^n)
    (e : F →+* E) (S : Finset (Fin (2*n))) (g : Derived F) :
    (tensorModel e S).character g ^ (2^n) = (tensorModel e S).character g := by
  have he : (iterateFrobenius E 2 n).comp e = e := by
    ext x
    change (e x) ^ (2^n) = e x
    rw [← map_pow, ← hF]
    congr 1
    let : Fintype F := Fintype.ofFinite F
    simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card x
  have hh := tensorModel_character_comp e (iterateFrobenius E 2 n) S g
  rw [he] at hh
  exact hh.symm

/-- Catalogue uniqueness turns character invariance into support invariance. -/
theorem rotateSupport_eq_of_character_fixed {E : Type*} [Field E] [IsAlgClosed E]
    [CharP E 2] {n : ℕ} [NeZero (2*n)] (hF : Nat.card F = 2^n)
    (e : F →+* E) (cat : AbsoluteTensorCatalogue F E e n)
    (r : ℕ) (S : Finset (Fin (2*n)))
    (hfix : ∀ g, (tensorModel e S).character g ^ (2^r) = (tensorModel e S).character g) :
    rotateSupport r S = S := by
  let : IsIrreducible (tensorModel e S) := cat.irreducible S
  let : IsIrreducible (tensorModel e (rotateSupport r S)) := cat.irreducible _
  apply cat.distinguish
  apply (character_eq_iff_equiv_of_irreducible _ _).mp
  funext g
  rw [tensorModel_character_rotate hF, hfix]

/-- A support repeated in t blocks has t times the cardinality of one block. -/
theorem rotateSupport_card_multiple {n s t : ℕ} [NeZero (2*n)]
    (hn : n = s*t) (S : Finset (Fin (2*n))) (hS : rotateSupport s S = S) :
    ∃ a : ℕ, S.card = a*t := by
  classical
  let f : ℕ → ℕ := fun i => if (i : Fin (2*n)) ∈ S then 1 else 0
  have hmem (j : Fin (2*n)) : j + (2*s : ℕ) ∈ S ↔ j ∈ S := by
    conv_lhs => rw [← hS]
    simp [rotateSupport]
  have hperiod : Function.Periodic f (2*s) := by
    intro i
    dsimp only [f]
    simp only [Nat.cast_add, hmem]
  have hsum : (∑ i ∈ Finset.range (2*n), f i) = S.card := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp [f]
  have hblocks (u : ℕ) : (∑ i ∈ Finset.range ((2*s)*u), f i) =
      (∑ i ∈ Finset.range (2*s), f i) * u := by
    induction u with
    | zero => simp
    | succ u ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, Nat.mul_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Nat.cast_id, Nat.mul_comm, Nat.add_comm] using hperiod.nat_mul u i
  refine ⟨∑ i ∈ Finset.range (2*s), f i, ?_⟩
  rw [← hsum, hn, ← Nat.mul_assoc, hblocks]

end
end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary
