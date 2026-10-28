module

public import Theory.Representation.SL2.BinarySmallModels

/-!
# Compatible Schur and Hermitian coefficient fields

Two finite fields of equal size embedded in a common field have the same
image: the polynomial `X^q-X` splits over each of them. Lifting the specified
embedding therefore gives a compatible ring equivalence, not just an abstract
cardinality comparison. Apply this to the actual Frobenius fixed half-field.

The final theorem also absorbs a chosen Frobenius shift into the group-field
identification. Together these comparisons provide the coefficient data for
scalar descent of the repeated-pair tensor in GLS volume 3, §2.8.8 and
§2.8.10(b), used in Aschbacher--Smith G.9.3(7), printed pp.354,356–357.
No lower bound beyond positive half-degree is needed, so this includes `s=1`.
-/

@[expose] public section

open scoped MatrixGroups MonoidAlgebra TensorProduct
open Representation.OrthogonalFourMinus.FiniteModel
namespace Representation.SL2.BinaryHermitian
noncomputable section

private theorem mem_range_of_pow_card {E L : Type*} [Field E] [Finite E]
    [Field L] (ι : E →+* L) {x : L} (hx : x ^ Nat.card E = x) :
    x ∈ ι.range := by
  let : Fintype E := Fintype.ofFinite E
  let p : Polynomial E := Polynomial.X ^ Fintype.card E - Polynomial.X
  have hp : p.Splits := Polynomial.splits_iff_card_roots.mpr (by
    rw [FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq E Fintype.one_lt_card]
    rfl)
  apply hp.mem_range_of_isRoot (FiniteField.X_pow_card_sub_X_ne_zero E Fintype.one_lt_card)
  simpa [p, Polynomial.IsRoot, Nat.card_eq_fintype_card, sub_eq_zero] using hx

/-- Finite coefficient fields of the same size have the same embedded image.
The resulting isomorphism respects the specified embeddings, not just cardinality. -/
theorem exists_compatible_fieldEquiv {E k L : Type*} [Field E] [Finite E]
    [Field k] [Finite k] [Field L] (ι : E →+* L) (β : k →+* L)
    (hcard : Nat.card k = Nat.card E) :
    ∃ θ : k ≃+* E, ∀ a, ι (θ a) = β a := by
  classical
  have hlift (a : k) : ∃ b : E, ι b = β a := by
    apply mem_range_of_pow_card ι
    rw [← hcard, ← map_pow]
    congr 1
    let : Fintype k := Fintype.ofFinite k
    simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card a
  let f : k →+* E :=
    { toFun := fun a => (hlift a).choose
      map_one' := ι.injective (by rw [(hlift 1).choose_spec, map_one, map_one])
      map_mul' a b := ι.injective (by
        rw [(hlift (a*b)).choose_spec, ι.map_mul, (hlift a).choose_spec,
          (hlift b).choose_spec, β.map_mul])
      map_zero' := ι.injective (by rw [(hlift 0).choose_spec, map_zero, map_zero])
      map_add' a b := ι.injective (by
        rw [(hlift (a+b)).choose_spec, ι.map_add, (hlift a).choose_spec,
          (hlift b).choose_spec, β.map_add]) }
  refine ⟨RingEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨f.injective, hcard⟩), ?_⟩
  exact fun a => (hlift a).choose_spec

/-- The actual Frobenius fixed half-field identifies with any coefficient
field of order `2^s`, compatibly with the given embeddings. -/
theorem exists_halfFieldEquiv {E L : Type*} [Field E] [Finite E] [Field L]
    (s : ℕ) [NeZero s] (ι : E →+* L) (β : Field s →+* L)
    (hcard : Nat.card E = 2 ^ s) :
    ∃ θ : fixedField s ≃+* E, ∀ a, ι (θ a) = β a.val := by
  apply exists_compatible_fieldEquiv ι (β.comp (fixedField s).subtype)
  rw [card_fixedField, hcard]

/-- Choose the group field identification so that the requested Frobenius
shift is absorbed in it, while the half-field embedding is the prescribed
coefficient embedding. -/
theorem exists_modelFields {K E L : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [Field L] (s j : ℕ) [NeZero s]
    (ι : E →+* L) (e : K →+* L)
    (hK : Nat.card K = 2 ^ (2*s)) (hE : Nat.card E = 2 ^ s) :
    ∃ (f : K ≃+* Field s) (β : Field s →+* L) (θ : E ≃+* fixedField s),
      (∀ a, β (θ a).val = ι a) ∧ ∀ x, β (f x) = e x ^ (2 ^ j) := by
  obtain ⟨f₀⟩ := BinarySmall.nonempty_hermitianFieldEquiv s hK
  let β : Field s →+* L := e.comp f₀.symm.toRingHom
  obtain ⟨θ, hθ⟩ := exists_halfFieldEquiv s ι β hE
  refine ⟨f₀.trans (iterateFrobeniusEquiv (Field s) 2 j), β, θ.symm, ?_, ?_⟩
  · intro a
    simpa only [RingEquiv.apply_symm_apply] using (hθ (θ.symm a)).symm
  · intro x
    change β (iterateFrobeniusEquiv (Field s) 2 j (f₀ x)) = _
    rw [iterateFrobeniusEquiv_def, map_pow]
    simp [β]

end
end Representation.SL2.BinaryHermitian
