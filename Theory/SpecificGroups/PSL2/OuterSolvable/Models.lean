module

public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Field transport and the small binary PSL₂ parameter

Entrywise application of a field isomorphism carries centers onto centers,
and therefore gives an isomorphism of the actual PSL₂ quotients. Over a
field with two elements, SL₂ acts faithfully on its four vectors and embeds
in the solvable symmetric group S₄. Thus a nonsolvable PSL₂ in
characteristic two has a model over GF(2ⁿ) with `n ≥ 2`.

These elementary model changes let the A₁ automorphism calculation in GLS3,
Theorem 2.5.12 and §2.7, apply to arbitrary finite fields rather than only
one chosen carrier. No simplicity or order theorem for PSL₂ is required.
-/

namespace Theory.PSL2.OuterSolvable
open Matrix
variable {K L : Type*} [Field K] [Field L]

@[expose] public def slRingEquiv (e : K ≃+* L) :
    SpecialLinearGroup (Fin 2) K ≃* SpecialLinearGroup (Fin 2) L where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by ext i j; exact e.symm_apply_apply (A i j)
  right_inv A := by ext i j; exact e.apply_symm_apply (A i j)
  map_mul' := (SpecialLinearGroup.map e.toRingHom).map_mul

@[expose] public def projectiveRingEquiv (e : K ≃+* L) : Group K ≃* Group L := by
  let f := slRingEquiv e
  apply QuotientGroup.congr _ _ f
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (Subgroup.centerCongr f ⟨a, ha⟩).property
  · intro hb
    exact ⟨f.symm b, (Subgroup.centerCongr f.symm ⟨b, hb⟩).property,
      f.apply_symm_apply b⟩

public theorem isSolvable_of_card_two [Finite K] (hK : Nat.card K = 2) :
    _root_.Group.IsSolvable (Group K) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let : FaithfulSMul (SpecialLinearGroup (Fin 2) K) (Fin 2 → K) := ⟨by
    intro a b h
    apply Subtype.ext
    exact Matrix.ext_iff_mulVec.mpr h⟩
  let e : (Fin 2 → K) ≃ Fin 4 := Fintype.equivFinOfCardEq (by
    rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hK]
    rfl)
  let f : SpecialLinearGroup (Fin 2) K →* Equiv.Perm (Fin 4) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom _ _)
  let : _root_.Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : _root_.Group.IsSolvable (SpecialLinearGroup (Fin 2) K) :=
    _root_.Group.isSolvable_of_isSolvable_injective
      (f := f) (e.permCongrHom.injective.comp MulAction.toPerm_injective)
  infer_instance

public theorem binary_model_of_not_isSolvable [Finite K] [CharP K 2]
    (hns : ¬ _root_.Group.IsSolvable (Group K)) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (Group K ≃* BinaryGroup n) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨n, _, hn⟩ := FiniteField.card K 2
  have hn2 : 2 ≤ (n : ℕ) := by
    by_contra h
    have hn1 : (n : ℕ) = 1 := by have := n.pos; omega
    apply hns
    apply isSolvable_of_card_two
    simpa [Nat.card_eq_fintype_card, hn1] using hn
  let : Fintype (BinaryField n) := Fintype.ofFinite _
  let e : K ≃+* BinaryField n := FiniteField.ringEquivOfCardEq (by
    rw [hn, ← Nat.card_eq_fintype_card, GaloisField.card 2 n (by have := n.pos; omega)])
  exact ⟨n, hn2, ⟨projectiveRingEquiv e⟩⟩
end Theory.PSL2.OuterSolvable
