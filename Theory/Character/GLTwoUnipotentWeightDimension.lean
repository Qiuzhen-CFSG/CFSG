module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Dimensions from nontrivial upper-unipotent weights in GL₂

For a complex representation of GL₂ over a finite field, absence of nonzero
upper-unipotent fixed vectors forces the ambient dimension to be `q - 1` times
the dimension of each nontrivial additive-character weight. The weight is the
intersection of eigenspaces for the actual `upperRightHom` matrices. Neither
irreducibility nor positivity of the ambient dimension is assumed; the result
also applies over the field with two elements.

Conjugation by `diag(a, 1)` shows that all nonidentity upper unipotents have a
common character value `c`. Twist the restricted representation by `psi(-a)`;
its invariant subspace is exactly the requested weight. Mathlib's character
averaging formula applied first to the trivial twist and then to a nontrivial
twist gives `size + (q - 1)c = 0` and `q * dim(weight) = size - c`.
The nontrivial additive-character sum vanishes, and eliminating `c` proves the
dimension identity.

This supplies the dimension step in the ordinary GL₂ cuspidal-degree argument
underlying the degree list cited by Brauer, *Desarguesian planes II*, printed
p. 128. The averaging proof here is independent of that asserted degree list
and does not assume Whittaker multiplicity one.
-/

open scoped MatrixGroups

private theorem unipotent_character_constant
    {F : Type*} [Field F] (size : ℕ)
    (rho : Representation ℂ (GL (Fin 2) F) (Fin size → ℂ))
    (parameter : F) (hne : parameter ≠ 0) :
    rho.character (Matrix.GeneralLinearGroup.upperRightHom parameter) =
      rho.character (Matrix.GeneralLinearGroup.upperRightHom 1) := by
  let diagonal : GL (Fin 2) F :=
    ⟨!![parameter, 0; 0, 1], !![parameter⁻¹, 0; 0, 1],
      by simp [Matrix.one_fin_two, hne], by simp [Matrix.one_fin_two, hne]⟩
  have hconj : diagonal * Matrix.GeneralLinearGroup.upperRightHom 1 * diagonal⁻¹ =
      Matrix.GeneralLinearGroup.upperRightHom parameter := by
    apply Units.ext
    simp [diagonal, Matrix.GeneralLinearGroup.upperRightHom, hne]
  rw [← hconj]
  exact rho.char_conj _ _

private noncomputable def weightTwist
    {F : Type*} [Field F] (size : ℕ)
    (rho : Representation ℂ (GL (Fin 2) F) (Fin size → ℂ))
    (psi : AddChar F ℂ) : Representation ℂ (Multiplicative F) (Fin size → ℂ) where
  toFun parameter := psi (-parameter.toAdd) •
    rho (Matrix.GeneralLinearGroup.upperRightHom parameter.toAdd)
  map_one' := by simp
  map_mul' first second := by
    change psi (-(first.toAdd + second.toAdd)) •
      rho (Matrix.GeneralLinearGroup.upperRightHom (first.toAdd + second.toAdd)) = _
    rw [neg_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, map_mul]
    simp only [smul_mul_smul_comm]

private theorem weightTwist_invariants
    {F : Type*} [Field F] (size : ℕ)
    (rho : Representation ℂ (GL (Fin 2) F) (Fin size → ℂ))
    (psi : AddChar F ℂ) :
    (weightTwist size rho psi).invariants =
      ⨅ parameter : F, Module.End.eigenspace
        (rho (Matrix.GeneralLinearGroup.upperRightHom parameter)) (psi parameter) := by
  ext vector
  simp only [Representation.mem_invariants, Submodule.mem_iInf,
    Module.End.mem_eigenspace_iff]
  constructor
  · intro hfixed parameter
    have heq := congrArg (fun vector => psi parameter • vector)
      (hfixed (Multiplicative.ofAdd parameter))
    simpa [weightTwist, smul_smul, ← AddChar.map_add_eq_mul] using heq
  · intro hweight parameter
    change psi (-parameter.toAdd) •
      rho (Matrix.GeneralLinearGroup.upperRightHom parameter.toAdd) vector = vector
    rw [hweight, smul_smul, ← AddChar.map_add_eq_mul]
    simp

private theorem weight_average
    {F : Type*} [Field F] [Fintype F] (size : ℕ)
    (rho : Representation ℂ (GL (Fin 2) F) (Fin size → ℂ))
    (psi : AddChar F ℂ) :
    (Nat.card F : ℂ)⁻¹ * ∑ parameter : F,
      psi (-parameter) * rho.character (Matrix.GeneralLinearGroup.upperRightHom parameter) =
    Module.finrank ℂ (⨅ parameter : F, Module.End.eigenspace
      (rho (Matrix.GeneralLinearGroup.upperRightHom parameter)) (psi parameter) :
      Submodule ℂ (Fin size → ℂ)) := by
  have hcard : (Nat.card (Multiplicative F) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  let := invertibleOfNonzero hcard
  have havg := (weightTwist size rho psi).card_inv_mul_sum_char_eq_finrank
  rw [weightTwist_invariants] at havg
  have hchar (parameter : Multiplicative F) :
      (weightTwist size rho psi).character parameter = psi (-parameter.toAdd) *
        rho.character (Matrix.GeneralLinearGroup.upperRightHom parameter.toAdd) := by
    simp [Representation.character, weightTwist]
  simp only [hchar] at havg
  have hsum := (Multiplicative.toAdd : Multiplicative F ≃ F).sum_comp
    (fun parameter : F => psi (-parameter) *
      rho.character (Matrix.GeneralLinearGroup.upperRightHom parameter))
  rw [hsum] at havg
  simpa only [Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)] using havg

public theorem gl2_dimension_eq_nontrivial_unipotent_weight_mul
    {F : Type*} [Field F] [Finite F] (size : ℕ)
    (rho : Representation ℂ (GL (Fin 2) F) (Fin size → ℂ))
    (hnofixed : ¬ ∃ vector, vector ≠ 0 ∧ ∀ parameter : F,
      rho (Matrix.GeneralLinearGroup.upperRightHom parameter) vector = vector)
    (psi : AddChar F ℂ) (hpsi : psi ≠ 1) :
    size = (Nat.card F - 1) * Module.finrank ℂ
      (⨅ parameter : F, Module.End.eigenspace
        (rho (Matrix.GeneralLinearGroup.upperRightHom parameter)) (psi parameter) :
        Submodule ℂ (Fin size → ℂ)) := by
  classical
  let := Fintype.ofFinite F
  let common := rho.character (Matrix.GeneralLinearGroup.upperRightHom (1 : F))
  have hchar (parameter : F) :
      rho.character (Matrix.GeneralLinearGroup.upperRightHom parameter) =
        common + if parameter = 0 then (size : ℂ) - common else 0 := by
    by_cases hzero : parameter = 0
    · subst parameter
      simp
    · simpa only [if_neg hzero, add_zero] using
        unipotent_character_constant size rho parameter hzero
  have htrivial : (⨅ parameter : F, Module.End.eigenspace
      (rho (Matrix.GeneralLinearGroup.upperRightHom parameter))
        ((1 : AddChar F ℂ) parameter)) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro vector hvector
    change vector = 0
    have hfixed : ∀ parameter : F,
        rho (Matrix.GeneralLinearGroup.upperRightHom parameter) vector = vector := by
      simpa only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff,
        AddChar.one_apply, one_smul] using hvector
    by_contra hne
    exact hnofixed ⟨vector, hne, hfixed⟩
  have hzero := weight_average size rho (1 : AddChar F ℂ)
  rw [htrivial] at hzero
  simp only [hchar, AddChar.one_apply, one_mul, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true,
    finrank_bot, Nat.cast_zero, Fintype.card_eq_nat_card] at hzero
  have hsum : ∑ parameter : F, psi (-parameter) = 0 := by
    calc
      _ = ∑ parameter : F, psi parameter := by
        simpa using Equiv.sum_comp (Equiv.neg F) (fun parameter => psi parameter)
      _ = 0 := AddChar.sum_eq_zero_of_ne_one hpsi
  have hweight := weight_average size rho psi
  simp only [hchar, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    hsum, zero_mul, zero_add, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, neg_zero, AddChar.map_zero_eq_one, one_mul] at hweight
  have hcard : (Nat.card F : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hcardpos : 1 ≤ Nat.card F := Nat.card_pos
  have hzero' : (Nat.card F : ℂ) * common + (size : ℂ) - common = 0 := by
    have := (mul_eq_zero.mp hzero).resolve_left (inv_ne_zero hcard)
    linear_combination this
  have hweight' : (size : ℂ) - common = (Nat.card F : ℂ) *
      Module.finrank ℂ (⨅ parameter : F, Module.End.eigenspace
        (rho (Matrix.GeneralLinearGroup.upperRightHom parameter)) (psi parameter) :
        Submodule ℂ (Fin size → ℂ)) := by
    calc
      _ = (Nat.card F : ℂ) * ((Nat.card F : ℂ)⁻¹ * ((size : ℂ) - common)) := by
        field_simp
      _ = _ := congrArg ((Nat.card F : ℂ) * ·) hweight
  apply Nat.cast_injective (R := ℂ)
  push_cast [Nat.cast_sub hcardpos]
  apply (mul_left_cancel₀ hcard)
  linear_combination hzero' + ((Nat.card F : ℂ) - 1) * hweight'
