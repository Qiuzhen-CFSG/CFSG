module

public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.RestrictedSeparation
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity
public import Theory.Representation.PRegularSimpleCount
public import Theory.SpecificGroups.SL3.PRegularClasses
public import Mathlib.Data.Fintype.BigOperators

/-!
# Classification by the concrete binary SL₃ tensor words

There are 4ⁿ words of length n in the four concrete restricted factors. These
words give pairwise inequivalent irreducible representations of SL₃(F).
The number of odd-order conjugacy classes is at most |F|² = 4ⁿ, so they
exhaust the finite-dimensional irreducible representations. Otherwise an
omitted irreducible would enlarge the family beyond the modular simple-family
bound. A choice of basis brings arbitrary carrier universes into the counting
argument, and an actual representation equivalence transports the result back.

The simple family is proved by upper-fixed vectors and the orbit of the highest
vector, and separated by its character polynomials. The class bound uses actual
SL₃ conjugacy, including the determinant correction of a GL₃ conjugator.
This module combines these results into `existsUnique_word_equiv`, with no
classification or completeness premise, and re-exports simplicity and separation
of the four restricted factors. The earlier conditional counting APIs remain
available. All statements include the field of two elements.

Source: GLS III, 2.8.2, 2.8.5–6 and 2.8.10(c). The finite counting argument is
the one used for the concrete SL₂ catalogue in
Theory.Representation.SL2.SteinbergParameters.
-/

public section

set_option backward.isDefEq.respectTransparency false
open scoped MatrixGroups
namespace Representation.SL3.BinaryDefiningFactors

universe u

/-- The four-label words of length n number exactly 4ⁿ. -/
theorem card_words (n : ℕ) : Nat.card {w : List Factor // w.length = n} = 4 ^ n := by
  change Nat.card (List.Vector Factor n) = _
  rw [Nat.card_eq_fintype_card, card_vector]
  rfl

section SimpleFamily

variable {F K : Type*} [Field F] [Finite F] [Field K] [CharP K 2]

/-- Every tensor word of field length is irreducible for the actual SL₃ action.
Algebraic closure of the coefficient field is unnecessary for this assertion. -/
theorem wordRep_isIrreducible (ι : F →+* K) (n : ℕ)
    (hcard : Nat.card F = 2 ^ n) (w : List Factor) (hw : w.length = n) :
    IsIrreducible (wordRep ι w) :=
  TensorSimplicity.wordRep_isIrreducible ι n hcard w hw

/-- Equivalent tensor words of field length have the same sequence of labels. -/
theorem wordRep_equiv_imp_eq (ι : F →+* K) (n : ℕ)
    (hcard : Nat.card F = 2 ^ n) (v w : List Factor)
    (hv : v.length = n) (hw : w.length = n)
    (e : (wordRep ι v).Equiv (wordRep ι w)) : v = w :=
  TensorSimplicity.wordRep_equiv_imp_eq ι n hcard v w hv hw e

/-- The tensor words of field length give pairwise distinct isomorphism types. -/
theorem wordRep_equiv_iff (ι : F →+* K) (n : ℕ)
    (hcard : Nat.card F = 2 ^ n) (v w : List Factor)
    (hv : v.length = n) (hw : w.length = n) :
    Nonempty ((wordRep ι v).Equiv (wordRep ι w)) ↔ v = w :=
  TensorSimplicity.wordRep_equiv_iff ι n hcard v w hv hw

end SimpleFamily

variable {F : Type*} [Field F] [Finite F] {K V : Type u}
  [Field K] [IsAlgClosed K] [CharP K 2]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private theorem exists_word_equiv_sameUniverse (ι : F →+* K) (n : ℕ)
    (hcard : Nat.card F = 2 ^ n)
    (hirr : ∀ w : List Factor, w.length = n → IsIrreducible (wordRep ι w))
    (hne : ∀ v w : List Factor, v.length = n → w.length = n →
      Nonempty ((wordRep ι v).Equiv (wordRep ι w)) → v = w)
    (hclasses : Nat.card (ConjClasses.mk '' {g : SL(3,F) | ¬ 2 ∣ orderOf g}) ≤
      (Nat.card F) ^ 2)
    (ρ : Representation K SL(3,F) V) [IsIrreducible ρ] :
    ∃ w : List Factor, w.length = n ∧ Nonempty (ρ.Equiv (wordRep ι w)) := by
  classical
  by_contra! hnone
  let I := List.Vector Factor n
  let M : Option I → Type u := fun i =>
    match i with
    | none => V
    | some w => WordSpace K w.val
  let addM : ∀ i, AddCommGroup (M i) := fun i => by cases i <;> dsimp [M] <;> infer_instance
  let modM : ∀ i, Module K (M i) := fun i => by cases i <;> dsimp [M] <;> infer_instance
  let rep : ∀ i, Representation K SL(3,F) (M i) := fun i =>
    match i with
    | none => ρ
    | some w => wordRep ι w.val
  have finM : ∀ i, FiniteDimensional K (M i) := by
    intro i
    cases i <;> dsimp [M] <;> infer_instance
  have irr : ∀ i, IsIrreducible (rep i) := by
    intro i
    cases i with
    | none => exact inferInstanceAs (IsIrreducible ρ)
    | some w => exact hirr w.val w.property
  have hpair : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro φ
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some w => exact (hnone w.val w.property).false φ
    | some v =>
      cases j with
      | none => exact (hnone v.val v.property).false φ.symm
      | some w =>
        apply hij
        congr 1
        exact Subtype.ext (hne v.val w.val v.property w.property ⟨φ⟩)
  have hb := (Representation.irreducible_family_card_le_pRegularConjClasses M rep 2
    hpair).trans hclasses
  have hf : Fintype.card Factor = 4 := rfl
  have hpow : (2 ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    rfl
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, I, card_vector, hf] at hb
  rw [hcard, hpow] at hb
  omega

/-- An irreducible representation occurs among the tensor words once simplicity,
inequivalence, and the odd-order conjugacy-class bound have been established.
The original carrier may lie in an arbitrary universe. -/
theorem exists_word_equiv_of_simple_family_and_class_bound
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ι : F →+* K) (n : ℕ) (hcard : Nat.card F = 2 ^ n)
    (hirr : ∀ w : List Factor, w.length = n → IsIrreducible (wordRep ι w))
    (hne : ∀ v w : List Factor, v.length = n → w.length = n →
      Nonempty ((wordRep ι v).Equiv (wordRep ι w)) → v = w)
    (hclasses : Nat.card (ConjClasses.mk '' {g : SL(3,F) | ¬ 2 ∣ orderOf g}) ≤
      (Nat.card F) ^ 2)
    (ρ : Representation K SL(3,F) W) [IsIrreducible ρ] :
    ∃ w : List Factor, w.length = n ∧ Nonempty (ρ.Equiv (wordRep ι w)) := by
  classical
  let b := (Module.finBasis K W).equivFun
  let σ : Representation K SL(3,F) (Fin (Module.finrank K W) → K) :=
    b.conjRingEquiv.toMonoidHom.comp ρ
  let φ : ρ.Equiv σ := Representation.Equiv.mk b (by
    intro g
    ext v
    simp [σ, LinearEquiv.conjRingEquiv])
  have hirrσ : IsIrreducible σ := by
    let f := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ φ.toIntertwiningMap
    have hf : Function.Bijective f := φ.toLinearEquiv.bijective
    let ef := LinearEquiv.ofBijective f hf
    rw [irreducible_iff_isSimpleModule_asModule]
    exact ef.isSimpleModule_iff.mp ((irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance)
  obtain ⟨w, hw, ⟨ψ⟩⟩ := exists_word_equiv_sameUniverse ι n hcard hirr hne hclasses σ
  exact ⟨w, hw, ⟨φ.trans ψ⟩⟩

/-- The same conditional counting argument gives a unique word, retaining an
actual representation equivalence. The three displayed premises still need
independent proofs before this yields the SL₃ classification. -/
theorem existsUnique_word_equiv_of_simple_family_and_class_bound
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ι : F →+* K) (n : ℕ) (hcard : Nat.card F = 2 ^ n)
    (hirr : ∀ w : List Factor, w.length = n → IsIrreducible (wordRep ι w))
    (hne : ∀ v w : List Factor, v.length = n → w.length = n →
      Nonempty ((wordRep ι v).Equiv (wordRep ι w)) → v = w)
    (hclasses : Nat.card (ConjClasses.mk '' {g : SL(3,F) | ¬ 2 ∣ orderOf g}) ≤
      (Nat.card F) ^ 2)
    (ρ : Representation K SL(3,F) W) [IsIrreducible ρ] :
    ∃! w : List Factor, w.length = n ∧ Nonempty (ρ.Equiv (wordRep ι w)) := by
  obtain ⟨w, hw, ⟨φ⟩⟩ :=
    exists_word_equiv_of_simple_family_and_class_bound ι n hcard hirr hne hclasses ρ
  refine ⟨w, ⟨hw, ⟨φ⟩⟩, ?_⟩
  rintro v ⟨hv, ⟨ψ⟩⟩
  exact hne v w hv hw ⟨ψ.symm.trans φ⟩

/-- The characteristic-two SL₃ tensor-word classification: every irreducible
finite-dimensional representation over an algebraically closed coefficient
field is equivalent to exactly one word of field length. The carrier universe
is arbitrary, and the witness is an actual representation equivalence.

This is the SL₃ specialization of GLS III, 2.8.2 and 2.8.6(a), with the four
concrete factors of 2.8.10(c). Simplicity, separation and the class bound are
all discharged by proved theorems. -/
theorem existsUnique_word_equiv
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ι : F →+* K) (n : ℕ) (hcard : Nat.card F = 2 ^ n)
    (ρ : Representation K SL(3,F) W) [IsIrreducible ρ] :
    ∃! w : List Factor, w.length = n ∧ Nonempty (ρ.Equiv (wordRep ι w)) := by
  let : CharP F 2 := ι.charP ι.injective 2
  exact existsUnique_word_equiv_of_simple_family_and_class_bound ι n hcard
    (wordRep_isIrreducible ι n hcard)
    (fun v w hv hw he => (wordRep_equiv_iff ι n hcard v w hv hw).mp he)
    Theory.SpecificGroups.SL3.PRegularClasses.card_pRegularConjClasses_le ρ

/-- Every irreducible representation occurs in the concrete tensor-word
catalogue, with an actual equivalence on its original carrier. -/
theorem exists_word_equiv
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ι : F →+* K) (n : ℕ) (hcard : Nat.card F = 2 ^ n)
    (ρ : Representation K SL(3,F) W) [IsIrreducible ρ] :
    ∃ w : List Factor, w.length = n ∧ Nonempty (ρ.Equiv (wordRep ι w)) :=
  (existsUnique_word_equiv ι n hcard ρ).exists

end Representation.SL3.BinaryDefiningFactors
