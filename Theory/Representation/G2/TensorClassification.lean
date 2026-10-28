module

public import Theory.Representation.G2.TensorClassification.Construction
public import Theory.Representation.G2.TensorClassification.SimpleDistinct
public import Theory.Representation.G2.TensorClassification.Rotation
public import Theory.Representation.G2.TensorClassification.SpecialWords
public import Theory.SpecificGroups.G2.PRegularClasses
public import Theory.Representation.PRegularSimpleCount
public import Mathlib.Algebra.Module.ULift

/-!
# Exhaustive classification of the concrete G₂ Frobenius tensors

There are `q² = 4^n` words in the four concrete restricted factors. Their
irreducibility and pairwise inequivalence, together with the upper bound of
`q²` on actual odd-order conjugacy classes, exhaust all finite-dimensional
irreducibles by the modular simple-family bound. A basis and universe lift
give genuine intertwining equivalences for carriers in arbitrary universes.

The conditional counting interfaces are retained; the final classification
theorems discharge all three premises using the concrete G₂ results. The
re-exported rotation and special-word interfaces prove the exact Frobenius
period criterion, characterize trivial action, and retain the genuine
single-natural-factor equivalence to the octonion quotient action. The
construction supplies the product dimension formula.

Sources: GLS3, 2.8.2, 2.8.5--8 and 2.8.10(g); Aschbacher--Smith, G.9.3(10),
printed pp.354, 356--357. The counting argument follows the checked SL₂ route
in `Theory.Representation.SL2.SteinbergParameters`.
-/

public noncomputable section

namespace Atlas.G2.TensorClassification
open Restricted

universe u v

section Exhaustion
variable {F : Type u} [Field F] [CharP F 2] [Finite F]
  {K : Type v} [Field K] [Algebra F K] [IsAlgClosed K] [CharP K 2]
  {n : ℕ}

private theorem exists_tensorRep_equiv_sameUniverse
    (hirr : ∀ w : Fin n → Factor, Representation.IsIrreducible (tensorRep F K w))
    (hdist : ∀ a b : Fin n → Factor,
      Nonempty ((tensorRep F K a).Equiv (tensorRep F K b)) → a = b)
    (hbound : Nat.card (ConjClasses.mk '' {g : Model F | ¬ 2 ∣ orderOf g}) ≤
      Nat.card (Fin n → Factor))
    {V : Type (max u v)} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (Model F) V) (hρ : Representation.IsIrreducible ρ) :
    ∃ w : Fin n → Factor, Nonempty (ρ.Equiv (tensorRep F K w)) := by
  classical
  by_contra! hnone
  let M : Option (Fin n → Factor) → Type (max u v) := fun i =>
    match i with
    | none => V
    | some w => TensorSpace F K w
  let addM : ∀ i, AddCommGroup (M i) := fun i => by cases i <;> dsimp [M] <;> infer_instance
  let modM : ∀ i, Module K (M i) := fun i => by cases i <;> dsimp [M] <;> infer_instance
  let rep : ∀ i, Representation K (Model F) (M i) := fun i =>
    match i with
    | none => ρ
    | some w => tensorRep F K w
  have finM : ∀ i, FiniteDimensional K (M i) := by
    intro i
    cases i <;> dsimp [M] <;> infer_instance
  have irr : ∀ i, Representation.IsIrreducible (rep i) := by
    intro i
    cases i with
    | none => exact hρ
    | some w => exact hirr w
  have hne : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro φ
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some w => exact (hnone w).false φ
    | some w =>
      cases j with
      | none => exact (hnone w).false φ.symm
      | some w' => exact hij (congrArg some (hdist w w' ⟨φ⟩))
  have hc := Representation.irreducible_family_card_le_pRegularConjClasses M rep 2 hne
  have hh := hc.trans hbound
  simp only [Nat.card_eq_fintype_card, Fintype.card_option] at hh
  omega

/-- Exhaustion from simplicity and distinctness of the concrete tensors and
an upper bound on the actual odd-order conjugacy classes. These three inputs
remain separate mathematical obligations. -/
theorem exists_tensorRep_equiv_of_simple_distinct_class_bound
    (hF : Nat.card F = 2 ^ n)
    (hirr : ∀ w : Fin n → Factor, Representation.IsIrreducible (tensorRep F K w))
    (hdist : ∀ a b : Fin n → Factor,
      Nonempty ((tensorRep F K a).Equiv (tensorRep F K b)) → a = b)
    (hbound : Nat.card (ConjClasses.mk '' {g : Model F | ¬ 2 ∣ orderOf g}) ≤
      Nat.card F ^ 2)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (Model F) V) (hρ : Representation.IsIrreducible ρ) :
    ∃ w : Fin n → Factor, Nonempty (ρ.Equiv (tensorRep F K w)) := by
  classical
  let b : V ≃ₗ[K] ULift.{u} (Fin (Module.finrank K V) → K) :=
    (Module.finBasis K V).equivFun.trans ULift.moduleEquiv.symm
  let σ : Representation K (Model F) (ULift.{u} (Fin (Module.finrank K V) → K)) :=
    b.conjRingEquiv.toMonoidHom.comp ρ
  let φ : ρ.Equiv σ := .mk b (by
    intro g
    ext x
    simp [σ, LinearEquiv.conjRingEquiv])
  have hσ : Representation.IsIrreducible σ :=
    (Representation.RepEquiv.irreducible_euqiv
      (Representation.RepEquiv.ofRepresentationEquiv φ)).mp hρ
  obtain ⟨w, ⟨ψ⟩⟩ := exists_tensorRep_equiv_sameUniverse hirr hdist
    (by simpa only [tensor_parameter_card F n hF] using hbound) σ hσ
  exact ⟨w, ⟨φ.trans ψ⟩⟩

/-- The counting assembly also supplies the unique actual word. -/
theorem existsUnique_tensorRep_equiv_of_simple_distinct_class_bound
    (hF : Nat.card F = 2 ^ n)
    (hirr : ∀ w : Fin n → Factor, Representation.IsIrreducible (tensorRep F K w))
    (hdist : ∀ a b : Fin n → Factor,
      Nonempty ((tensorRep F K a).Equiv (tensorRep F K b)) → a = b)
    (hbound : Nat.card (ConjClasses.mk '' {g : Model F | ¬ 2 ∣ orderOf g}) ≤
      Nat.card F ^ 2)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (Model F) V) (hρ : Representation.IsIrreducible ρ) :
    ∃! w : Fin n → Factor, Nonempty (ρ.Equiv (tensorRep F K w)) := by
  obtain ⟨w, ⟨e⟩⟩ :=
    exists_tensorRep_equiv_of_simple_distinct_class_bound hF hirr hdist hbound ρ hρ
  refine ⟨w, ⟨e⟩, ?_⟩
  rintro w' ⟨e'⟩
  exact hdist w' w ⟨e'.symm.trans e⟩

/-- Every finite-dimensional irreducible representation of the actual finite G₂
model over an algebraically closed characteristic-two field is a concrete
Frobenius tensor. No degree restriction or catalogue premise is required. -/
theorem exists_tensorRep_equiv
    (hF : Nat.card F = 2 ^ n)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (Model F) V) (hρ : Representation.IsIrreducible ρ) :
    ∃ w : Fin n → Factor, Nonempty (ρ.Equiv (tensorRep F K w)) :=
  exists_tensorRep_equiv_of_simple_distinct_class_bound hF
    (tensorRep_irreducible hF) (fun _ _ => tensorRep_equiv_imp_eq hF)
    PRegularClasses.card_pRegularConjClasses_le ρ hρ

/-- The complete, unique tensor word of an arbitrary finite-dimensional
irreducible representation, with an actual intertwining equivalence. -/
theorem existsUnique_tensorRep_equiv
    (hF : Nat.card F = 2 ^ n)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (Model F) V) (hρ : Representation.IsIrreducible ρ) :
    ∃! w : Fin n → Factor, Nonempty (ρ.Equiv (tensorRep F K w)) :=
  existsUnique_tensorRep_equiv_of_simple_distinct_class_bound hF
    (tensorRep_irreducible hF) (fun _ _ => tensorRep_equiv_imp_eq hF)
    PRegularClasses.card_pRegularConjClasses_le ρ hρ

end Exhaustion

end Atlas.G2.TensorClassification

end
