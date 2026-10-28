module

public import Theory.Representation.PRegularSimpleCount

/-!
# Exhaustion of a modular simple family by conjugacy-class counting

A family of pairwise inequivalent simple representations is exhaustive once
its size reaches the number of p-regular conjugacy classes. Adjoining a missing
simple would contradict the proved modular trace-independence bound. This uses
neither Maschke's theorem nor an assumed character-table completeness result.

The PSL₃(3) application uses seven candidates in characteristic two. The
candidate constructions and the group-specific class bound are separate inputs.
This is the standard modular simple-count argument underlying the small-degree
calculation cited in GM02, Proposition 4.2, manuscript pp.9--10.
-/

namespace Representation
universe u v w

/-- A family reaching the p-regular class bound contains every simple module.
The group, index set and coefficient field may occupy arbitrary universes. -/
public theorem exists_equiv_of_pRegular_class_bound
    {F W : Type v} {G : Type u} {ι : Type w}
    [Field F] [IsAlgClosed F] [Group G] [Finite G] [Fintype ι]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (V : ι → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]
    [∀ i, FiniteDimensional F (V i)] (ρ : ∀ i, Representation F G (V i))
    [∀ i, IsIrreducible (ρ i)]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (hne : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))
    (hclasses : Nat.card (ConjClasses.mk '' {g : G | ¬ p ∣ orderOf g}) ≤ Nat.card ι)
    (σ : Representation F G W) [IsIrreducible σ] :
    ∃ i, Nonempty (σ.Equiv (ρ i)) := by
  classical
  by_contra! hnone
  let M : Option ι → Type v := fun i =>
    match i with
    | none => W
    | some j => V j
  let addM : ∀ i, AddCommGroup (M i) := fun i => by
    cases i <;> dsimp [M] <;> infer_instance
  let modM : ∀ i, Module F (M i) := fun i => by
    cases i <;> dsimp [M] <;> infer_instance
  let rep : ∀ i, Representation F G (M i) := fun i =>
    match i with
    | none => σ
    | some j => ρ j
  have finM : ∀ i, FiniteDimensional F (M i) := by
    intro i
    cases i <;> dsimp [M] <;> infer_instance
  have irr : ∀ i, IsIrreducible (rep i) := by
    intro i
    cases i <;> dsimp [rep] <;> infer_instance
  have hne' : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro e
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some j => exact (hnone j).false e
    | some i =>
      cases j with
      | none => exact (hnone i).false e.symm
      | some j => exact (hne (fun h => hij (congrArg some h))).false e
  have hbound := irreducible_family_card_le_pRegularConjClasses M rep p hne'
  have hcard : Nat.card (Option ι) = Nat.card ι + 1 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_option]
  omega

end Representation
