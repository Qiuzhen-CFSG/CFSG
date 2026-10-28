module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.Saturation

/-!
# Recognizing a modular simple representation by its degree

Suppose a distinguished simple model and a complementary family of pairwise
inequivalent simple models reach the number of p-regular conjugacy classes.
If none of the complementary models has the distinguished model's degree,
every simple representation of that degree is equivalent to the distinguished
model. This is an actual representation equivalence, not just equality of
characters or dimensions.

Adjoin the distinguished model to the family, apply modular trace-independence
saturation, and exclude the complementary entries by dimension. The HS
application uses the concrete degree-twenty model and eight complementary
models over a common algebraic closure. The finite-model constructions and
conjugacy-class coverage remain separate mathematical inputs.

Source: the standard modular simple-count argument, proved in
`PRegularSimpleCount` and `PSL3Three.AbsoluteDegrees.Saturation`; application
to Guralnick--Malle, *Classification of 2F-modules I*, Proposition 5.1.
-/

public section
namespace Representation
universe u v w

/-- A saturating family whose other members have different degrees recognizes
an arbitrary simple action of the distinguished model's degree. -/
theorem nonempty_equiv_of_complementary_models
    {F U W : Type v} {G : Type u} {ι : Type w}
    [Field F] [IsAlgClosed F] [Group G] [Finite G] [Fintype ι]
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (σ : Representation F G U) [hσ : σ.IsIrreducible]
    (V : ι → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]
    [∀ i, FiniteDimensional F (V i)] (ρ : ∀ i, Representation F G (V i))
    [hirr : ∀ i, (ρ i).IsIrreducible]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (hne : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))
    (hdifferent : ∀ i, Module.finrank F (V i) ≠ Module.finrank F U)
    (hclasses : Nat.card (ConjClasses.mk '' {g : G | ¬ p ∣ orderOf g}) ≤
      Nat.card ι + 1)
    (τ : Representation F G W) [hτ : τ.IsIrreducible]
    (hd : Module.finrank F W = Module.finrank F U) : Nonempty (τ.Equiv σ) := by
  classical
  let M : Option ι → Type v := fun i => match i with
    | none => U
    | some j => V j
  let addM : ∀ i, AddCommGroup (M i) := fun i => by
    cases i <;> dsimp [M] <;> infer_instance
  let modM : ∀ i, Module F (M i) := fun i => by
    cases i <;> dsimp [M] <;> infer_instance
  let rep : ∀ i, Representation F G (M i) := fun i => match i with
    | none => σ
    | some j => ρ j
  have finM : ∀ i, FiniteDimensional F (M i) := by
    intro i
    cases i <;> dsimp [M] <;> infer_instance
  have irr : ∀ i, (rep i).IsIrreducible := by
    intro i
    cases i <;> dsimp [rep] <;> infer_instance
  have hne' : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    refine ⟨fun e => ?_⟩
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some j => exact hdifferent j e.toLinearEquiv.finrank_eq.symm
    | some i =>
      cases j with
      | none => exact hdifferent i e.toLinearEquiv.finrank_eq
      | some j => exact (hne (fun h => hij (congrArg some h))).false e
  have hc : Nat.card (Option ι) = Nat.card ι + 1 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_option]
  obtain ⟨i, ⟨e⟩⟩ := exists_equiv_of_pRegular_class_bound M rep p hne'
    (hc.symm ▸ hclasses) τ
  cases i with
  | none => exact ⟨e⟩
  | some i => exact (hdifferent i (e.toLinearEquiv.finrank_eq.symm.trans hd)).elim

end Representation
