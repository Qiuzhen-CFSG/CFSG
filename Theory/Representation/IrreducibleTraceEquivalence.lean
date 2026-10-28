module
public import Theory.Representation.IrreducibleTraceIndependence

/-!
# Irreducible representations determined by trace

Two finite-dimensional irreducible representations of a monoid over an
algebraically closed field are equivalent exactly when their trace characters
are equal. The theorem holds in arbitrary characteristic without any group
order assumption.

If they were inequivalent, their two-element family would have linearly
independent trace characters by simultaneous simple-module density, hence
distinct characters. Conversely an actual intertwining equivalence preserves
trace. This supplies the trace-to-equivalence step in Frobenius descent for
the defining-characteristic SL2 modules used by ABG through Fong--Wong (1E).
-/

namespace Representation
universe u

/-- Equal trace characters determine an irreducible representation in any characteristic. -/
public theorem character_eq_iff_equiv_of_irreducible
    {F G : Type*} [Field F] [IsAlgClosed F] [Monoid G]
    {V W : Type u} [AddCommGroup V] [AddCommGroup W]
    [Module F V] [Module F W] [FiniteDimensional F V] [FiniteDimensional F W]
    (ρ : Representation F G V) (σ : Representation F G W)
    [IsIrreducible ρ] [IsIrreducible σ] :
    ρ.character = σ.character ↔ Nonempty (ρ.Equiv σ) := by
  classical
  refine ⟨fun h => ?_, fun ⟨e⟩ => char_iso e⟩
  by_contra hne
  let M : Bool → Type u := fun b => if b then W else V
  let addM : ∀ b, AddCommGroup (M b) := fun b => by cases b <;> dsimp [M] <;> infer_instance
  let modM : ∀ b, Module F (M b) := fun b => by cases b <;> dsimp [M] <;> infer_instance
  let rep : ∀ b, Representation F G (M b) := fun b => by
    cases b
    · exact ρ
    · exact σ
  have finM : ∀ b, FiniteDimensional F (M b) := by
    intro b
    cases b <;> dsimp [M] <;> infer_instance
  have irr : ∀ b, IsIrreducible (rep b) := by
    intro b
    cases b <;> dsimp [rep] <;> infer_instance
  have hp : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro e
    cases i <;> cases j
    · exact hij rfl
    · exact hne ⟨e⟩
    · exact hne ⟨e.symm⟩
    · exact hij rfl
  have hli := linearIndependent_characters_of_pairwise_inequivalent M rep hp
  have he : (false : Bool) = true := hli.injective h
  cases he

end Representation

