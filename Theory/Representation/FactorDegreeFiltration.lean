module

public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.OrbitQuotient
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Degrees of simple quotients from a finite filtration

`FactorDegreeFiltration D ρ` is an actual finite filtration by invariant
subspaces, with irreducible successive quotients whose dimensions belong to
`D`. A nonzero map to an irreducible representation either remains nonzero
on the penultimate subspace, or factors through the final simple quotient.
Induction therefore puts the target's dimension in `D`.

For a transitive binary permutation module with a two-group point stabilizer,
the fixed-vector argument supplies a surjection onto every irreducible binary
representation. Consequently one checked filtration controls all irreducible
degrees, without an assumed character table or a semisimplicity assumption.

This is the composition-series argument used here for the numerical assertion
in Aschbacher--Smith, G.7.2(3), printed p.348. Its input is the concrete
permutation module's filtration, which must be constructed separately.
-/

@[expose] public section

open Representation
universe u
namespace Representation
variable {k G : Type*} [Field k] [Group G]

/-- A finite filtration by subrepresentations with simple successive quotients
of degrees in `D`. Both the subspaces and their literal quotient actions are
part of the witness. -/
inductive FactorDegreeFiltration (D : Set ℕ) :
    {V : Type u} → [AddCommGroup V] → [Module k V] → Representation k G V → Prop
  | zero {V : Type u} [AddCommGroup V] [Module k V]
      (ρ : Representation k G V) [Subsingleton V] : FactorDegreeFiltration D ρ
  | step {V : Type u} [AddCommGroup V] [Module k V]
      {ρ : Representation k G V} (S : Subrepresentation ρ)
      (previous : FactorDegreeFiltration D S.toRepresentation)
      (simple : IsIrreducible S.quotientRepresentation)
      (degree : Module.finrank k (V ⧸ S.toSubmodule) ∈ D) : FactorDegreeFiltration D ρ

variable {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable {ρ : Representation k G V} {σ : Representation k G W}

/-- Every irreducible quotient occurs in the finite filtration. -/
theorem FactorDegreeFiltration.finrank_mem {D : Set ℕ}
    (h : FactorDegreeFiltration D ρ) [IsIrreducible σ]
    (f : ρ.IntertwiningMap σ) (hf : f ≠ 0) : Module.finrank k W ∈ D := by
  induction h with
  | zero τ =>
    exfalso
    apply hf
    ext x
    exact (congrArg f (Subsingleton.elim x 0)).trans (map_zero f)
  | @step X _ _ τ S previous simple degree ih =>
    let r : S.toRepresentation.IntertwiningMap σ := {
      toLinearMap := f.toLinearMap.comp S.toSubmodule.subtype
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        exact IntertwiningMap.isIntertwining τ σ f g x }
    by_cases hr : r = 0
    · have hk : S.toSubmodule ≤ LinearMap.ker f.toLinearMap := by
        intro x hx
        exact congrArg (fun q : S.toRepresentation.IntertwiningMap σ => q ⟨x, hx⟩) hr
      let q : S.quotientRepresentation.IntertwiningMap σ := {
        toLinearMap := S.toSubmodule.liftQ f.toLinearMap hk
        isIntertwining' := by
          intro g
          apply LinearMap.ext
          intro x
          induction x using Submodule.Quotient.induction_on with
          | H x => exact IntertwiningMap.isIntertwining τ σ f g x }
      have hq : q ≠ 0 := by
        intro hq
        apply hf
        ext x
        exact congrArg (fun z : S.quotientRepresentation.IntertwiningMap σ =>
          z (S.toSubmodule.mkQ x)) hq
      let := simple
      have he := (q.ofBijective ((IsIrreducible.bijective_or_eq_zero q).resolve_right hq)).toLinearEquiv
      rw [← he.finrank_eq]
      exact degree
    · exact ih r hr

end Representation

namespace BinaryPermutation

/-- A filtration of a transitive permutation module with a two-group point
stabilizer controls the degree of every irreducible binary representation. -/
theorem finrank_mem_of_factorDegreeFiltration
    {G Ω V : Type*} [Group G] [Fintype Ω]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {D : Set ℕ} (τ : G →* Equiv.Perm Ω) (o : Ω)
    (H : Subgroup G) (hH : IsPGroup 2 H)
    (hstab : ∀ g : G, g ∈ H ↔ τ g o = o)
    (htrans : ∀ x : Ω, ∃ g : G, τ g o = x)
    (hfiltration : Representation.FactorDegreeFiltration D ((representation Ω).comp τ))
    (ρ : Representation (ZMod 2) G V) [Representation.IsIrreducible ρ] :
    Module.finrank (ZMod 2) V ∈ D := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨f, hf⟩ := BinaryLinearThree.IrreducibleCatalogue.irreducible_permutation_quotient
    τ o H hH hstab htrans ρ
  apply hfiltration.finrank_mem f
  intro hz
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨x, hx⟩ := hf v
  exact hv (hx.symm.trans (congrArg (fun q => q x) hz))

end BinaryPermutation
