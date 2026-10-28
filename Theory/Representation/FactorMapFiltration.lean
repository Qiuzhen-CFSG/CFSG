module

public import Theory.Representation.FactorDegreeFiltration

/-!
# Recognizing simple quotients from maps on a finite filtration

A finite filtration records actual invariant subspaces and their simple
quotient actions. For each factor of the same dimension as a specified target,
we additionally record a nonzero intertwiner to that target. Any irreducible
quotient of the original representation in that dimension is then equivalent
to the target: restrict a quotient map along the filtration until it first
becomes nonzero, and use simplicity and equal dimensions.

For a transitive binary permutation module with a two-group stabilizer, every
irreducible module is a quotient. Thus a finite list of concrete factor maps
suffices for recognition. This is the composition-series argument used for
Aschbacher--Smith G.9.3(10), printed pp.354,356--357. Construction of the
filtration and its factor maps is a separate, concrete obligation.
-/

@[expose] public section

universe u
namespace Representation
variable {k G W : Type*} [Field k] [Group G] [AddCommGroup W] [Module k W]

/-- A finite simple-factor filtration with nonzero maps to `σ` on precisely
those factors whose dimension equals the dimension of `σ`. The representations
in the constructors are the literal subspace and quotient actions. -/
inductive FactorMapFiltration (σ : Representation k G W) :
    {V : Type u} → [AddCommGroup V] → [Module k V] → Representation k G V → Prop
  | zero {V : Type u} [AddCommGroup V] [Module k V]
      (ρ : Representation k G V) [Subsingleton V] : FactorMapFiltration σ ρ
  | step {V : Type u} [AddCommGroup V] [Module k V]
      {ρ : Representation k G V} (S : Subrepresentation ρ)
      (previous : FactorMapFiltration σ S.toRepresentation)
      (simple : IsIrreducible S.quotientRepresentation)
      (factorMap : Module.finrank k (V ⧸ S.toSubmodule) = Module.finrank k W →
        ∃ f : S.quotientRepresentation.IntertwiningMap σ, f ≠ 0) :
      FactorMapFiltration σ ρ

variable {X V : Type*} [AddCommGroup X] [Module k X]
  [AddCommGroup V] [Module k V]
  {τ : Representation k G X} {ρ : Representation k G V} {σ : Representation k G W}

/-- An irreducible quotient of the selected degree inherits a nonzero factor
map to the specified target. -/
theorem FactorMapFiltration.exists_intertwiner (h : FactorMapFiltration σ τ)
    [IsIrreducible ρ] (hd : Module.finrank k V = Module.finrank k W)
    (f : τ.IntertwiningMap ρ) (hf : f ≠ 0) :
    ∃ q : ρ.IntertwiningMap σ, q ≠ 0 := by
  induction h with
  | zero υ =>
    exfalso
    apply hf
    ext x
    exact (congrArg f (Subsingleton.elim x 0)).trans (map_zero f)
  | @step Y _ _ υ S previous simple factorMap ih =>
    let r : S.toRepresentation.IntertwiningMap ρ := {
      toLinearMap := f.toLinearMap.comp S.toSubmodule.subtype
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        exact IntertwiningMap.isIntertwining υ ρ f g x }
    by_cases hr : r = 0
    · have hk : S.toSubmodule ≤ LinearMap.ker f.toLinearMap := by
        intro x hx
        exact congrArg (fun q : S.toRepresentation.IntertwiningMap ρ => q ⟨x, hx⟩) hr
      let q : S.quotientRepresentation.IntertwiningMap ρ := {
        toLinearMap := S.toSubmodule.liftQ f.toLinearMap hk
        isIntertwining' := by
          intro g
          apply LinearMap.ext
          intro x
          induction x using Submodule.Quotient.induction_on with
          | H x => exact IntertwiningMap.isIntertwining υ ρ f g x }
      have hq : q ≠ 0 := by
        intro hq
        apply hf
        ext x
        exact congrArg (fun z : S.quotientRepresentation.IntertwiningMap ρ =>
          z (S.toSubmodule.mkQ x)) hq
      let := simple
      let e := q.ofBijective ((IsIrreducible.bijective_or_eq_zero q).resolve_right hq)
      obtain ⟨p, hp⟩ := factorMap (e.toLinearEquiv.finrank_eq.trans hd)
      refine ⟨p.comp e.symm.toIntertwiningMap, ?_⟩
      intro hz
      apply hp
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      have hx := congrArg (fun z : ρ.IntertwiningMap σ => z (e x)) hz
      simpa using hx
    · exact ih r hr

/-- Equal dimensions turn the inherited nonzero map into an actual
intertwining linear equivalence. No irreducibility of the target is assumed. -/
theorem FactorMapFiltration.equiv_of_finrank_eq (h : FactorMapFiltration σ τ)
    [FiniteDimensional k V] [FiniteDimensional k W] [IsIrreducible ρ]
    (hd : Module.finrank k V = Module.finrank k W)
    (f : τ.IntertwiningMap ρ) (hf : f ≠ 0) : Nonempty (ρ.Equiv σ) := by
  obtain ⟨q, hq⟩ := h.exists_intertwiner hd f hf
  have hi := (IsIrreducible.injective_or_eq_zero q).resolve_right hq
  exact ⟨q.ofBijective ⟨hi,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi⟩⟩

end Representation

namespace BinaryPermutation

/-- Concrete factor maps on a permutation module with two-group stabilizer
recognize every irreducible binary representation of the target dimension. -/
theorem equiv_of_factorMapFiltration
    {G Ω V W : Type*} [Group G] [Fintype Ω]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (τ : G →* Equiv.Perm Ω) (o : Ω)
    (H : Subgroup G) (hH : IsPGroup 2 H)
    (hstab : ∀ g : G, g ∈ H ↔ τ g o = o)
    (htrans : ∀ x : Ω, ∃ g : G, τ g o = x)
    (σ : Representation (ZMod 2) G W)
    (hfiltration : Representation.FactorMapFiltration σ ((representation Ω).comp τ))
    (ρ : Representation (ZMod 2) G V) [Representation.IsIrreducible ρ]
    (hd : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) W) :
    Nonempty (ρ.Equiv σ) := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨f, hf⟩ := BinaryLinearThree.IrreducibleCatalogue.irreducible_permutation_quotient
    τ o H hH hstab htrans ρ
  apply hfiltration.equiv_of_finrank_eq hd f
  intro hz
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨x, hx⟩ := hf v
  exact hv (hx.symm.trans (congrArg (fun q => q x) hz))

end BinaryPermutation
