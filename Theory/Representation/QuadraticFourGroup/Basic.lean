module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.ElementaryAbelian.Basic
public import Theory.Representation.SubspaceQuotient
public import Mathlib.RepresentationTheory.Intertwining

/-!
# The source hypotheses for quadratic four-groups

GLS, volume 2, Theorem 25.14 assumes a faithful binary representation, a
component moved by an involution in a four-group, the identity `[V,a,B] = 0`,
and `C_B(L) = 1`. `Hypotheses` records exactly these inputs; finiteness of the
group and dimension are separate typeclass assumptions in applications.

The displacement identity survives invariant subspaces, quotients and
equivariant surjections. These elementary reductions are proved here, along
with consequences of genuine component calculus. They do not assert the
classification theorem. In particular they do not assume either the
identification of the orbit quotient or its tensor-module structure.

The final theorem must use `componentOrbit L B / O₂(componentOrbit L B)` and
all irreducible subquotients of the restricted representation. Its nontrivial
factors are tensors over `F_(2^n)`, restricted to `F₂`, with `n > 1`;
the field in the printed Step 5 heading is a typo (see the statement's remarks).
-/

@[expose] public section

namespace Representation.QuadraticFourGroup

open Subgroup Theory.GroupTheory

section Linear

variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k G W}

/-- The pointwise meaning of `[V,a,B] = 0`; only displacements by `a`
are required to be fixed by `B`. -/
def FixesDisplacements (ρ : Representation k G V) (a : G) (B : Subgroup G) : Prop :=
  ∀ b ∈ B, ∀ v : V, ρ b (ρ a v - v) = ρ a v - v

/-- The displacement identity descends along an equivariant surjection. -/
theorem FixesDisplacements.of_surjective {a : G} {B : Subgroup G}
    (h : FixesDisplacements ρ a B) (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) : FixesDisplacements σ a B := by
  intro b hb w
  obtain ⟨v, rfl⟩ := hf w
  simpa only [map_sub, f.isIntertwining] using congrArg f (h b hb v)

/-- An invariant subspace inherits the displacement identity. -/
theorem FixesDisplacements.subrepresentation {a : G} {B : Subgroup G}
    (h : FixesDisplacements ρ a B) (U : Subrepresentation ρ) :
    FixesDisplacements U.toRepresentation a B := by
  intro b hb v
  apply Subtype.ext
  exact h b hb v

/-- The actual quotient action inherits the displacement identity. -/
theorem FixesDisplacements.quotient {a : G} {B : Subgroup G}
    (h : FixesDisplacements ρ a B) (U : Subrepresentation ρ) :
    FixesDisplacements U.quotientRepresentation a B := by
  intro b hb v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change U.quotientRepresentation b
      (U.quotientRepresentation a (U.toSubmodule.mkQ v) - U.toSubmodule.mkQ v) =
      U.quotientRepresentation a (U.toSubmodule.mkQ v) - U.toSubmodule.mkQ v
    simpa only [map_sub, Subrepresentation.quotientRepresentation_mk] using
      congrArg U.toSubmodule.mkQ (h b hb v)

/-- An irreducible section means an actual irreducible invariant subquotient,
up to an equivariant linear isomorphism. Trivial representations are allowed. -/
def IsIrreducibleSection (ρ : Representation k G V) (σ : Representation k G W) : Prop :=
  σ.IsIrreducible ∧ ∃ U : Subrepresentation ρ,
    ∃ N : Subrepresentation U.toRepresentation, Nonempty (N.quotientRepresentation.Equiv σ)

/-- Every irreducible section inherits the displacement identity; no
faithfulness of the section is asserted. -/
theorem FixesDisplacements.irreducibleSection {a : G} {B : Subgroup G}
    (h : FixesDisplacements ρ a B) (hs : IsIrreducibleSection ρ σ) :
    FixesDisplacements σ a B := by
  obtain ⟨_, U, N, ⟨e⟩⟩ := hs
  exact ((h.subrepresentation U).quotient N).of_surjective
    e.toIntertwiningMap e.toLinearEquiv.surjective

end Linear

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L B : Subgroup G) (a : G)

/-- The inputs of GLS2 Theorem 25.14, without any classification conclusions. -/
structure Hypotheses : Prop where
  faithful : Function.Injective ρ
  component : IsComponent G L
  elementary : IsElementaryAbelian 2 B
  card_four : Nat.card B = 4
  mem : a ∈ B
  involution : orderOf a = 2
  moves : L.map (MulAut.conj a).toMonoidHom ≠ L
  quadratic : FixesDisplacements ρ a B
  centralizer : B ⊓ Subgroup.centralizer (L : Set G) = ⊥

variable {ρ L B a}

/-- The moving element prevents the four-group from normalizing the component. -/
theorem Hypotheses.not_normalizes (h : Hypotheses ρ L B a) :
    ¬ B ≤ normalizer (L : Set G) := by
  intro hN
  exact h.moves (mem_normalizer_iff_map_conj_eq.mp (hN h.mem))

/-- The two distinct components in the source hypothesis commute. -/
theorem Hypotheses.commuting_conjugate (h : Hypotheses ρ L B a) :
    ⁅L, L.map (MulAut.conj a).toMonoidHom⁆ = ⊥ :=
  h.component.commutator_eq_bot_of_ne (h.component.map_conj a) (Ne.symm h.moves)

/-- The actual orbit is perfect, relatively normal in `L ⊔ B`, and generated
by its commutators with `B`. Ambient normality is not needed. -/
theorem Hypotheses.orbit_properties (h : Hypotheses ρ L B a) :
    Group.IsPerfect (componentOrbit L B) ∧
      ((componentOrbit L B).subgroupOf (L ⊔ B)).Normal ∧
      ⁅componentOrbit L B, B⁆ = componentOrbit L B :=
  h.component.orbit_properties B h.not_normalizes

end Representation.QuadraticFourGroup

end
