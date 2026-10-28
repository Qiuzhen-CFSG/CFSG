module

public import Theory.AlgebraicGroup.Representations.Rational
public import Theory.AlgebraicGroup.Variety.MorphicAction

/-!
# Full flags and their geometric realization interface

A full flag is an increasing submodule chain with successive dimensions
`0, 1, ..., dim V`, indexed by natural numbers and constant afterwards.
Linear automorphisms act by taking images of all its subspaces. A geometric
flag model must identify its points with these flags and induce this exact action.

The two independent inputs to Borel, *Linear Algebraic Groups*, §11.1 are
flag geometry (a complete model for every rational representation) and linear
algebra (a faithful representation with a Borel as the stabilizer of a flag).
These definitions expose their common interface; they do not assert either
existence theorem.
-/

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy

universe u v
variable (k : Type u) [Field k] (V : Type v)
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A full flag, with its `i`th subspace of dimension `i` and its tail equal to
the whole vector space. Natural indexing matches the invariant-chain API. -/
public structure FullFlag (k : Type u) [Field k] (V : Type v)
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] where
  subspace : ℕ → Submodule k V
  monotone : Monotone subspace
  finrank_eq : ∀ i, Module.finrank k (subspace i) = min i (Module.finrank k V)

variable {k V}

@[ext]
public theorem FullFlag.ext {F F' : FullFlag k V}
    (h : ∀ i, F.subspace i = F'.subspace i) : F = F' := by
  cases F
  cases F'
  congr
  exact funext h

/-- Transport a flag by a linear automorphism. -/
@[expose]
public def FullFlag.map (e : V ≃ₗ[k] V) (F : FullFlag k V) : FullFlag k V where
  subspace i := (F.subspace i).map e.toLinearMap
  monotone := fun _ _ h => Submodule.map_mono (F.monotone h)
  finrank_eq i := (e.finrank_map_eq (F.subspace i)).trans (F.finrank_eq i)

/-- The natural general linear action on complete flags. -/
public instance FullFlag.linearAction : MulAction (LinearMap.GeneralLinearGroup k V) (FullFlag k V) where
  smul g F := F.map g.toLinearEquiv
  one_smul F := by
    apply FullFlag.ext
    intro i
    change (F.subspace i).map (1 : Module.End k V) = F.subspace i
    exact Submodule.map_id _
  mul_smul g h F := by
    apply FullFlag.ext
    intro i
    change (F.subspace i).map ((g * h : LinearMap.GeneralLinearGroup k V) : Module.End k V) =
      ((F.subspace i).map (h : Module.End k V)).map (g : Module.End k V)
    exact Submodule.map_comp (h : Module.End k V) (g : Module.End k V) (F.subspace i)

public theorem FullFlag.smul_subspace (g : LinearMap.GeneralLinearGroup k V)
    (F : FullFlag k V) (i : ℕ) :
    (g • F).subspace i = (F.subspace i).map (g : Module.End k V) := rfl

/-- The action of a representation on full flags. -/
public abbrev flagAction {G : Variety k} [AlgebraicGroup G]
    (ρ : RationalRepresentation G V) : MulAction (Variety.Point G) (FullFlag k V) :=
  MulAction.compHom (FullFlag k V) ρ.action

/-- A complete geometric realization of full flags with their actual linear
action. Its existence requires flag-variety geometry, not just linear algebra. -/
public structure FlagModel [IsAlgClosed k] {G : Variety k} [AlgebraicGroup G]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation G V) where
  variety : Variety.Geometric k
  action : Variety.Geometric.MorphicAction G variety
  pointEquiv : Variety.Geometric.Point variety ≃ FullFlag k V
  equivariant : ∀ (g : Variety.Point G) (x : Variety.Geometric.Point variety),
    pointEquiv (action.toMulAction.smul g x) = (flagAction ρ).smul g (pointEquiv x)
  complete : Variety.Geometric.IsComplete variety

/-- Stabilizers in a geometric flag model agree with the actual linear flag
stabilizers. This identifies the eventual Borel stabilizer without a quotient. -/
public theorem FlagModel.smul_eq_iff [IsAlgClosed k]
    {G : Variety k} [AlgebraicGroup G]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {ρ : RationalRepresentation G V} (M : FlagModel ρ)
    (g : Variety.Point G) (x : Variety.Geometric.Point M.variety) :
    M.action.toMulAction.smul g x = x ↔
      (flagAction ρ).smul g (M.pointEquiv x) = M.pointEquiv x := by
  rw [← M.pointEquiv.injective.eq_iff, M.equivariant]

end Theory.AlgebraicGroup.BorelGeometricConjugacy
