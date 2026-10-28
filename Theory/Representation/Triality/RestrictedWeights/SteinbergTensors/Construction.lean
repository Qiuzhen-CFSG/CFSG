module

public import Theory.AlgebraicGroup.RootSystems.TypeD4RestrictedWeights
public import Theory.AlgebraicGroup.Representations.Algebraic.HighestWeight
public import Mathlib.RepresentationTheory.Character
public import Theory.Representation.SubrepresentationLattice

/-!
# Rational basic D4 factors and their actual tensor products

The inputs carry nonzero finite-dimensional vector spaces, rational irreducible
point-group actions and highest-weight vectors. No finite restriction theorem,
tensor irreducibility, or classification is included among the inputs.

The tensor construction uses pullback along the specified point Frobenius and
`Representation.tprod`. The degree formula is elementary linear algebra. The
one-factor equivalence retains the field-two case explicitly.

Source: GLS3, Definitions 2.8.1 and 2.8.3 and Corollary 2.8.6(a).
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

/-- An actual nonzero rational irreducible algebraic representation. -/
structure RationalFactor (K : Variety k) [AlgebraicGroup K] where
  Space : Type u
  [addCommGroup : AddCommGroup Space]
  [module : Module k Space]
  [finiteDimensional : FiniteDimensional k Space]
  [nonzero : Nontrivial Space]
  action : RationalRepresentation K Space
  irreducible : IsIrreducibleRepresentation action

attribute [instance] RationalFactor.addCommGroup RationalFactor.module
  RationalFactor.finiteDimensional RationalFactor.nonzero

/-- A family with the actual binary highest weights. The geometric setup must
identify `e` with the simple-coroot coordinates for the specified Borel and torus. -/
structure RationalBasicFamily (B T : ClosedSubgroup K) (e : Weight ↪ TorusWeight T) where
  factor : BasicWeight → RationalFactor K
  highest : ∀ a, ∃ v, HasHighWeight (factor a).action B T v (e (coefficient a))

/-- Pull back the point action along an actual group homomorphism. -/
def RationalFactor.restrict (A : RationalFactor K) {G : Type v} [Group G]
    (ι : G →* Variety.Point K) : FDRep k G :=
  FDRep.of (((Units.coeHom _).comp A.action.action).comp ι)

/-- Pullback keeps the vector space, hence its dimension. -/
theorem RationalFactor.finrank_restrict (A : RationalFactor K) {G : Type v} [Group G]
    (ι : G →* Variety.Point K) :
    Module.finrank k (A.restrict ι) = Module.finrank k A.Space := rfl

/-- Every rational basic factor is nonzero. -/
theorem RationalFactor.finrank_pos (A : RationalFactor K) :
    0 < Module.finrank k A.Space := Module.finrank_pos

/-- On the full point group the basic factor is an irreducible representation
in Mathlib's sense, which additionally requires a nonzero module. -/
theorem RationalFactor.point_irreducible (A : RationalFactor K) :
    Representation.IsIrreducible (A.restrict (MonoidHom.id _)).ρ := by
  let : Nontrivial (A.restrict (MonoidHom.id _)) :=
    inferInstanceAs (Nontrivial A.Space)
  refine ⟨fun S => ?_⟩
  rcases A.irreducible.2 S.toSubmodule
      (fun g v hv => S.apply_mem_toSubmodule g hv) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

/-- Algebraic intertwining equivalences restrict to genuine finite-group
intertwining equivalences along any specified homomorphism. -/
def restrictEquiv (A C : RationalFactor K)
    (f : A.Space ≃ₗ[k] C.Space) (hf : Intertwines A.action C.action f.toLinearMap)
    {G : Type v} [Group G] (ι : G →* Variety.Point K) :
    Representation.Equiv (A.restrict ι).ρ (C.restrict ι).ρ :=
  .mk f (fun g => LinearMap.ext (hf (ι g)))

section Tensor
variable {G : Type v} [Group G]

/-- The iterated tensor product of the first `n` actual representations. -/
def tensorPrefix (V : ℕ → FDRep k G) : ℕ → FDRep k G
  | 0 => FDRep.of (Representation.trivial k G k)
  | n + 1 => FDRep.of (Representation.tprod (tensorPrefix V n).ρ (V n).ρ)

omit [IsAlgClosed k] in
/-- The tensor product has the product of the factor dimensions. -/
theorem finrank_tensorPrefix (V : ℕ → FDRep k G) (n : ℕ) :
    Module.finrank k (tensorPrefix V n) =
      ∏ i ∈ Finset.range n, Module.finrank k (V i) := by
  induction n with
  | zero => exact Module.finrank_self k
  | succ n ih =>
    change Module.finrank k (TensorProduct k (tensorPrefix V n) (V n)) = _
    rw [Module.finrank_tensorProduct, ih, Finset.prod_range_succ]

/-- The one-factor tensor is actually equivalent to its factor. -/
def tensorPrefixOneEquiv (V : ℕ → FDRep k G) :
    Representation.Equiv (tensorPrefix V 1).ρ (V 0).ρ := by
  refine .mk (TensorProduct.lid k (V 0)) ?_
  intro g
  apply TensorProduct.ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro v
  change k at c
  change c • (V 0).ρ g v = (V 0).ρ g (c • v)
  exact (map_smul _ _ _).symm

end Tensor

/-- The `i`th factor is pulled back along the `i`th Frobenius iterate before
restriction. On a genuine setup `φ` is the ordinary characteristic-two Frobenius. -/
def twistedFactor (A : BasicWeight → RationalFactor K)
    (φ : Monoid.End (Variety.Point K))
    {G : Type v} [Group G] (ι : G →* Variety.Point K)
    (a : BasicWeight) (i : ℕ) : FDRep k G :=
  (A a).restrict ((φ ^ i).comp ι)

/-- The actual restricted product with exponents `1,2,...,2^(n-1)`. -/
def tensor (A : BasicWeight → RationalFactor K)
    (φ : Monoid.End (Variety.Point K))
    {G : Type v} [Group G] (ι : G →* Variety.Point K)
    (a : ℕ → BasicWeight) (n : ℕ) : FDRep k G :=
  tensorPrefix (fun i => twistedFactor A φ ι (a i) i) n

/-- The product formula for the specified representation, independent of any
irreducibility or exhaustivity assertion. -/
theorem finrank_tensor (A : BasicWeight → RationalFactor K)
    (φ : Monoid.End (Variety.Point K))
    {G : Type v} [Group G] (ι : G →* Variety.Point K)
    (a : ℕ → BasicWeight) (n : ℕ) :
    Module.finrank k (tensor A φ ι a n) =
      ∏ i ∈ Finset.range n, Module.finrank k (A (a i)).Space := by
  rw [tensor, finrank_tensorPrefix]
  rfl

/-- Explicit inclusion of `n = 1`: the tensor is equivalent to the restriction
of its single basic factor. -/
def tensorOneEquiv (A : BasicWeight → RationalFactor K)
    (φ : Monoid.End (Variety.Point K))
    {G : Type v} [Group G] (ι : G →* Variety.Point K)
    (a : ℕ → BasicWeight) :
    Representation.Equiv (tensor A φ ι a 1).ρ ((A (a 0)).restrict ι).ρ :=
  tensorPrefixOneEquiv (fun i => twistedFactor A φ ι (a i) i)

/-- The point-group tensor action, packaged as an algebraic representation.
Its rationality and irreducibility are separate theorem obligations. -/
def rationalTensor (A : BasicWeight → RationalFactor K)
    (φ : Monoid.End (Variety.Point K)) (a : ℕ → BasicWeight) (n : ℕ) :
    RationalRepresentation K (tensor A φ (MonoidHom.id _) a n) where
  action := Representation.asGroupHom (tensor A φ (MonoidHom.id _) a n).ρ

/-- The rational tensor package has exactly the previously constructed action. -/
theorem rationalTensor_action (A : BasicWeight → RationalFactor K)
    (φ : Monoid.End (Variety.Point K)) (a : ℕ → BasicWeight) (n : ℕ)
    (g : Variety.Point K) :
    ((rationalTensor A φ a n).action g : Module.End k _) =
      (tensor A φ (MonoidHom.id _) a n).ρ g :=
  Representation.asGroupHom_apply _ g

end Triality.RestrictedWeights.SteinbergTensors
