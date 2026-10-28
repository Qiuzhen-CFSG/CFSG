module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ChevalleyCarrier
public import Theory.AlgebraicGroup.Representations.Algebraic.Irreducible
public import Theory.SpecificGroups.ReeF4.Model
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Actual algebraic factors and their exceptional tensor product

An `AlgebraicFactor` is a nonzero finite-dimensional rational irreducible
representation of the concrete closed F4 Chevalley carrier. It carries its
vector space and action, rather than just a dimension or a family label.
Given a homomorphism from the concrete finite split group to this algebraic
carrier, `exceptionalFactor` restricts such an action to the Ree group after
the specified power of the concrete exceptional endomorphism. The iterated
tensor product is formed using `Representation.tprod`.

This module defines the objects and proves their elementary dimension
formulas. It does not assert the exceptional classification or any lower
bound for nontrivial algebraic factors. `BasicWeights` specifies the four
exceptional basic highest weights separately.

Source: GLS3, Definitions 2.8.1 and 2.8.3, Theorems 2.8.2 and 2.8.5, and
Corollary 2.8.6(b). In that corollary the factors have basic highest weights;
the construction here also makes sense for other rational irreducibles.
-/

public section

open Theory.AlgebraicGroup

namespace ReeF4.BinaryDegree.ExceptionalTensor

universe u v

/-- A nonzero rational irreducible representation of the actual algebraic F4
carrier. No classification or dimension bound is part of this structure. -/
structure AlgebraicFactor (F : Type u) [Field F] [IsAlgClosed F] where
  Space : Type u
  [addCommGroup : AddCommGroup Space]
  [module : Module F Space]
  [finiteDimensional : FiniteDimensional F Space]
  [nonzero : Nontrivial Space]
  action : RationalRepresentation (F4Chevalley.Carrier (k := F)) Space
  irreducible : IsIrreducibleRepresentation action

attribute [instance] AlgebraicFactor.addCommGroup AlgebraicFactor.module
  AlgebraicFactor.finiteDimensional AlgebraicFactor.nonzero

variable {F : Type u} [Field F] [IsAlgClosed F]

/-- Nontriviality of the group action, as distinct from a nonzero vector space. -/
@[expose] def AlgebraicFactor.IsNontrivial (B : AlgebraicFactor F) : Prop :=
  ∃ g, B.action.action g ≠ 1

/-- Restriction of the actual action along a homomorphism into the carrier. -/
@[expose] noncomputable def AlgebraicFactor.restrict (B : AlgebraicFactor F)
    {G : Type v} [Group G]
    (ι : G →* Variety.Point (F4Chevalley.Carrier (k := F))) : FDRep F G :=
  FDRep.of (((Units.coeHom _).comp B.action.action).comp ι)

theorem AlgebraicFactor.finrank_restrict (B : AlgebraicFactor F)
    {G : Type v} [Group G]
    (ι : G →* Variety.Point (F4Chevalley.Carrier (k := F))) :
    Module.finrank F (B.restrict ι) = Module.finrank F B.Space := by rfl

theorem AlgebraicFactor.finrank_pos (B : AlgebraicFactor F) :
    0 < Module.finrank F B.Space := Module.finrank_pos

section TensorPrefix

variable {K : Type u} [Field K] {G : Type v} [Group G]

/-- Tensor the first `n` members of an actual representation family. -/
@[expose] noncomputable def tensorPrefix (V : ℕ → FDRep K G) : ℕ → FDRep K G
  | 0 => FDRep.of (Representation.trivial K G K)
  | n + 1 => FDRep.of (Representation.tprod (tensorPrefix V n).ρ (V n).ρ)

theorem finrank_tensorPrefix (V : ℕ → FDRep K G) (n : ℕ) :
    Module.finrank K (tensorPrefix V n) =
      ∏ i ∈ Finset.range n, Module.finrank K (V i) := by
  induction n with
  | zero =>
    change Module.finrank K K = 1
    exact Module.finrank_self K
  | succ n ih =>
    change Module.finrank K (TensorProduct K (tensorPrefix V n) (V n)) = _
    rw [Module.finrank_tensorProduct, ih, Finset.prod_range_succ]

end TensorPrefix

/-- The actual `i`th factor, twisted by the exceptional endomorphism and
restricted to the concrete Ree fixed subgroup. -/
@[expose] noncomputable def exceptionalFactor {k : ℕ}
    (ι : SplitGroup k →* Variety.Point (F4Chevalley.Carrier (k := F)))
    (B : ZMod (2 * k + 1) → AlgebraicFactor F)
    (i : ZMod (2 * k + 1)) : FDRep F (Model k) :=
  (B i).restrict (ι.comp ((exceptionalEndomorphism k ^ i.val).comp (toSplitGroup k)))

theorem finrank_exceptionalFactor {k : ℕ}
    (ι : SplitGroup k →* Variety.Point (F4Chevalley.Carrier (k := F)))
    (B : ZMod (2 * k + 1) → AlgebraicFactor F) (i : ZMod (2 * k + 1)) :
    Module.finrank F (exceptionalFactor ι B i) = Module.finrank F (B i).Space := by rfl

/-- The `2*k+1` exceptional tensor factors in source order. -/
@[expose] noncomputable def exceptionalTensor {k : ℕ}
    (ι : SplitGroup k →* Variety.Point (F4Chevalley.Carrier (k := F)))
    (B : ZMod (2 * k + 1) → AlgebraicFactor F) : FDRep F (Model k) :=
  tensorPrefix (fun i : ℕ => exceptionalFactor ι B (i : ZMod (2 * k + 1))) (2 * k + 1)

theorem finrank_exceptionalTensor {k : ℕ}
    (ι : SplitGroup k →* Variety.Point (F4Chevalley.Carrier (k := F)))
    (B : ZMod (2 * k + 1) → AlgebraicFactor F) :
    Module.finrank F (exceptionalTensor ι B) =
      ∏ i ∈ Finset.range (2 * k + 1), Module.finrank F (B (i : ZMod (2 * k + 1))).Space := by
  rw [exceptionalTensor, finrank_tensorPrefix]
  rfl

/-- On the actual fixed subgroup, one exceptional step is `k+1` ordinary
Frobenius steps. This follows from the fixed-point equation and `ψ² = F`. -/
theorem exceptional_eq_frobenius_on_model (k : ℕ) (x : Model k) :
    exceptionalEndomorphism k (toSplitGroup k x) =
      (splitFrobeniusEnd k ^ (k + 1)) (toSplitGroup k x) := by
  rw [← exceptionalEndomorphism_sq, ← pow_mul]
  have hn : 2 * (k + 1) = 1 + (2 * k + 1) := by omega
  rw [hn, pow_add, pow_one, ← reeTwist_eq_pow]
  change _ = exceptionalEndomorphism k (reeTwist k (toSplitGroup k x))
  rw [reeTwist_toSplitGroup]

end ReeF4.BinaryDegree.ExceptionalTensor
