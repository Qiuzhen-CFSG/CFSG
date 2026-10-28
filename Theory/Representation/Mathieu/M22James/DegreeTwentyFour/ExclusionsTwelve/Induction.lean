module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.Reduction
public import Mathlib.RepresentationTheory.Induced

/-!
# Inducing the small point constituents

Induce the two concrete six-dimensional binary SL₃(4) modules through the
literal point embedding in the triple Mathieu cover. The coinvariant formula
for Frobenius reciprocity sends a nonzero local intertwiner to a nonzero global
one; evaluation at the identity coset proves nonvanishing. The reductions in
`Reduction` therefore turn binary degree twenty-four into a simple quotient
of one of these two specified induced modules, after dualizing if necessary.

`InducedQuotientExclusion` states the finite-module calculation still required.
No composition-factor list, splitting, or recognition theorem is assumed to
have been proved. Its proof is an independent prerequisite of the final gap.
Source context: Guralnick–Malle I, Proposition 5.1, pp.15–16. The induction
formula follows Mathlib's `Rep.indResHomEquiv`, with its actual inverse/right
translation convention, and works across arbitrary vector-space universes.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve
open Representation Uniqueness Uniqueness.PointRestriction.PointModel
open Representation.SL3FourLocalCatalogue
open scoped MonoidAlgebra TensorProduct
universe u

/-- The checked point-stabilizer identification followed by its actual inclusion. -/
def pointEmbedding : Representation.SL3FourLocalCatalogue.SL →* M22TripleCover :=
  pointStabilizer.subtype.comp pointStabilizerEquiv.symm.toMonoidHom

/-- The actual coinvariant carrier of the induced constituent. -/
abbrev InducedSpace (a : Constituent) := IndV pointEmbedding (constituent a)

/-- Induction of the natural or dual binary point action. -/
def inducedRepresentation (a : Constituent) :
    Representation (ZMod 2) M22TripleCover (InducedSpace a) :=
  ind pointEmbedding (constituent a)

/-- This fixed induced module has no simple binary quotient of degree twenty-four. -/
def InducedQuotientExclusion (a : Constituent) : Prop :=
  ∀ (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) M22TripleCover V),
    ρ.IsIrreducible → Module.finrank (ZMod 2) V = 24 →
    ∀ f : IntertwiningMap (inducedRepresentation a) ρ, f = 0

variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) M22TripleCover V) {a : Constituent}

/-- Frobenius reciprocity on actual intertwining maps. -/
def inducedMap (f : IntertwiningMap (constituent a) (pointAction ρ)) :
    IntertwiningMap (inducedRepresentation a) ρ where
  toLinearMap := Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun g =>
      ρ g⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).toLinearMap)
    (fun g => by
      ext h v
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
      simp [Representation.ofMulAction_single, mul_inv_rev, pointEmbedding]
      rw [IntertwiningMap.isIntertwining _ _ f]
      simp [pointAction])
  isIntertwining' g := by ext; simp [inducedRepresentation]

theorem inducedMap_mk_one (f : IntertwiningMap (constituent a) (pointAction ρ))
    (v : Representation.SL3FourLocalCatalogue.W) :
    inducedMap ρ f (IndV.mk pointEmbedding (constituent a) 1 v) = f v := by
  simp [inducedMap]

theorem inducedMap_ne_zero (f : IntertwiningMap (constituent a) (pointAction ρ))
    (hf : f ≠ 0) : inducedMap ρ f ≠ 0 := by
  intro h
  apply hf
  ext v
  have he := congrArg (fun T : IntertwiningMap (inducedRepresentation a) ρ =>
    T (IndV.mk pointEmbedding (constituent a) 1 v)) h
  change inducedMap ρ f (IndV.mk pointEmbedding (constituent a) 1 v) = 0 at he
  rw [inducedMap_mk_one] at he
  exact he

/-- Both possible point filtrations are excluded by the two finite induced-module calculations. -/
theorem binary_exclusion_of_induced
    [FiniteDimensional (ZMod 2) V] [ρ.IsIrreducible]
    (hc : ∀ a, InducedQuotientExclusion.{u} a)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 24) : False := by
  rcases point_constituent_or_dual ρ hf hd with ⟨a, f, hf'⟩ | ⟨a, f, hf'⟩
  · exact inducedMap_ne_zero ρ f hf'
      (hc a V ρ inferInstance hd (inducedMap ρ f))
  · let := dual_isIrreducible ρ
    exact inducedMap_ne_zero ρ.dual f hf'
      (hc a (Module.Dual (ZMod 2) V) ρ.dual inferInstance
        (Subspace.dual_finrank_eq.trans hd) (inducedMap ρ.dual f))

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve
