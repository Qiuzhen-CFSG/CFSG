module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification.CommonSimpleRigidity.ProjectiveSummand
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.GroupTheory.Sylow

/-!
# The length of a nonprojective summand of a subgroup restriction

The witness consists of an actual submodule of the restricted representation,
an actual projective complement, and indecomposability and nonprojectivity of
the retained summand. Its composition length is independent of the witness by
the local-endomorphism-ring argument. No Green correspondence or existence of
such a decomposition is asserted here.

For a prime-order Sylow subgroup, Feit VII.1.4--5 gives precisely this form of
restriction to the normalizer. `HasNormalizerLength` fixes the interpretation
of the tildes in VII.2.25, printed p.304; its length is not the composition
length of the original ambient module.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- A unique nonprojective indecomposable summand, up to isomorphism, in the
literal restriction to `H`. Existence is an additional mathematical assertion. -/
structure NonprojectiveRestrictionSummand (H : Subgroup G) (ρ : Representation K G V) where
  carrier : Submodule (MonoidAlgebra K H) (Representation.asModule (ρ.comp H.subtype))
  complement : Submodule (MonoidAlgebra K H) (Representation.asModule (ρ.comp H.subtype))
  isCompl : IsCompl carrier complement
  indecomposable : Module.IsIndecomposable (MonoidAlgebra K H) carrier
  nonprojective : ¬ Module.Projective (MonoidAlgebra K H) carrier
  complement_projective : Module.Projective (MonoidAlgebra K H) complement

namespace NonprojectiveRestrictionSummand

variable {H : Subgroup G} {ρ : Representation K G V}

/-- Composition length over the actual subgroup algebra. -/
@[expose] def length (a : NonprojectiveRestrictionSummand H ρ) : ℕ∞ :=
  Module.length (MonoidAlgebra K H) a.carrier

/-- Two choices of the nonprojective summand of the same restriction agree. -/
theorem equiv [FiniteDimensional K V] (a b : NonprojectiveRestrictionSummand H ρ) :
    Nonempty (a.carrier ≃ₗ[MonoidAlgebra K H] b.carrier) := by
  let : FiniteDimensional K a.carrier :=
    FiniteDimensional.of_injective (a.carrier.subtype.restrictScalars K)
      a.carrier.subtype_injective
  let : Module.Projective (MonoidAlgebra K H) b.complement := b.complement_projective
  exact Module.nonprojective_indecomposable_equiv_of_prod_equiv (F := K)
    a.indecomposable b.indecomposable a.nonprojective
    ((Submodule.prodEquivOfIsCompl _ _ a.isCompl).trans
      (Submodule.prodEquivOfIsCompl _ _ b.isCompl).symm)

/-- The length is therefore independent of the complementary decomposition. -/
theorem length_eq [FiniteDimensional K V] (a b : NonprojectiveRestrictionSummand H ρ) :
    a.length = b.length := by
  obtain ⟨e⟩ := a.equiv b
  exact e.length_eq

end NonprojectiveRestrictionSummand

/-- An actual normalizer restriction has a nonprojective summand of the
specified length. There is no assumption of seriality of the original module. -/
@[expose] def HasNormalizerLength {p : ℕ} (P : Sylow p G)
    (ρ : Representation K G V) (l : ℕ) : Prop :=
  ∃ a : NonprojectiveRestrictionSummand (Subgroup.normalizer (P : Set G)) ρ,
    a.length = l

/-- The length relation is single-valued; it is not an arbitrary numeric label. -/
theorem normalizerLength_unique [FiniteDimensional K V] {p : ℕ} {P : Sylow p G}
    {ρ : Representation K G V} {l k : ℕ}
    (hl : HasNormalizerLength P ρ l) (hk : HasNormalizerLength P ρ k) : l = k := by
  obtain ⟨a, ha⟩ := hl
  obtain ⟨b, hb⟩ := hk
  have h : (l : ℕ∞) = k := ha.symm.trans ((a.length_eq b).trans hb)
  exact_mod_cast h

end Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification
