module

public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.Exceptional
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.RootElements
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.FieldAction
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ResidualAction
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.RootElements
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.FieldAction
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.Reduction

/-!
# Earlier exceptional rows consumed by the residual comparison

These are explicit inputs, not assertions of the involution tables. Actors
are automorphisms of the concrete carriers, roots are actual elements, and
the field rows identify the two-residual with a genuine smaller derived
group. The numerical clauses retain only the odd-order information needed
in the comparison. In particular the triality clause requests one divisor,
not a full order or simplicity theorem.

The binary G₂ row uses the action of the full octonion group on its actual
commutator. Its inner residual is the already constructed quaternion--cubic
subgroup K, of order 24; its outer residual is A₄. Ree parameters are positive;
the Tits endpoint uses the separate full binary Ree involution calculation.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 16.1.2--4,
printed pp.1170--1171, and the comparison in 16.4.11(2), p.1193.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional
open Subgroup

/-- The two G₂ rows, including the derived half-field endpoint at f = 2. -/
structure G2InvolutionRows (F : Type*) [Field F] (f : ℕ) : Prop where
  inner_root : ∀ a : MulAut (Atlas.G2.Model F), orderOf a = 2 →
    (∃ x, a = MulAut.conj x) →
    ∃ x : Atlas.G2.Model F, Atlas.G2.EvenInvolutionGeometry.IsRootElement x ∧
      a = MulAut.conj x ∧
      ∃ k : ℕ, Nat.card a.fixedSubgroup ∣ 2 ^ k * ((2 ^ f) ^ 2 - 1)
  outer_field : ∀ a : MulAut (Atlas.G2.Model F), orderOf a = 2 →
    (¬ ∃ x, a = MulAut.conj x) →
    ∃ m : ℕ, 0 < m ∧ f = 2 * m ∧
      (∃ (σ : F ≃+* F) (c : Atlas.G2.Model F),
        (∀ x : F, σ x = x ^ (2 ^ m)) ∧
        a = MulAut.conj c * Atlas.G2.LieAutomorphismExtensions.fieldAction σ *
          (MulAut.conj c)⁻¹) ∧
      Nonempty (pResidual 2 a.fixedSubgroup ≃*
        commutator (Atlas.G2.Model (GaloisField 2 m)))

/-- G₂ table clauses at the exact field witnesses in Theorem C. -/
def G2InvolutionTable : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (f : ℕ), 2 ≤ f →
    Nat.card F = 2 ^ f → G2InvolutionRows F f

/-- Genuine graph-field triality rows, with the coefficient action specified. -/
structure TrialityInvolutionRows (f : ℕ) (hf : 0 < f) : Prop where
  inner_root : ∀ a : MulAut (Triality.Standard.BinaryCarrier f hf), orderOf a = 2 →
    (∃ x, a = MulAut.conj x) →
    ∃ x : Triality.Standard.BinaryCarrier f hf,
      (Triality.Standard.EvenInvolutionGeometry.IsLongRootInvolution f hf x ∨
        Triality.Standard.EvenInvolutionGeometry.IsShortRootInvolution f hf x) ∧
      a = MulAut.conj x ∧
      ∃ k : ℕ, Nat.card a.fixedSubgroup ∣ 2 ^ k * ((2 ^ f) ^ 6 - 1)
  outer_field : ∀ a : MulAut (Triality.Standard.BinaryCarrier f hf), orderOf a = 2 →
    (¬ ∃ x, a = MulAut.conj x) →
    ∃ (m : ℕ) (hm : 0 < m), f = 2 * m ∧
      (∃ b : MulAut (Triality.Standard.BinaryCarrier f hf),
        b * a * b⁻¹ = Triality.Standard.OuterOdd.coefficientAction
          (Triality.Standard.binaryParameters f hf)
          (Triality.Standard.EvenField.coefficientFrobenius f hf (3 * m))) ∧
      Nonempty (pResidual 2 a.fixedSubgroup ≃*
        commutator (Triality.Standard.BinaryCarrier m hm))
  smaller_odd_divisor : ∀ (m : ℕ) (hm : 0 < m), f = 2 * m →
    ((2 ^ m) ^ 8 + (2 ^ m) ^ 4 + 1) * ((2 ^ m) ^ 6 - 1) ∣
      Nat.card (commutator (Triality.Standard.BinaryCarrier m hm))

/-- The f = 1 triality endpoint is included; an outer field row forces f even. -/
def TrialityInvolutionTable : Prop :=
  ∀ (f : ℕ) (hf : 0 < f), TrialityInvolutionRows f hf

/-- The source root actions on G₂(2)′, retaining the full acting group. -/
structure BinaryG2InvolutionRows : Prop where
  inner_root : ∀ a : MulAut (commutator (Atlas.G2.Model (ZMod 2))), orderOf a = 2 →
    (∃ x, a = MulAut.conj x) →
    ∃ x : Atlas.G2.Model (ZMod 2), x ∈ commutator (Atlas.G2.Model (ZMod 2)) ∧
      Atlas.G2.EvenInvolutionGeometry.IsRootElement x ∧
      a = Atlas.G2.LieAutomorphismExtensions.binaryConjugation x ∧
      Nonempty (pResidual 2 a.fixedSubgroup ≃*
        Atlas.G2.BinaryParabolicPair.ResidualAction.K)
  outer_root : ∀ a : MulAut (commutator (Atlas.G2.Model (ZMod 2))), orderOf a = 2 →
    (¬ ∃ x, a = MulAut.conj x) →
    ∃ x : Atlas.G2.Model (ZMod 2), x ∉ commutator (Atlas.G2.Model (ZMod 2)) ∧
      Atlas.G2.EvenInvolutionGeometry.IsRootElement x ∧
      a = Atlas.G2.LieAutomorphismExtensions.binaryConjugation x ∧
      Nonempty (pResidual 2 a.fixedSubgroup ≃* alternatingGroup (Fin 4))

/-- Only the involutory inner--field coverage is requested for positive Ree
parameters. Coprimality with 2*(m)+1 will eliminate the field part. -/
def ReeInvolutionTable : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ a : MulAut (ReeF4.Model m), orderOf a = 2 →
    ∃ (x : ReeF4.Model m) (k : ℕ),
      a = MulAut.conj x * ReeF4.Parabolics.OuterLocal.fieldAutomorphism m ^ k

/-- The two concrete binary Ree inputs used for Tits. This makes no assertion
that the outer automorphism group of Tits has odd order. -/
structure TitsInvolutionInputs : Prop where
  derived_action : Function.Bijective ReeF4.Parabolics.OuterLocal.binaryDerivedAction
  involutions : Tits.InvolutionRootGeometry.BinaryInvolutionCoverage

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional
