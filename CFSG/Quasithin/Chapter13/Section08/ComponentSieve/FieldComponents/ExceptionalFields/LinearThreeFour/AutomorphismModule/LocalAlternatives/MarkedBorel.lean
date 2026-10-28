module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.ActionLift
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.BorelTransport

/-!
# The marked Borel input for the SL₃(4) calculation

This interface separates two unfinished arguments. The intrinsic calculation
uses two normal, two-perfect factors of the actual Sylow normalizer, each
with quotient of order three, and the prescribed fixing/inverting action
modulo each factor's own two-core. The source marking must construct these
factors as the images of the actual L₀ and L₁,+.

The record contains no automorphism classification or central-image conclusion.
It does not assert that the source configuration supplies its fields. In
particular, neither the Borel two-core nor the factors' two-cores are discarded.

Source: Aschbacher–Smith, Notation 13.2.1 and 13.2.2(3), printed p.877,
and the SL₃(4) paragraph of 13.8.20, printed p.955 (PDF p.972).
-/

@[expose] public section
open Subgroup Representation.SL3FourNaturalDual
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives
open LinearThree.Geometry.CoveredProduct

/-- Intrinsic hypotheses for the marked Borel calculation, before classifying the actor. -/
structure MarkedBorelFactors (α : MulAut SL) where
  sylow : Sylow 2 SL
  zeroFactor : Subgroup SL
  plusFactor : Subgroup SL
  zero_le : zeroFactor ≤ normalizer (sylow : Set SL)
  plus_le : plusFactor ≤ normalizer (sylow : Set SL)
  zero_normal : (zeroFactor.subgroupOf (normalizer (sylow : Set SL))).Normal
  plus_normal : (plusFactor.subgroupOf (normalizer (sylow : Set SL))).Normal
  zero_perfect : IsPPerfect 2 zeroFactor
  plus_perfect : IsPPerfect 2 plusFactor
  zero_quotient_card : Nat.card (zeroFactor ⧸ pCore 2 zeroFactor) = 3
  plus_quotient_card : Nat.card (plusFactor ⧸ pCore 2 plusFactor) = 3
  generate : zeroFactor ⊔ plusFactor = normalizer (sylow : Set SL)
  sylow_stable : (sylow : Subgroup SL).map α.toMonoidHom = sylow
  fix_zero : ∀ x ∈ zeroFactor, α x * x⁻¹ ∈ zeroFactor.pCoreIn 2
  invert_plus : ∀ x ∈ plusFactor, α x * x ∈ plusFactor.pCoreIn 2

variable {G : Type*} [Group G]

/-- Source marking is an intermediate conclusion to be constructed, not a standing hypothesis. -/
structure SourceBorelMarking (H K L T V₁ : Subgroup G)
    [(Source.starImage H K).Normal] (eK : Source.starImage H K ≃* SL)
    (t : Source.Hstar H) where
  factors : MarkedBorelFactors (sourceConjugation H K eK t)
  zero_eq : factors.zeroFactor = modelImage H K (ResidualPlacement.zero L) eK
  plus_eq : factors.plusFactor = modelImage H K (ResidualPlacement.plus L T V₁) eK

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives
