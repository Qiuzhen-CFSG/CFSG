module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.ActorCompatibility

/-!
# Compatibility of the actual exceptional factor

The geometric actor dichotomy and normal generation by the original cubic
subgroup imply that distinct conjugates of the order-21 candidate commute.
The existing faithful three-space argument supplies cross-fixation, giving
FactorSeed for exactly the same subgroup B. The sole independent premise
is the finite pair-bound theorem, to be discharged by its source owner.

Source: the exceptional factor step of E.6.24, printed p.255.
-/

public section
open Module Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure
variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] {ρ : Representation (ZMod 2) A W} {C B : Subgroup A}

/-- Distinct conjugates of the same actual candidate commute. -/
theorem ExceptionalCandidate.commuting_conjugates_of_pair_bound
    (hB : ExceptionalCandidate ρ C B) (h : Input ρ C)
    (hpair : ∀ a b : A,
      (¬ ∀ c ∈ C.map (MulAut.conj a).toMonoidHom,
        ∀ d ∈ C.map (MulAut.conj b).toMonoidHom, Commute c d) →
      finrank (ZMod 2) ↥(displacementSpan ρ (C.map (MulAut.conj a).toMonoidHom) ⊤ ⊔
        displacementSpan ρ (C.map (MulAut.conj b).toMonoidHom) ⊤) ≤ 3) :
    ∀ a : A, B.map (MulAut.conj a).toMonoidHom ≠ B →
      ∀ b ∈ B, ∀ d ∈ B.map (MulAut.conj a).toMonoidHom, Commute b d :=
  Frobenius21.commuting_conjugates_of_actor_dichotomy hB.contained hB.cyclic_card
    hB.factor_card hB.nonabelian (hB.actor_contained_or_centralizes_of_pair_bound h hpair)

/-- The original exceptional candidate, with its same subgroup marking,
now has every FactorSeed field. -/
theorem ExceptionalCandidate.factorSeed_of_pair_bound
    (hB : ExceptionalCandidate ρ C B) (h : Input ρ C)
    (hpair : ∀ a b : A,
      (¬ ∀ c ∈ C.map (MulAut.conj a).toMonoidHom,
        ∀ d ∈ C.map (MulAut.conj b).toMonoidHom, Commute c d) →
      finrank (ZMod 2) ↥(displacementSpan ρ (C.map (MulAut.conj a).toMonoidHom) ⊤ ⊔
        displacementSpan ρ (C.map (MulAut.conj b).toMonoidHom) ⊤) ≤ 3) : FactorSeed ρ C B :=
  hB.factorSeed_of_commuting_conjugates h.faithful (hB.commuting_conjugates_of_pair_bound h hpair)

end Representation.RegularCyclicNormalClosure
