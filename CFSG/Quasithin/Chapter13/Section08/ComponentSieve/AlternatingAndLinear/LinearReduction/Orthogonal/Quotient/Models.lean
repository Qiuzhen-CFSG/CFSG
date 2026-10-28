module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.MarkedObstruction
public import Theory.Representation.BinaryPermutation

/-!
# Compatible models for the irreducible orthogonal quotient

The surviving model is the actual natural S₈ representation, using a specified
permutation identification of the actor. The other model is the natural GL₄(2)
module plus its contragredient, restricted to the specified subgroup K*. These
predicates contain intertwining linear equivalences, rather than dimensions.

Once the B.4 alternatives are supplied, the marked-plane obstruction eliminates
the second alternative. Extracting those alternatives from the exact B.4 inputs
remains a separate source obligation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of 13.8.25,
printed pp.959–960, PDF pp.976–977.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient
open Representation Representation.BinaryOffender BinaryLinear

abbrev FourSpace := Fin 4 → ZMod 2

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- The six-dimensional natural module for this fixed permutation marking. -/
def IsEightNatural (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Equiv.Perm (Fin 8)) : Prop :=
  ∃ e : U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8),
    ∀ g v, e (ρ g v) = BinaryPermutation.naturalRepresentation (Fin 8) (eH g) (e v)

/-- A natural-plus-dual model of the restricted K*-action, with one fixed marking. -/
def IsNaturalDualRestriction (ρ : Representation (ZMod 2) H U)
    (K : Subgroup H) (eK : K ≃* BinaryLinear.GL FourSpace) : Prop :=
  ∃ e : U ≃ₗ[ZMod 2] (FourSpace × Module.Dual (ZMod 2) FourSpace),
    ∀ k : K, ∀ v, e (ρ k v) = naturalDualAction (eK k) (e v)

/-- The geometric exclusion retains the actual natural equivalence in the
surviving alternative. This is conditional on the B.4 alternatives, not their
source derivation. No dimension-only recognition is used. -/
theorem natural_of_marked_alternatives (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Equiv.Perm (Fin 8)) (K : Subgroup H)
    (eK : K ≃* BinaryLinear.GL FourSpace)
    (P L : Subgroup K) (hLP : L ≤ P)
    (A F : Submodule (ZMod 2) FourSpace) (hAF : A ≤ F)
    (hA : Module.finrank (ZMod 2) A = 1)
    (hF : Module.finrank (ZMod 2) F + 1 = Module.finrank (ZMod 2) FourSpace)
    (hP : P.map eK.toMonoidHom = parabolic A ⊓ parabolic F)
    (S : Submodule (ZMod 2) U) (hdim : Module.finrank (ZMod 2) S = 2)
    (hstable : ∀ g ∈ P, ∀ v ∈ S, ρ (g : H) v ∈ S)
    (hcomm : subspaceCommutator (ρ.comp K.subtype) S L = S)
    (halternatives : IsEightNatural ρ eH ∨ IsNaturalDualRestriction ρ K eK) :
    IsEightNatural ρ eH := by
  rcases halternatives with hn | hd
  · exact hn
  · exact (not_naturalDual_of_marked_plane (ρ.comp K.subtype) eK.toMonoidHom
      P L hLP A F hAF hA hF hP S hdim hstable hcomm hd).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient
