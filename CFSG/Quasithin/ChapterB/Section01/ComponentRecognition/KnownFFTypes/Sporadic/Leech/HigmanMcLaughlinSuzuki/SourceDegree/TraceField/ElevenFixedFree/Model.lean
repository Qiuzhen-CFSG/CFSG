module

public import Theory.Representation.HigmanSims.Twenty.Marked
public import Theory.Representation.PrimeFixedFree
public import Theory.Representation.AbsolutelyIrreducible
public import Theory.Representation.Quotient
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Mathlib.Algebra.Field.ZMod

/-!
# Assembly of the concrete HS degree-twenty model

The checked word `ab` has order eleven and no fixed vector. The carrier
order contains just one factor of eleven, so cyclic Sylow conjugacy proves
fixed-point-freeness for every order-eleven element. A marked comparison
transports the actual matrices to the degree-100 HS carrier; the simplicity
inherited by the source consumer makes that comparison faithful.

This module assembles two still-explicit inputs: existence of the marked
comparison, and absolute irreducibility of the matrix action. Neither input
is asserted here. It concerns one genuine model, not every absolutely
irreducible action of degree twenty.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
HS paragraph, p.16; ATLAS HSG1-p100B0 and HSG1-f2r20B0.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField.Model

open Sporadic.LeechRelated.HS
open Sporadic.LeechRelated.HS.Twenty

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem orderEleven_fixedFree_of_markedComparison
    [IsSimpleGroup Carrier] (C : MarkedComparison)
    (g : Carrier) (hg : orderOf g = 11) :
    LinearMap.ker (C.action g - 1) = ⊥ := by
  have hx : orderOf (permutationA * permutationB) = 11 := by
    have h := orderOf_injective C.hom C.injective (permutationA * permutationB)
    rw [C.map_eleven, eleven_order] at h
    exact h.symm
  exact Representation.prime_fixedFree_of_one C.action (by decide : Nat.Prime 11)
    (by rw [NormalizerIndex.card_carrier]; decide) hx C.action_eleven_fixedFree g hg

/-- Concrete model assembly. The two mathematical construction inputs remain
explicit until their independent certificates have been proved. -/
theorem exists_model_of_inputs [IsSimpleGroup Carrier]
    (C : MarkedComparison) (habs : representation.IsAbsolutelyIrreducible) :
    ∃ ρ : Representation (ZMod 2) Carrier Vector,
      Function.Injective ρ ∧
        Representation.IsAbsolutelyIrreducible (F := ZMod 2) (G := Carrier) (V := Vector) ρ ∧
        Module.finrank (ZMod 2) Vector = 20 ∧
        ∀ g, orderOf g = 11 → LinearMap.ker (ρ g - 1) = ⊥ := by
  refine ⟨C.action, C.action_injective, ?_, representation_finrank,
    orderEleven_fixedFree_of_markedComparison C⟩
  constructor
  change Representation.IsIrreducible
    ((Representation.extendScalars (AlgebraicClosure (ZMod 2)) representation).comp C.hom)
  exact (Representation.irreducible_comp_surjective_iff C.hom C.surjective _).mpr
    habs.irreducible_of_closure

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField.Model
