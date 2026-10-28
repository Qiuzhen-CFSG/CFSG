/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co2PairSplitting.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co2LocalWitness
public import Theory.AtlasPort.OtherSporadic.GroupTheory.InvolutionSection

/-!
The split marked-pair permutation quotient of the local Co2 subgroup.
A concrete involution gives a section and identifies the Mathieu kernel.

Source: Gerald Höhn, `Atlas/Conway/Co2PairSplitting.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
set_option maxRecDepth 10000

abbrev Co2MarkedPairGroup := Mathieu22PairModel ((0,0),0)
  (⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩ : Mathieu23Points ((0,0),0))

abbrev Co2MarkedPair := ({((0,0),0),((0,0),1)} : Set Omega)

def co2LocalSwap : Co2MarkedPairGroup :=
  ⟨co2PairSwap,(Atlas.GroupTheory.pairStabilizer_mem _ _ (by decide) _).mpr
    (Or.inr ⟨co2PairSwap_shape.1,co2PairSwap_shape.2.1⟩)⟩

theorem co2LocalSwap_sq : co2LocalSwap * co2LocalSwap = 1 :=
  Subtype.ext co2PairSwap_shape.2.2

def co2PairRestriction : Co2MarkedPairGroup →* Equiv.Perm Co2MarkedPair :=
  mathieu22PairRestriction ((0,0),0)
    ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩

theorem co2PairRestriction_swap_ne : co2PairRestriction co2LocalSwap ≠ 1 := by
  intro he
  have hh := congrArg (fun p : Equiv.Perm Co2MarkedPair =>
    (p ⟨((0,0),0),Or.inl rfl⟩).val) he
  change co2PairSwap.val ((0,0),0) = ((0,0),0) at hh
  rw [co2PairSwap_shape.1] at hh
  exact (by decide : ((0,0),1) ≠ (((0,0),0) : Omega)) hh

theorem co2MarkedPair_perms_card : Nat.card (Equiv.Perm Co2MarkedPair) = 2 := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_perm]
  have hc : Fintype.card Co2MarkedPair = 2 := by
    simp [Co2MarkedPair]
  rw [hc]
  decide

/-- A proved splitting of the actual pair restriction, from the lattice involution. -/
def co2PairSection : Equiv.Perm Co2MarkedPair →* Co2MarkedPairGroup :=
  Atlas.GroupTheory.involutionQuotientSection co2PairRestriction co2MarkedPair_perms_card
    co2LocalSwap co2LocalSwap_sq co2PairRestriction_swap_ne

theorem co2PairSection_rightInverse (p : Equiv.Perm Co2MarkedPair) :
    co2PairRestriction (co2PairSection p) = p :=
  Atlas.GroupTheory.involutionQuotientSection_rightInverse co2PairRestriction co2MarkedPair_perms_card
    co2LocalSwap co2LocalSwap_sq co2PairRestriction_swap_ne p

def co2NormalWitnessMonomial : GolayMonomialGroup :=
  SemidirectProduct.inl (Multiplicative.ofAdd (golayBasis 0)) * co2WitnessMonomial *
    SemidirectProduct.inl (Multiplicative.ofAdd (golayBasis 0))

theorem co2NormalWitnessMonomial_image :
    monomialEmbedding co2NormalWitnessMonomial = co2NormalWitness.val := by
  rw [co2NormalWitness_formula]
  unfold co2NormalWitnessMonomial
  rw [map_mul,map_mul,co2WitnessMonomial_image]
  have hs : monomialEmbedding (SemidirectProduct.inl (Multiplicative.ofAdd (golayBasis 0))) =
      co2ConnectorSign := congrArg (fun f : Multiplicative golay →* LeechIsometryGroup =>
        f (Multiplicative.ofAdd (golayBasis 0))) monomial_inl
  rw [hs]

theorem co2NormalWitnessMonomial_right : co2NormalWitnessMonomial.right = co2PairSwap := by
  change (1 * co2PairSwap) * 1 = co2PairSwap
  simp

theorem co2NormalWitness_projection :
    Atlas.Sporadic.Conway2.pairProjection ⟨co2NormalWitness,co2NormalWitness_local⟩ =
      co2LocalSwap := by
  let e := Atlas.Sporadic.Conway2.localSemidirectEquiv
  let w : Atlas.Sporadic.Conway2.LocalGroup := ⟨co2NormalWitness,co2NormalWitness_local⟩
  let m := e.symm w
  have he : monomialEmbedding (pairSetMonomialInclusion ((0,0),0)
      ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩ m) = co2NormalWitness.val :=
    congrArg (fun g : Atlas.Sporadic.Conway2.LocalGroup => g.val.val) (e.apply_symm_apply w)
  have hm := monomialEmbedding_injective (he.trans co2NormalWitnessMonomial_image.symm)
  have hr := congrArg SemidirectProduct.right hm
  apply Subtype.ext
  change m.right.val = co2PairSwap
  exact hr.trans co2NormalWitnessMonomial_right

theorem co2NormalWitness_projection_outside_kernel :
    Atlas.Sporadic.Conway2.pairProjection ⟨co2NormalWitness,co2NormalWitness_local⟩ ∉
      co2PairRestriction.ker := by
  rw [co2NormalWitness_projection]
  exact co2PairRestriction_swap_ne

end Atlas.Conway
