/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianAxisNeighborCatalogue.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianEightAxisNeighbors

/-!
# IcosianAxisNeighborCatalogue

The two coordinate neighbors and eight explicit edge neighbors exhaust the ten
neighbors of the first axis. Injectivity and the known count prove bijectivity.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianAxisNeighborCatalogue.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

def icosianTwoAxisNeighbor (i : Fin 2) : IcosianAxisNeighbor :=
  ⟨icosianRootAxisPoint i.succ,icosianRootAxisPoints_orthogonal 0 i.succ (Fin.succ_ne_zero i).symm⟩

theorem icosianTwoAxisNeighbor_injective : Function.Injective icosianTwoAxisNeighbor := by
  intro i j h
  exact Fin.succ_injective 2 (icosianRootAxisPoint_injective (congrArg Subtype.val h))

theorem icosianEightNeighbor_ne_twoAxis (i : Fin 8) (j : Fin 2) :
    icosianEightNeighborPoint i≠icosianTwoAxisNeighbor j := by
  intro h
  have hp : icosianRootPoint (icosianEightNeighborRoot i)=
      icosianRootPoint (icosianAxisRoot (j.succ,1)) :=
    congrArg (fun p : IcosianAxisNeighbor => p.val.val) h
  obtain ⟨u,hu⟩ := (icosianRootPoint_eq_iff (icosianAxisRoot (j.succ,1)) (icosianEightNeighborRoot i)).mp hp
  fin_cases j
  · have ht := congrArg (fun r : IcosianRoot => (r.val 2).val) hu
    change (icosianEightNeighborScalar i).val=0*u.val.val at ht
    rw [zero_mul] at ht
    have hn := icosianEightNeighborScalar_norm i
    rw [ht] at hn
    norm_num [icosianNorm] at hn
  · have ht := congrArg (fun r : IcosianRoot => (r.val 1).val) hu
    change (icosianEightNeighborScalar 0).val=0*u.val.val at ht
    rw [zero_mul] at ht
    have hn := icosianEightNeighborScalar_norm 0
    rw [ht] at hn
    norm_num [icosianNorm] at hn

def icosianAxisNeighborCatalogue : (Fin 2 ⊕ Fin 8) → IcosianAxisNeighbor :=
  Sum.elim icosianTwoAxisNeighbor icosianEightNeighborPoint

theorem icosianAxisNeighborCatalogue_injective : Function.Injective icosianAxisNeighborCatalogue := by
  intro p q h
  cases p with
  | inl i =>
    cases q with
    | inl j => exact congrArg Sum.inl (icosianTwoAxisNeighbor_injective h)
    | inr j => exact (icosianEightNeighbor_ne_twoAxis j i h.symm).elim
  | inr i =>
    cases q with
    | inl j => exact (icosianEightNeighbor_ne_twoAxis i j h).elim
    | inr j => exact congrArg Sum.inr (icosianEightNeighborPoint_injective h)

/-- The two axes and eight explicitly constructed edge lines exhaust the
local geometry by the independent count ten. -/
theorem icosianAxisNeighborCatalogue_bijective : Function.Bijective icosianAxisNeighborCatalogue := by
  let : Finite IcosianAxisNeighbor := Nat.finite_of_card_ne_zero (by rw [icosianAxisNeighbors_card]; decide)
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨icosianAxisNeighborCatalogue_injective,?_⟩
  rw [icosianAxisNeighbors_card,Nat.card_sum]
  norm_num

end Atlas.Conway
