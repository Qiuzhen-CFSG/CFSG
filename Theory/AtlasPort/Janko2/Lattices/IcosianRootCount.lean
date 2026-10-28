/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianRootCount.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianRootFamilyShapes

/-!
# Icosian Root Count

The actual Hermitian norm-two roots split into four disjoint exhaustive
coordinate-norm families. Their counts 360, 2880, 23040, and 11520
sum to 37800 through an explicit equivalence with the family fibers.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianRootCount.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators

abbrev IcosianRootShapeFiber (i : Fin 4) := {r : IcosianRoot // HasIcosianRootShape r i}

def icosianRootShapeFiberAxis : IcosianRootShapeFiber 0 ≃ IcosianAxisRoot :=
  Equiv.subtypeEquivRight icosianRootShape_axis

def icosianRootShapeFiberEdge : IcosianRootShapeFiber 1 ≃ IcosianEdgeRoot :=
  Equiv.subtypeEquivRight icosianRootShape_edge

def icosianRootShapeFiberC : IcosianRootShapeFiber 2 ≃ IcosianRootCFamily :=
  Equiv.subtypeEquivRight icosianRootShape_c

def icosianRootShapeFiberD : IcosianRootShapeFiber 3 ≃ IcosianRootDFamily :=
  Equiv.subtypeEquivRight icosianRootShape_d

theorem icosianRootShapeFiber_card (i : Fin 4) :
    Nat.card (IcosianRootShapeFiber i)=![360,2880,23040,11520] i := by
  fin_cases i
  · exact (Nat.card_congr icosianRootShapeFiberAxis).trans icosianAxisRoots_card
  · exact (Nat.card_congr icosianRootShapeFiberEdge).trans icosianEdgeRoots_card
  · exact (Nat.card_congr icosianRootShapeFiberC).trans icosianRootCFamily_card
  · exact (Nat.card_congr icosianRootShapeFiberD).trans icosianRootDFamily_card

instance icosianRootShapeFiber_finite (i : Fin 4) : Finite (IcosianRootShapeFiber i) := by
  apply Nat.finite_of_card_ne_zero
  rw [icosianRootShapeFiber_card]
  fin_cases i <;> decide

def icosianRootShapeEquiv : (Σ i : Fin 4,IcosianRootShapeFiber i) ≃ IcosianRoot :=
  Equiv.ofBijective (fun p => p.2.val) (by
    constructor
    · rintro ⟨i,r⟩ ⟨j,s⟩ h
      change r.val=s.val at h
      have hij : i=j := icosianRootShape_unique r.val r.property (h.symm ▸ s.property)
      subst j
      exact congrArg (Sigma.mk i) (Subtype.ext h)
    · intro r
      obtain ⟨i,hi⟩ := icosianRootShape_exhaustive r
      exact ⟨⟨i,r,hi⟩,rfl⟩)

/-- The actual icosian Leech lattice has 37800 quaternionic roots of norm two.
The four disjoint coordinate norm families have 360, 2880, 23040 and 11520 roots. -/
theorem icosianRoots_card : Nat.card IcosianRoot=37800 := by
  rw [← Nat.card_congr icosianRootShapeEquiv,Nat.card_sigma]
  simp [icosianRootShapeFiber_card,Fin.sum_univ_succ]

instance icosianRoot_finite : Finite IcosianRoot :=
  Nat.finite_of_card_ne_zero (by rw [icosianRoots_card]; decide)

end Atlas.Lattices
