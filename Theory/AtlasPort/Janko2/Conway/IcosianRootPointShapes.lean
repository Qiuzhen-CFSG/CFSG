/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianRootPointShapes.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootGeometryCard

/-!
# IcosianRootPointShapes

Right-unit invariance makes root shape intrinsic to a projective root point. Scalar-
fiber counting gives the four shape cardinalities and proves unique, exhaustive
classification.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianRootPointShapes.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped BigOperators

theorem icosianRootNormWord_rightUnit (r : IcosianRoot) (u : icosianNormOneGroup)
    (i : Fin 3) : icosianRootNormWord (icosianRootRightUnit r u) i=icosianRootNormWord r i := by
  apply goldenIntegerToRational_injective
  simp only [icosianRootNormWord,icosianIntegralNorm_spec]
  change icosianNorm ((r.val i).val*u.val.val)=icosianNorm (r.val i).val
  rw [icosianNorm_mul,icosianNormOneGroup_norm,mul_one]

theorem icosianRootShape_of_same_point (r s : IcosianRoot)
    (h : icosianRootPoint s=icosianRootPoint r) (i : Fin 4) :
    HasIcosianRootShape s i ↔ HasIcosianRootShape r i := by
  obtain ⟨u,rfl⟩ := (icosianRootPoint_eq_iff r s).mp h
  simp only [HasIcosianRootShape,icosianRootNormWord_rightUnit]

def HasIcosianRootPointShape (p : IcosianRootPoint) (i : Fin 4) : Prop :=
  ∃ r : IcosianRoot,icosianRootPoint r=p.val ∧ HasIcosianRootShape r i

abbrev IcosianRootPointShape (i : Fin 4) := {p : IcosianRootPoint // HasIcosianRootPointShape p i}

def icosianRootShapeToPoint (i : Fin 4) (r : IcosianRootShapeFiber i) : IcosianRootPointShape i :=
  ⟨icosianRootToPoint r.val,r.val,rfl,r.property⟩

theorem icosianRootShapeToPoint_surjective (i : Fin 4) :
    Function.Surjective (icosianRootShapeToPoint i) := by
  rintro ⟨p,r,hr,hi⟩
  exact ⟨⟨r,hi⟩,Subtype.ext (Subtype.ext hr)⟩

def icosianRootShapePointFiberEquiv (i : Fin 4) (p : IcosianRootPointShape i) :
    {r : IcosianRootShapeFiber i // icosianRootShapeToPoint i r=p} ≃
      {r : IcosianRoot // icosianRootToPoint r=p.val} where
  toFun r := ⟨r.val.val,congrArg Subtype.val r.property⟩
  invFun r := by
    have hi : HasIcosianRootShape r.val i := by
      obtain ⟨s,hs,hi⟩ := p.property
      exact (icosianRootShape_of_same_point s r.val
        ((congrArg Subtype.val r.property).trans hs.symm) i).mpr hi
    exact ⟨⟨r.val,hi⟩,Subtype.ext r.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem icosianRootShapePointFiber_card (i : Fin 4) (p : IcosianRootPointShape i) :
    Nat.card {r : IcosianRootShapeFiber i // icosianRootShapeToPoint i r=p}=120 := by
  rw [Nat.card_congr (icosianRootShapePointFiberEquiv i p),icosianRootToPoint_fiber_card]

theorem icosianRootPointShape_card (i : Fin 4) :
    Nat.card (IcosianRootPointShape i)=![3,24,192,96] i := by
  let : Fintype (IcosianRootPointShape i) := Fintype.ofFinite _
  have he := Nat.card_congr (Equiv.sigmaPreimageEquiv (icosianRootShapeToPoint i))
  rw [Nat.card_sigma] at he
  change (∑ p : IcosianRootPointShape i,
    Nat.card {r : IcosianRootShapeFiber i // icosianRootShapeToPoint i r=p})=
      Nat.card (IcosianRootShapeFiber i) at he
  simp_rw [icosianRootShapePointFiber_card] at he
  rw [Finset.sum_const,Finset.card_univ,← Nat.card_eq_fintype_card,
    icosianRootShapeFiber_card] at he
  simp only [nsmul_eq_mul,Nat.cast_id] at he
  fin_cases i <;> dsimp at he ⊢ <;> omega

theorem icosianRootPointShape_unique (p : IcosianRootPoint) {i j : Fin 4}
    (hi : HasIcosianRootPointShape p i) (hj : HasIcosianRootPointShape p j) : i=j := by
  obtain ⟨r,hr,hi⟩ := hi
  obtain ⟨s,hs,hj⟩ := hj
  apply icosianRootShape_unique r hi
  exact (icosianRootShape_of_same_point r s (hs.trans hr.symm) j).mp hj

theorem icosianRootPointShape_exhaustive (p : IcosianRootPoint) :
    ∃ i,HasIcosianRootPointShape p i := by
  obtain ⟨r,hr⟩ := p.property
  obtain ⟨i,hi⟩ := icosianRootShape_exhaustive r
  exact ⟨i,r,hr,hi⟩

end Atlas.Conway
