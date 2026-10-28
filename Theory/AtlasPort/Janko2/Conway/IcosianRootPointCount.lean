/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianRootPointCount.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootLines

/-!
# IcosianRootPointCount

The root-to-point map has 120-element fibers. Its sigma decomposition turns the root
count into the conditional 315-point count.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianRootPointCount.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Lattices

/-- The root-to-line map has the actual geometric range as codomain. -/
def icosianRootToPoint (r : IcosianRoot) : IcosianRootPoint :=
  ⟨icosianRootPoint r,r,rfl⟩

theorem icosianRootToPoint_surjective : Function.Surjective icosianRootToPoint := by
  rintro ⟨p,r,hr⟩
  exact ⟨r,Subtype.ext hr⟩

def icosianRootPointFiberEquiv (p : IcosianRootPoint) (r : IcosianRoot)
    (hr : icosianRootPoint r=p.val) :
    {s : IcosianRoot // icosianRootToPoint s=p} ≃
      {s : IcosianRoot // icosianRootPoint s=icosianRootPoint r} where
  toFun s := ⟨s.val,(congrArg Subtype.val s.property).trans hr.symm⟩
  invFun s := ⟨s.val,Subtype.ext (s.property.trans hr)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem icosianRootToPoint_fiber_card (p : IcosianRootPoint) :
    Nat.card {s : IcosianRoot // icosianRootToPoint s=p}=120 := by
  obtain ⟨r,hr⟩ := p.property
  rw [Nat.card_congr (icosianRootPointFiberEquiv p r hr),icosianRootLineFiber_card]

/-- Root-line counting from the structural root count and proved scalar saturation. -/
theorem icosianRootPoint_card_of_root_card (h : Nat.card IcosianRoot=37800) :
    Nat.card IcosianRootPoint=315 := by
  let : Finite IcosianRoot := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  let : Finite IcosianRootPoint := Finite.of_surjective _ icosianRootToPoint_surjective
  let : Fintype IcosianRootPoint := Fintype.ofFinite _
  have he := Nat.card_congr (Equiv.sigmaPreimageEquiv icosianRootToPoint)
  rw [Nat.card_sigma] at he
  change (∑ p : IcosianRootPoint, Nat.card {s : IcosianRoot // icosianRootToPoint s=p})=Nat.card IcosianRoot at he
  simp_rw [icosianRootToPoint_fiber_card] at he
  rw [Finset.sum_const,Finset.card_univ,← Nat.card_eq_fintype_card,h] at he
  simp only [nsmul_eq_mul,Nat.cast_id] at he
  omega

end Atlas.Conway
