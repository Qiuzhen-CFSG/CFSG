/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianRootPointNormWord.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointShapes

/-!
# IcosianRootPointNormWord

Right-unit invariance makes the coordinate norm word well-defined on root lines.
Constant scalar fibers relate root and point norm-level counts.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianRootPointNormWord.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped BigOperators

def icosianRootPointNormWord (p : IcosianRootPoint) : Fin 3 → GoldenInteger :=
  icosianRootNormWord p.property.choose

theorem icosianRootNormWord_of_same_point (r s : IcosianRoot)
    (h : icosianRootPoint s = icosianRootPoint r) :
    icosianRootNormWord s = icosianRootNormWord r := by
  obtain ⟨u, rfl⟩ := (icosianRootPoint_eq_iff r s).mp h
  funext i
  exact icosianRootNormWord_rightUnit r u i

theorem icosianRootPointNormWord_toPoint (r : IcosianRoot) :
    icosianRootPointNormWord (icosianRootToPoint r) = icosianRootNormWord r := by
  exact icosianRootNormWord_of_same_point r _ (icosianRootToPoint r).property.choose_spec

abbrev IcosianRootNormLevel (i : Fin 3) (a : GoldenInteger) :=
  {r : IcosianRoot // icosianRootNormWord r i = a}

abbrev IcosianRootPointNormLevel (i : Fin 3) (a : GoldenInteger) :=
  {p : IcosianRootPoint // icosianRootPointNormWord p i = a}

def icosianRootNormLevelToPoint (i : Fin 3) (a : GoldenInteger)
    (r : IcosianRootNormLevel i a) : IcosianRootPointNormLevel i a :=
  ⟨icosianRootToPoint r.val, by rw [icosianRootPointNormWord_toPoint]; exact r.property⟩

def icosianRootNormLevelPointFiberEquiv (i : Fin 3) (a : GoldenInteger)
    (p : IcosianRootPointNormLevel i a) :
    {r : IcosianRootNormLevel i a // icosianRootNormLevelToPoint i a r = p} ≃
      {r : IcosianRoot // icosianRootToPoint r = p.val} where
  toFun r := ⟨r.val.val, congrArg Subtype.val r.property⟩
  invFun r := by
    have hr : icosianRootNormWord r.val i = a := by
      rw [← icosianRootPointNormWord_toPoint, r.property]
      exact p.property
    exact ⟨⟨r.val, hr⟩, Subtype.ext r.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem icosianRootNormLevelPointFiber_card (i : Fin 3) (a : GoldenInteger)
    (p : IcosianRootPointNormLevel i a) :
    Nat.card {r : IcosianRootNormLevel i a // icosianRootNormLevelToPoint i a r = p} = 120 := by
  rw [Nat.card_congr (icosianRootNormLevelPointFiberEquiv i a p), icosianRootToPoint_fiber_card]

theorem icosianRootPointNormLevel_card_mul (i : Fin 3) (a : GoldenInteger) :
    Nat.card (IcosianRootPointNormLevel i a) * 120 = Nat.card (IcosianRootNormLevel i a) := by
  let : Fintype (IcosianRootPointNormLevel i a) := Fintype.ofFinite _
  have he := Nat.card_congr (Equiv.sigmaPreimageEquiv (icosianRootNormLevelToPoint i a))
  rw [Nat.card_sigma] at he
  change (∑ p : IcosianRootPointNormLevel i a,
    Nat.card {r : IcosianRootNormLevel i a // icosianRootNormLevelToPoint i a r = p}) =
      Nat.card (IcosianRootNormLevel i a) at he
  simp_rw [icosianRootNormLevelPointFiber_card] at he
  simpa only [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    nsmul_eq_mul, Nat.cast_id] using he

end Atlas.Conway
