/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeFiberTransport

/-!
# HexacodeKernelTransitivity

The local hexacode kernel is transitive on nonzero words vanishing at its fixed
coordinate. Each such word has a unique second zero; coordinate transport matches that
zero, and fiber transitivity matches the word.

Source: `Atlas/Codes/HexacodeKernelTransitivity.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

/-- The actual A5 kernel acts transitively on all fifteen nonzero kernel words. -/
theorem hexPointKernel_nonzero_transitive (i : HexIndex) (u v : hexZeroCoordinate i)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : hexPointKernel i, hexZeroLinear i g.val u = v := by
  obtain ⟨j,⟨hji,hj⟩,_⟩ := hexZeroCoordinate_unique_other_zero i u hu
  obtain ⟨k,⟨hki,hk⟩,_⟩ := hexZeroCoordinate_unique_other_zero i v hv
  obtain ⟨g,hg⟩ := hexPointKernel_transitive_complement i j k hji hki
  let u1 := hexZeroLinear i g.val u
  have hu1 : u1 ≠ 0 := fun h => hu ((hexZeroLinear i g.val).map_eq_zero_iff.mp h)
  have hperm : g.val.val.val.perm j = k := hg
  have hu1k : u1.val.val k = 0 := by
    change g.val.val.val.localMap k (u.val.val (g.val.val.val.perm.symm k)) = 0
    rw [← hperm,Equiv.symm_apply_apply,hj,map_zero]
  let U : hexDoubleZero i k := ⟨u1.val,u1.prop,hu1k⟩
  let V : hexDoubleZero i k := ⟨v.val,v.prop,hk⟩
  have hU : U ≠ 0 := fun h => hu1 (Subtype.ext (congrArg (fun w : hexDoubleZero i k => w.val) h))
  have hV : V ≠ 0 := fun h => hv (Subtype.ext (congrArg (fun w : hexDoubleZero i k => w.val) h))
  obtain ⟨r,_,hr⟩ := hex_fiber_transitive i k hki.symm U V hU hV
  refine ⟨r*g,?_⟩
  apply Subtype.ext
  change hexAction (r.val.val*g.val.val) u.val = v.val
  rw [map_mul]
  exact hr

end Atlas.Codes
