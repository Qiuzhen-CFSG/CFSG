/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianProjectiveKernel.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianLineReflectionAction
public import Theory.AtlasPort.Janko2.Conway.IcosianProjectiveAxisRigidity
public import Theory.AtlasPort.Janko2.Conway.IcosianAxisRootGeometry
public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionSwaps
public import Theory.AtlasPort.Janko2.Conway.IcosianAxisReflections

/-!
# IcosianProjectiveKernel

A map fixing every root point is a common scalar by coordinate swaps. Commutation
with the explicit i and j reflection words forces that scalar to be a real sign.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianProjectiveKernel.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianReflectionEdgeUnit_I :
    (icosianReflectionEdgeUnitIntegral 1).val = -icosianI := by
  apply QuaternionAlgebra.ext <;> decide +kernel

theorem icosianReflectionEdgeUnit_J :
    (icosianReflectionEdgeUnitIntegral 2).val = icosianJ := by
  apply QuaternionAlgebra.ext <;> decide +kernel

/-- The projective kernel is forced to be a common quaternion scalar by the two
coordinate swaps, and then a real sign by the paired i and j words. -/
theorem icosian_fix_rootPoints_eq_sign (g : icosianHermitianGroup)
    (hg : ∀ p : IcosianRootPoint, g • p = p) : g=1 ∨ g=icosianCentralSign := by
  have haxes : ∀ i, g • icosianAxisPoint i=icosianAxisPoint i := by
    intro i
    have h := congrArg Subtype.val (hg (icosianRootAxisPoint i))
    change g • (icosianRootAxisPoint i).val=(icosianRootAxisPoint i).val at h
    simpa only [icosianRootAxisPoint_val] using h
  obtain ⟨q,hq,happly⟩ := icosian_diagonal_of_fix_axes g haxes
  have hc := icosian_fix_rootPoints_commutes_reflections g hg
  have heq (p : Fin 2) : q 0=q (icosianReflectionEdgePartner p) := by
    have h := hc (icosianReflectionEdgeGenerator 0 p) (icosianReflectionEdgeGenerator_mem 0 p)
    have he := congrArg
      (fun f : icosianHermitianGroup => f.val
        (Pi.single (icosianReflectionEdgePartner p) 1 : IcosianRationalCoordinates) 0) h
    change g.val ((icosianReflectionEdgeGenerator 0 p).val _) 0 =
      (icosianReflectionEdgeGenerator 0 p).val (g.val _) 0 at he
    rw [icosianReflectionSwap_linear] at he
    simp only [icosianReflectionSwapMonomial_apply,happly] at he
    simpa [Equiv.swap_apply_left,icosianReflectionEdgePartner_ne_zero] using he
  have hcommon : ∀ i, q i=q 0 := by
    intro i
    fin_cases i
    · rfl
    · exact (heq 0).symm
    · exact (heq 1).symm
  have hu (k : Fin 3) : q 0*(icosianReflectionEdgeUnitIntegral k).val =
      (icosianReflectionEdgeUnitIntegral k).val*q 0 := by
    have h := hc (icosianReflectionEdgeWord k 0) (icosianReflectionEdgeWord_mem_reflections k 0)
    have he := congrArg
      (fun f : icosianHermitianGroup => f.val (Pi.single 0 1 : IcosianRationalCoordinates) 0) h
    change g.val ((icosianReflectionEdgeWord k 0).val _) 0 =
      (icosianReflectionEdgeWord k 0).val (g.val _) 0 at he
    rw [icosianReflectionEdgeWord_linear] at he
    simp only [icosianReflectionEdgeMonomial_apply,happly,icosianReflectionEdgeDiagonalRaw,
      Pi.single_eq_same,mul_one] at he
    exact he
  have hi : q 0*icosianI=icosianI*q 0 := by
    have h := hu 1
    rw [icosianReflectionEdgeUnit_I] at h
    simpa only [mul_neg,neg_mul,neg_inj] using h
  have hj : q 0*icosianJ=icosianJ*q 0 := by
    simpa only [icosianReflectionEdgeUnit_J] using hu 2
  rcases icosian_norm_one_commutes_I_J (q 0) (hq 0).2 hi hj with hs | hs
  · left
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    funext i
    change g.val x i=x i
    rw [happly,hcommon,hs,one_mul]
  · right
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    funext i
    rw [icosianCentralSign_apply]
    change g.val x i= -x i
    rw [happly,hcommon,hs,neg_one_mul]

end Atlas.Conway
