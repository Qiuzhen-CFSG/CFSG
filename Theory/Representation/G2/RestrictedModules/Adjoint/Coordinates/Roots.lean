module

public import Theory.Representation.G2.RestrictedModules.Adjoint.Coordinates.Reconstruction

/-!
# The six root families on the actual adjoint coordinates

We evaluate conjugation by each Wilson root map and its inverse at the fourteen
matrix entries defining the coordinates. Each scalar identity is a small
polynomial calculation over an arbitrary field of characteristic two. The final
formulas concern the transported action of the actual octonion automorphism
model, with no comparison to a separately generated matrix group.

Source: GLS3, Example 2.8.10(g); Wilson's root maps are the attributed ATLAS
ports in `Theory.AtlasPort.LinearGroups.G2.RootLinearMaps`.
-/

-- As in reconstruction, keep independent coordinate checks within one worker.

set_option Elab.async false
@[expose] public section
namespace Atlas.G2.Restricted.Adjoint.Coordinates
open Atlas.SplitOctonion
variable (F : Type*) [Field F] [CharP F 2]

-- Every scalar check uses the same polynomial normalization; some coordinates
-- close at simplification, others require characteristic-two coefficient reduction.
local macro "root_coordinate" : tactic =>
  `(tactic| (simp [Explicit.rootAApply, Explicit.rootBApply, Explicit.rootCApply,
    Explicit.rootDApply, Explicit.rootEApply, Explicit.rootFApply,
    endomorphism, basisVector, sub_eq_add_neg, CharTwo.neg_eq]
    <;> ring_nf <;> simp [CharTwo.ofNat_eq_mod]))

private theorem rootA_coord_0 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootA a) (fromParams F r)) 0 = r 0 + a*r 6 + a^2*r 8 + a*r 13 := by
  change Explicit.rootAApply a
    (endomorphism r (Explicit.rootAApply (-a) (basisVector 7))) 1 = _
  root_coordinate

private theorem rootA_coord_1 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootA a) (fromParams F r)) 1 = r 1 + a*r 5 := by
  change Explicit.rootAApply a
    (endomorphism r (Explicit.rootAApply (-a) (basisVector 7))) 2 = _
  root_coordinate

private theorem rootA_coord_2 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootA a) (fromParams F r)) 2 = r 2 + a*r 11 := by
  change Explicit.rootAApply a
    (endomorphism r (Explicit.rootAApply (-a) (basisVector 7))) 4 = _
  root_coordinate

private theorem rootA_coord_3 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootA a) (fromParams F r)) 3 = r 3 + a*r 9 := by
  change Explicit.rootAApply a
    (endomorphism r (Explicit.rootAApply (-a) (basisVector 6))) 5 = _
  root_coordinate

private theorem rootA_coord_4 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootA a) (fromParams F r)) 4 = r 4 + a*r 10 := by
  change Explicit.rootAApply a
    (endomorphism r (Explicit.rootAApply (-a) (basisVector 7))) 5 = _
  root_coordinate

private theorem rootA_coord_5 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootA a) (fromParams F r)) 5 = r 5 := by
  change Explicit.rootAApply a
    (endomorphism r (Explicit.rootAApply (-a) (basisVector 5))) 6 = _
  root_coordinate

private theorem rootA_coord_6 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootA a) (fromParams F r)) 6 = r 6 + a*r 8 := by
  change Explicit.rootAApply a
    (endomorphism r (Explicit.rootAApply (-a) (basisVector 6))) 6 = _
  root_coordinate

private theorem rootA_coord_7 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootA a) (fromParams F r)) 7 = r 7 := by
  change Explicit.rootAApply a
    (endomorphism r (Explicit.rootAApply (-a) (basisVector 7))) 6 = _
  root_coordinate

private theorem rootA_coord_8 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootA a) (fromParams F r)) 8 = r 8 := by
  change Explicit.rootAApply a
    (endomorphism r (Explicit.rootAApply (-a) (basisVector 1))) 7 = _
  root_coordinate

private theorem rootA_coord_9 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootA a) (fromParams F r)) 9 = r 9 := by
  change Explicit.rootAApply a
    (endomorphism r (Explicit.rootAApply (-a) (basisVector 2))) 7 = _
  root_coordinate

private theorem rootA_coord_10 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootA a) (fromParams F r)) 10 = r 10 := by
  change Explicit.rootAApply a
    (endomorphism r (Explicit.rootAApply (-a) (basisVector 4))) 7 = _
  root_coordinate

private theorem rootA_coord_11 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootA a) (fromParams F r)) 11 = r 11 := by
  change Explicit.rootAApply a
    (endomorphism r (Explicit.rootAApply (-a) (basisVector 5))) 7 = _
  root_coordinate

private theorem rootA_coord_12 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootA a) (fromParams F r)) 12 = r 12 := by
  change Explicit.rootAApply a
    (endomorphism r (Explicit.rootAApply (-a) (basisVector 6))) 7 = _
  root_coordinate

private theorem rootA_coord_13 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootA a) (fromParams F r)) 13 = a*r 8 + r 13 := by
  change Explicit.rootAApply a
    (endomorphism r (Explicit.rootAApply (-a) (basisVector 7))) 7 = _
  root_coordinate

/-- Wilson root A, at every field parameter, acts by actual conjugation. -/
@[simp] theorem action_rootA (a : F) (r : Space F) :
    action F (rootA a) r = ![
      r 0 + a*r 6 + a^2*r 8 + a*r 13,
      r 1 + a*r 5,
      r 2 + a*r 11,
      r 3 + a*r 9,
      r 4 + a*r 10,
      r 5,
      r 6 + a*r 8,
      r 7,
      r 8,
      r 9,
      r 10,
      r 11,
      r 12,
      a*r 8 + r 13] := by
  rw [action_apply]
  ext i
  fin_cases i
  · exact rootA_coord_0 F a r
  · exact rootA_coord_1 F a r
  · exact rootA_coord_2 F a r
  · exact rootA_coord_3 F a r
  · exact rootA_coord_4 F a r
  · exact rootA_coord_5 F a r
  · exact rootA_coord_6 F a r
  · exact rootA_coord_7 F a r
  · exact rootA_coord_8 F a r
  · exact rootA_coord_9 F a r
  · exact rootA_coord_10 F a r
  · exact rootA_coord_11 F a r
  · exact rootA_coord_12 F a r
  · exact rootA_coord_13 F a r

private theorem rootB_coord_0 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootB a) (fromParams F r)) 0 = r 0 + a*r 3 := by
  change Explicit.rootBApply a
    (endomorphism r (Explicit.rootBApply (-a) (basisVector 7))) 1 = _
  root_coordinate

private theorem rootB_coord_1 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootB a) (fromParams F r)) 1 = r 1 + a*r 6 + a^2*r 9 := by
  change Explicit.rootBApply a
    (endomorphism r (Explicit.rootBApply (-a) (basisVector 7))) 2 = _
  root_coordinate

private theorem rootB_coord_2 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootB a) (fromParams F r)) 2 = r 2 + a*r 12 := by
  change Explicit.rootBApply a
    (endomorphism r (Explicit.rootBApply (-a) (basisVector 7))) 4 = _
  root_coordinate

private theorem rootB_coord_3 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootB a) (fromParams F r)) 3 = r 3 := by
  change Explicit.rootBApply a
    (endomorphism r (Explicit.rootBApply (-a) (basisVector 6))) 5 = _
  root_coordinate

private theorem rootB_coord_4 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootB a) (fromParams F r)) 4 = r 4 := by
  change Explicit.rootBApply a
    (endomorphism r (Explicit.rootBApply (-a) (basisVector 7))) 5 = _
  root_coordinate

private theorem rootB_coord_5 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootB a) (fromParams F r)) 5 = r 5 + a*r 8 := by
  change Explicit.rootBApply a
    (endomorphism r (Explicit.rootBApply (-a) (basisVector 5))) 6 = _
  root_coordinate

private theorem rootB_coord_6 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootB a) (fromParams F r)) 6 = r 6 := by
  change Explicit.rootBApply a
    (endomorphism r (Explicit.rootBApply (-a) (basisVector 6))) 6 = _
  root_coordinate

private theorem rootB_coord_7 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootB a) (fromParams F r)) 7 = r 7 + a*r 10 := by
  change Explicit.rootBApply a
    (endomorphism r (Explicit.rootBApply (-a) (basisVector 7))) 6 = _
  root_coordinate

private theorem rootB_coord_8 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootB a) (fromParams F r)) 8 = r 8 := by
  change Explicit.rootBApply a
    (endomorphism r (Explicit.rootBApply (-a) (basisVector 1))) 7 = _
  root_coordinate

private theorem rootB_coord_9 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootB a) (fromParams F r)) 9 = r 9 := by
  change Explicit.rootBApply a
    (endomorphism r (Explicit.rootBApply (-a) (basisVector 2))) 7 = _
  root_coordinate

private theorem rootB_coord_10 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootB a) (fromParams F r)) 10 = r 10 := by
  change Explicit.rootBApply a
    (endomorphism r (Explicit.rootBApply (-a) (basisVector 4))) 7 = _
  root_coordinate

private theorem rootB_coord_11 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootB a) (fromParams F r)) 11 = r 11 := by
  change Explicit.rootBApply a
    (endomorphism r (Explicit.rootBApply (-a) (basisVector 5))) 7 = _
  root_coordinate

private theorem rootB_coord_12 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootB a) (fromParams F r)) 12 = r 12 := by
  change Explicit.rootBApply a
    (endomorphism r (Explicit.rootBApply (-a) (basisVector 6))) 7 = _
  root_coordinate

private theorem rootB_coord_13 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootB a) (fromParams F r)) 13 = a*r 9 + r 13 := by
  change Explicit.rootBApply a
    (endomorphism r (Explicit.rootBApply (-a) (basisVector 7))) 7 = _
  root_coordinate

/-- Wilson root B, at every field parameter, acts by actual conjugation. -/
@[simp] theorem action_rootB (a : F) (r : Space F) :
    action F (rootB a) r = ![
      r 0 + a*r 3,
      r 1 + a*r 6 + a^2*r 9,
      r 2 + a*r 12,
      r 3,
      r 4,
      r 5 + a*r 8,
      r 6,
      r 7 + a*r 10,
      r 8,
      r 9,
      r 10,
      r 11,
      r 12,
      a*r 9 + r 13] := by
  rw [action_apply]
  ext i
  fin_cases i
  · exact rootB_coord_0 F a r
  · exact rootB_coord_1 F a r
  · exact rootB_coord_2 F a r
  · exact rootB_coord_3 F a r
  · exact rootB_coord_4 F a r
  · exact rootB_coord_5 F a r
  · exact rootB_coord_6 F a r
  · exact rootB_coord_7 F a r
  · exact rootB_coord_8 F a r
  · exact rootB_coord_9 F a r
  · exact rootB_coord_10 F a r
  · exact rootB_coord_11 F a r
  · exact rootB_coord_12 F a r
  · exact rootB_coord_13 F a r

private theorem rootC_coord_0 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootC a) (fromParams F r)) 0 = r 0 + a*r 4 + a^3*r 9 + a^2*r 12 := by
  change Explicit.rootCApply a
    (endomorphism r (Explicit.rootCApply (-a) (basisVector 7))) 1 = _
  root_coordinate

private theorem rootC_coord_1 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootC a) (fromParams F r)) 1 = r 1 + a*r 7 + a^3*r 8 + a^2*r 11 := by
  change Explicit.rootCApply a
    (endomorphism r (Explicit.rootCApply (-a) (basisVector 7))) 2 = _
  root_coordinate

private theorem rootC_coord_2 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootC a) (fromParams F r)) 2 = r 2 + a^2*r 10 + a*r 13 := by
  change Explicit.rootCApply a
    (endomorphism r (Explicit.rootCApply (-a) (basisVector 7))) 4 = _
  root_coordinate

private theorem rootC_coord_3 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootC a) (fromParams F r)) 3 = r 3 := by
  change Explicit.rootCApply a
    (endomorphism r (Explicit.rootCApply (-a) (basisVector 6))) 5 = _
  root_coordinate

private theorem rootC_coord_4 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootC a) (fromParams F r)) 4 = r 4 + a^2*r 9 := by
  change Explicit.rootCApply a
    (endomorphism r (Explicit.rootCApply (-a) (basisVector 7))) 5 = _
  root_coordinate

private theorem rootC_coord_5 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootC a) (fromParams F r)) 5 = r 5 := by
  change Explicit.rootCApply a
    (endomorphism r (Explicit.rootCApply (-a) (basisVector 5))) 6 = _
  root_coordinate

private theorem rootC_coord_6 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootC a) (fromParams F r)) 6 = r 6 + a*r 10 := by
  change Explicit.rootCApply a
    (endomorphism r (Explicit.rootCApply (-a) (basisVector 6))) 6 = _
  root_coordinate

private theorem rootC_coord_7 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootC a) (fromParams F r)) 7 = r 7 + a^2*r 8 := by
  change Explicit.rootCApply a
    (endomorphism r (Explicit.rootCApply (-a) (basisVector 7))) 6 = _
  root_coordinate

private theorem rootC_coord_8 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootC a) (fromParams F r)) 8 = r 8 := by
  change Explicit.rootCApply a
    (endomorphism r (Explicit.rootCApply (-a) (basisVector 1))) 7 = _
  root_coordinate

private theorem rootC_coord_9 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootC a) (fromParams F r)) 9 = r 9 := by
  change Explicit.rootCApply a
    (endomorphism r (Explicit.rootCApply (-a) (basisVector 2))) 7 = _
  root_coordinate

private theorem rootC_coord_10 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootC a) (fromParams F r)) 10 = r 10 := by
  change Explicit.rootCApply a
    (endomorphism r (Explicit.rootCApply (-a) (basisVector 4))) 7 = _
  root_coordinate

private theorem rootC_coord_11 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootC a) (fromParams F r)) 11 = a*r 8 + r 11 := by
  change Explicit.rootCApply a
    (endomorphism r (Explicit.rootCApply (-a) (basisVector 5))) 7 = _
  root_coordinate

private theorem rootC_coord_12 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootC a) (fromParams F r)) 12 = a*r 9 + r 12 := by
  change Explicit.rootCApply a
    (endomorphism r (Explicit.rootCApply (-a) (basisVector 6))) 7 = _
  root_coordinate

private theorem rootC_coord_13 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootC a) (fromParams F r)) 13 = r 13 := by
  change Explicit.rootCApply a
    (endomorphism r (Explicit.rootCApply (-a) (basisVector 7))) 7 = _
  root_coordinate

/-- Wilson root C, at every field parameter, acts by actual conjugation. -/
@[simp] theorem action_rootC (a : F) (r : Space F) :
    action F (rootC a) r = ![
      r 0 + a*r 4 + a^3*r 9 + a^2*r 12,
      r 1 + a*r 7 + a^3*r 8 + a^2*r 11,
      r 2 + a^2*r 10 + a*r 13,
      r 3,
      r 4 + a^2*r 9,
      r 5,
      r 6 + a*r 10,
      r 7 + a^2*r 8,
      r 8,
      r 9,
      r 10,
      a*r 8 + r 11,
      a*r 9 + r 12,
      r 13] := by
  rw [action_apply]
  ext i
  fin_cases i
  · exact rootC_coord_0 F a r
  · exact rootC_coord_1 F a r
  · exact rootC_coord_2 F a r
  · exact rootC_coord_3 F a r
  · exact rootC_coord_4 F a r
  · exact rootC_coord_5 F a r
  · exact rootC_coord_6 F a r
  · exact rootC_coord_7 F a r
  · exact rootC_coord_8 F a r
  · exact rootC_coord_9 F a r
  · exact rootC_coord_10 F a r
  · exact rootC_coord_11 F a r
  · exact rootC_coord_12 F a r
  · exact rootC_coord_13 F a r

private theorem rootD_coord_0 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootD a) (fromParams F r)) 0 = r 0 + a*r 2 + a^3*r 5 + a^2*r 7 := by
  change Explicit.rootDApply a
    (endomorphism r (Explicit.rootDApply (-a) (basisVector 7))) 1 = _
  root_coordinate

private theorem rootD_coord_1 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootD a) (fromParams F r)) 1 = r 1 := by
  change Explicit.rootDApply a
    (endomorphism r (Explicit.rootDApply (-a) (basisVector 7))) 2 = _
  root_coordinate

private theorem rootD_coord_2 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootD a) (fromParams F r)) 2 = r 2 + a^2*r 5 := by
  change Explicit.rootDApply a
    (endomorphism r (Explicit.rootDApply (-a) (basisVector 7))) 4 = _
  root_coordinate

private theorem rootD_coord_3 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootD a) (fromParams F r)) 3 = r 3 + a^3*r 8 + a^2*r 10 + a*r 12 := by
  change Explicit.rootDApply a
    (endomorphism r (Explicit.rootDApply (-a) (basisVector 6))) 5 = _
  root_coordinate

private theorem rootD_coord_4 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootD a) (fromParams F r)) 4 = r 4 + a*r 6 + a^2*r 11 := by
  change Explicit.rootDApply a
    (endomorphism r (Explicit.rootDApply (-a) (basisVector 7))) 5 = _
  root_coordinate

private theorem rootD_coord_5 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootD a) (fromParams F r)) 5 = r 5 := by
  change Explicit.rootDApply a
    (endomorphism r (Explicit.rootDApply (-a) (basisVector 5))) 6 = _
  root_coordinate

private theorem rootD_coord_6 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootD a) (fromParams F r)) 6 = r 6 := by
  change Explicit.rootDApply a
    (endomorphism r (Explicit.rootDApply (-a) (basisVector 6))) 6 = _
  root_coordinate

private theorem rootD_coord_7 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootD a) (fromParams F r)) 7 = a*r 5 + r 7 := by
  change Explicit.rootDApply a
    (endomorphism r (Explicit.rootDApply (-a) (basisVector 7))) 6 = _
  root_coordinate

private theorem rootD_coord_8 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootD a) (fromParams F r)) 8 = r 8 := by
  change Explicit.rootDApply a
    (endomorphism r (Explicit.rootDApply (-a) (basisVector 1))) 7 = _
  root_coordinate

private theorem rootD_coord_9 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootD a) (fromParams F r)) 9 = r 9 := by
  change Explicit.rootDApply a
    (endomorphism r (Explicit.rootDApply (-a) (basisVector 2))) 7 = _
  root_coordinate

private theorem rootD_coord_10 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootD a) (fromParams F r)) 10 = a*r 8 + r 10 := by
  change Explicit.rootDApply a
    (endomorphism r (Explicit.rootDApply (-a) (basisVector 4))) 7 = _
  root_coordinate

private theorem rootD_coord_11 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootD a) (fromParams F r)) 11 = r 11 := by
  change Explicit.rootDApply a
    (endomorphism r (Explicit.rootDApply (-a) (basisVector 5))) 7 = _
  root_coordinate

private theorem rootD_coord_12 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootD a) (fromParams F r)) 12 = a^2*r 8 + r 12 := by
  change Explicit.rootDApply a
    (endomorphism r (Explicit.rootDApply (-a) (basisVector 6))) 7 = _
  root_coordinate

private theorem rootD_coord_13 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootD a) (fromParams F r)) 13 = a*r 11 + r 13 := by
  change Explicit.rootDApply a
    (endomorphism r (Explicit.rootDApply (-a) (basisVector 7))) 7 = _
  root_coordinate

/-- Wilson root D, at every field parameter, acts by actual conjugation. -/
@[simp] theorem action_rootD (a : F) (r : Space F) :
    action F (rootD a) r = ![
      r 0 + a*r 2 + a^3*r 5 + a^2*r 7,
      r 1,
      r 2 + a^2*r 5,
      r 3 + a^3*r 8 + a^2*r 10 + a*r 12,
      r 4 + a*r 6 + a^2*r 11,
      r 5,
      r 6,
      a*r 5 + r 7,
      r 8,
      r 9,
      a*r 8 + r 10,
      r 11,
      a^2*r 8 + r 12,
      a*r 11 + r 13] := by
  rw [action_apply]
  ext i
  fin_cases i
  · exact rootD_coord_0 F a r
  · exact rootD_coord_1 F a r
  · exact rootD_coord_2 F a r
  · exact rootD_coord_3 F a r
  · exact rootD_coord_4 F a r
  · exact rootD_coord_5 F a r
  · exact rootD_coord_6 F a r
  · exact rootD_coord_7 F a r
  · exact rootD_coord_8 F a r
  · exact rootD_coord_9 F a r
  · exact rootD_coord_10 F a r
  · exact rootD_coord_11 F a r
  · exact rootD_coord_12 F a r
  · exact rootD_coord_13 F a r

private theorem rootE_coord_0 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootE a) (fromParams F r)) 0 = r 0 + a*r 1 := by
  change Explicit.rootEApply a
    (endomorphism r (Explicit.rootEApply (-a) (basisVector 7))) 1 = _
  root_coordinate

private theorem rootE_coord_1 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootE a) (fromParams F r)) 1 = r 1 := by
  change Explicit.rootEApply a
    (endomorphism r (Explicit.rootEApply (-a) (basisVector 7))) 2 = _
  root_coordinate

private theorem rootE_coord_2 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootE a) (fromParams F r)) 2 = r 2 := by
  change Explicit.rootEApply a
    (endomorphism r (Explicit.rootEApply (-a) (basisVector 7))) 4 = _
  root_coordinate

private theorem rootE_coord_3 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootE a) (fromParams F r)) 3 = r 3 + a^2*r 5 + a*r 13 := by
  change Explicit.rootEApply a
    (endomorphism r (Explicit.rootEApply (-a) (basisVector 6))) 5 = _
  root_coordinate

private theorem rootE_coord_4 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootE a) (fromParams F r)) 4 = r 4 + a*r 7 := by
  change Explicit.rootEApply a
    (endomorphism r (Explicit.rootEApply (-a) (basisVector 7))) 5 = _
  root_coordinate

private theorem rootE_coord_5 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootE a) (fromParams F r)) 5 = r 5 := by
  change Explicit.rootEApply a
    (endomorphism r (Explicit.rootEApply (-a) (basisVector 5))) 6 = _
  root_coordinate

private theorem rootE_coord_6 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootE a) (fromParams F r)) 6 = a*r 5 + r 6 := by
  change Explicit.rootEApply a
    (endomorphism r (Explicit.rootEApply (-a) (basisVector 6))) 6 = _
  root_coordinate

private theorem rootE_coord_7 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootE a) (fromParams F r)) 7 = r 7 := by
  change Explicit.rootEApply a
    (endomorphism r (Explicit.rootEApply (-a) (basisVector 7))) 6 = _
  root_coordinate

private theorem rootE_coord_8 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootE a) (fromParams F r)) 8 = r 8 := by
  change Explicit.rootEApply a
    (endomorphism r (Explicit.rootEApply (-a) (basisVector 1))) 7 = _
  root_coordinate

private theorem rootE_coord_9 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootE a) (fromParams F r)) 9 = a*r 8 + r 9 := by
  change Explicit.rootEApply a
    (endomorphism r (Explicit.rootEApply (-a) (basisVector 2))) 7 = _
  root_coordinate

private theorem rootE_coord_10 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootE a) (fromParams F r)) 10 = r 10 := by
  change Explicit.rootEApply a
    (endomorphism r (Explicit.rootEApply (-a) (basisVector 4))) 7 = _
  root_coordinate

private theorem rootE_coord_11 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootE a) (fromParams F r)) 11 = r 11 := by
  change Explicit.rootEApply a
    (endomorphism r (Explicit.rootEApply (-a) (basisVector 5))) 7 = _
  root_coordinate

private theorem rootE_coord_12 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootE a) (fromParams F r)) 12 = a*r 11 + r 12 := by
  change Explicit.rootEApply a
    (endomorphism r (Explicit.rootEApply (-a) (basisVector 6))) 7 = _
  root_coordinate

private theorem rootE_coord_13 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootE a) (fromParams F r)) 13 = r 13 := by
  change Explicit.rootEApply a
    (endomorphism r (Explicit.rootEApply (-a) (basisVector 7))) 7 = _
  root_coordinate

/-- Wilson root E, at every field parameter, acts by actual conjugation. -/
@[simp] theorem action_rootE (a : F) (r : Space F) :
    action F (rootE a) r = ![
      r 0 + a*r 1,
      r 1,
      r 2,
      r 3 + a^2*r 5 + a*r 13,
      r 4 + a*r 7,
      r 5,
      a*r 5 + r 6,
      r 7,
      r 8,
      a*r 8 + r 9,
      r 10,
      r 11,
      a*r 11 + r 12,
      r 13] := by
  rw [action_apply]
  ext i
  fin_cases i
  · exact rootE_coord_0 F a r
  · exact rootE_coord_1 F a r
  · exact rootE_coord_2 F a r
  · exact rootE_coord_3 F a r
  · exact rootE_coord_4 F a r
  · exact rootE_coord_5 F a r
  · exact rootE_coord_6 F a r
  · exact rootE_coord_7 F a r
  · exact rootE_coord_8 F a r
  · exact rootE_coord_9 F a r
  · exact rootE_coord_10 F a r
  · exact rootE_coord_11 F a r
  · exact rootE_coord_12 F a r
  · exact rootE_coord_13 F a r

private theorem rootF_coord_0 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootF a) (fromParams F r)) 0 = r 0 := by
  change Explicit.rootFApply a
    (endomorphism r (Explicit.rootFApply (-a) (basisVector 7))) 1 = _
  root_coordinate

private theorem rootF_coord_1 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootF a) (fromParams F r)) 1 = r 1 + a*r 2 + a^3*r 3 + a^2*r 4 := by
  change Explicit.rootFApply a
    (endomorphism r (Explicit.rootFApply (-a) (basisVector 7))) 2 = _
  root_coordinate

private theorem rootF_coord_2 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootF a) (fromParams F r)) 2 = r 2 + a^2*r 3 := by
  change Explicit.rootFApply a
    (endomorphism r (Explicit.rootFApply (-a) (basisVector 7))) 4 = _
  root_coordinate

private theorem rootF_coord_3 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootF a) (fromParams F r)) 3 = r 3 := by
  change Explicit.rootFApply a
    (endomorphism r (Explicit.rootFApply (-a) (basisVector 6))) 5 = _
  root_coordinate

private theorem rootF_coord_4 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootF a) (fromParams F r)) 4 = a*r 3 + r 4 := by
  change Explicit.rootFApply a
    (endomorphism r (Explicit.rootFApply (-a) (basisVector 7))) 5 = _
  root_coordinate

private theorem rootF_coord_5 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootF a) (fromParams F r)) 5 = r 5 + a^3*r 9 + a^2*r 10 + a*r 11 := by
  change Explicit.rootFApply a
    (endomorphism r (Explicit.rootFApply (-a) (basisVector 5))) 6 = _
  root_coordinate

private theorem rootF_coord_6 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootF a) (fromParams F r)) 6 = r 6 + a*r 12 := by
  change Explicit.rootFApply a
    (endomorphism r (Explicit.rootFApply (-a) (basisVector 6))) 6 = _
  root_coordinate

private theorem rootF_coord_7 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootF a) (fromParams F r)) 7 = a*r 6 + r 7 + a^2*r 12 + a*r 13 := by
  change Explicit.rootFApply a
    (endomorphism r (Explicit.rootFApply (-a) (basisVector 7))) 6 = _
  root_coordinate

private theorem rootF_coord_8 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootF a) (fromParams F r)) 8 = r 8 := by
  change Explicit.rootFApply a
    (endomorphism r (Explicit.rootFApply (-a) (basisVector 1))) 7 = _
  root_coordinate

private theorem rootF_coord_9 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootF a) (fromParams F r)) 9 = r 9 := by
  change Explicit.rootFApply a
    (endomorphism r (Explicit.rootFApply (-a) (basisVector 2))) 7 = _
  root_coordinate

private theorem rootF_coord_10 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootF a) (fromParams F r)) 10 = a*r 9 + r 10 := by
  change Explicit.rootFApply a
    (endomorphism r (Explicit.rootFApply (-a) (basisVector 4))) 7 = _
  root_coordinate

private theorem rootF_coord_11 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootF a) (fromParams F r)) 11 = a^2*r 9 + r 11 := by
  change Explicit.rootFApply a
    (endomorphism r (Explicit.rootFApply (-a) (basisVector 5))) 7 = _
  root_coordinate

private theorem rootF_coord_12 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootF a) (fromParams F r)) 12 = r 12 := by
  change Explicit.rootFApply a
    (endomorphism r (Explicit.rootFApply (-a) (basisVector 6))) 7 = _
  root_coordinate

private theorem rootF_coord_13 (a : F) (r : Space F) :
    params F (Adjoint.action F (rootF a) (fromParams F r)) 13 = a*r 12 + r 13 := by
  change Explicit.rootFApply a
    (endomorphism r (Explicit.rootFApply (-a) (basisVector 7))) 7 = _
  root_coordinate

/-- Wilson root F, at every field parameter, acts by actual conjugation. -/
@[simp] theorem action_rootF (a : F) (r : Space F) :
    action F (rootF a) r = ![
      r 0,
      r 1 + a*r 2 + a^3*r 3 + a^2*r 4,
      r 2 + a^2*r 3,
      r 3,
      a*r 3 + r 4,
      r 5 + a^3*r 9 + a^2*r 10 + a*r 11,
      r 6 + a*r 12,
      a*r 6 + r 7 + a^2*r 12 + a*r 13,
      r 8,
      r 9,
      a*r 9 + r 10,
      a^2*r 9 + r 11,
      r 12,
      a*r 12 + r 13] := by
  rw [action_apply]
  ext i
  fin_cases i
  · exact rootF_coord_0 F a r
  · exact rootF_coord_1 F a r
  · exact rootF_coord_2 F a r
  · exact rootF_coord_3 F a r
  · exact rootF_coord_4 F a r
  · exact rootF_coord_5 F a r
  · exact rootF_coord_6 F a r
  · exact rootF_coord_7 F a r
  · exact rootF_coord_8 F a r
  · exact rootF_coord_9 F a r
  · exact rootF_coord_10 F a r
  · exact rootF_coord_11 F a r
  · exact rootF_coord_12 F a r
  · exact rootF_coord_13 F a r

end Atlas.G2.Restricted.Adjoint.Coordinates
