module

public import Theory.Representation.G2.RestrictedModules.Adjoint.Coordinates.Reconstruction

/-!
# Weyl maps and torus weights on the actual adjoint module

Conjugating the reconstructed derivations by the two octonion Weyl maps gives
explicit coordinate permutations, with the necessary change on the diagonal
parameters. Conjugation by the actual split torus is diagonal; its characters
are the ratios of the octonion weights at the fourteen selected matrix entries.
All formulas are over an arbitrary field of characteristic two.

Source: GLS3, Example 2.8.10(g); the Weyl and torus maps are the attributed ATLAS
ports in `Theory.AtlasPort.LinearGroups.G2.WeylMaps` and `Torus`.
-/


set_option Elab.async false
@[expose] public section
namespace Atlas.G2.Restricted.Adjoint.Coordinates
open Atlas.SplitOctonion
variable (F : Type*) [Field F] [CharP F 2]

local macro "weyl_coordinate" : tactic =>
  `(tactic| simp [weylRApply, weylSApply, endomorphism, basisVector, CharTwo.neg_eq])

private theorem weylR_coord_0 (r : Space F) :
    params F (Adjoint.action F weylR (fromParams F r)) 0 = r 1 := by
  change weylRApply (endomorphism r (weylRApply (basisVector 7))) 1 = _
  weyl_coordinate

private theorem weylR_coord_1 (r : Space F) :
    params F (Adjoint.action F weylR (fromParams F r)) 1 = r 0 := by
  change weylRApply (endomorphism r (weylRApply (basisVector 7))) 2 = _
  weyl_coordinate

private theorem weylR_coord_2 (r : Space F) :
    params F (Adjoint.action F weylR (fromParams F r)) 2 = r 2 := by
  change weylRApply (endomorphism r (weylRApply (basisVector 7))) 4 = _
  weyl_coordinate

private theorem weylR_coord_3 (r : Space F) :
    params F (Adjoint.action F weylR (fromParams F r)) 3 = r 5 := by
  change weylRApply (endomorphism r (weylRApply (basisVector 6))) 5 = _
  weyl_coordinate

private theorem weylR_coord_4 (r : Space F) :
    params F (Adjoint.action F weylR (fromParams F r)) 4 = r 7 := by
  change weylRApply (endomorphism r (weylRApply (basisVector 7))) 5 = _
  weyl_coordinate

private theorem weylR_coord_5 (r : Space F) :
    params F (Adjoint.action F weylR (fromParams F r)) 5 = r 3 := by
  change weylRApply (endomorphism r (weylRApply (basisVector 5))) 6 = _
  weyl_coordinate

private theorem weylR_coord_6 (r : Space F) :
    params F (Adjoint.action F weylR (fromParams F r)) 6 = r 6 + r 13 := by
  change weylRApply (endomorphism r (weylRApply (basisVector 6))) 6 = _
  weyl_coordinate

private theorem weylR_coord_7 (r : Space F) :
    params F (Adjoint.action F weylR (fromParams F r)) 7 = r 4 := by
  change weylRApply (endomorphism r (weylRApply (basisVector 7))) 6 = _
  weyl_coordinate

private theorem weylR_coord_8 (r : Space F) :
    params F (Adjoint.action F weylR (fromParams F r)) 8 = r 9 := by
  change weylRApply (endomorphism r (weylRApply (basisVector 1))) 7 = _
  weyl_coordinate

private theorem weylR_coord_9 (r : Space F) :
    params F (Adjoint.action F weylR (fromParams F r)) 9 = r 8 := by
  change weylRApply (endomorphism r (weylRApply (basisVector 2))) 7 = _
  weyl_coordinate

private theorem weylR_coord_10 (r : Space F) :
    params F (Adjoint.action F weylR (fromParams F r)) 10 = r 10 := by
  change weylRApply (endomorphism r (weylRApply (basisVector 4))) 7 = _
  weyl_coordinate

private theorem weylR_coord_11 (r : Space F) :
    params F (Adjoint.action F weylR (fromParams F r)) 11 = r 12 := by
  change weylRApply (endomorphism r (weylRApply (basisVector 5))) 7 = _
  weyl_coordinate

private theorem weylR_coord_12 (r : Space F) :
    params F (Adjoint.action F weylR (fromParams F r)) 12 = r 11 := by
  change weylRApply (endomorphism r (weylRApply (basisVector 6))) 7 = _
  weyl_coordinate

private theorem weylR_coord_13 (r : Space F) :
    params F (Adjoint.action F weylR (fromParams F r)) 13 = r 13 := by
  change weylRApply (endomorphism r (weylRApply (basisVector 7))) 7 = _
  weyl_coordinate

/-- The actual Weyl map R on adjoint coordinates. -/
@[simp] theorem action_weylR (r : Space F) :
    action F weylR r = ![r 1, r 0, r 2, r 5, r 7, r 3, r 6 + r 13, r 4, r 9, r 8, r 10, r 12, r 11, r 13] := by
  rw [action_apply]
  ext i
  fin_cases i
  · exact weylR_coord_0 F r
  · exact weylR_coord_1 F r
  · exact weylR_coord_2 F r
  · exact weylR_coord_3 F r
  · exact weylR_coord_4 F r
  · exact weylR_coord_5 F r
  · exact weylR_coord_6 F r
  · exact weylR_coord_7 F r
  · exact weylR_coord_8 F r
  · exact weylR_coord_9 F r
  · exact weylR_coord_10 F r
  · exact weylR_coord_11 F r
  · exact weylR_coord_12 F r
  · exact weylR_coord_13 F r

private theorem weylS_coord_0 (r : Space F) :
    params F (Adjoint.action F weylS (fromParams F r)) 0 = r 0 := by
  change weylSApply (endomorphism r (weylSApply (basisVector 7))) 1 = _
  weyl_coordinate

private theorem weylS_coord_1 (r : Space F) :
    params F (Adjoint.action F weylS (fromParams F r)) 1 = r 3 := by
  change weylSApply (endomorphism r (weylSApply (basisVector 7))) 2 = _
  weyl_coordinate

private theorem weylS_coord_2 (r : Space F) :
    params F (Adjoint.action F weylS (fromParams F r)) 2 = r 4 := by
  change weylSApply (endomorphism r (weylSApply (basisVector 7))) 4 = _
  weyl_coordinate

private theorem weylS_coord_3 (r : Space F) :
    params F (Adjoint.action F weylS (fromParams F r)) 3 = r 1 := by
  change weylSApply (endomorphism r (weylSApply (basisVector 6))) 5 = _
  weyl_coordinate

private theorem weylS_coord_4 (r : Space F) :
    params F (Adjoint.action F weylS (fromParams F r)) 4 = r 2 := by
  change weylSApply (endomorphism r (weylSApply (basisVector 7))) 5 = _
  weyl_coordinate

private theorem weylS_coord_5 (r : Space F) :
    params F (Adjoint.action F weylS (fromParams F r)) 5 = r 9 := by
  change weylSApply (endomorphism r (weylSApply (basisVector 5))) 6 = _
  weyl_coordinate

private theorem weylS_coord_6 (r : Space F) :
    params F (Adjoint.action F weylS (fromParams F r)) 6 = r 13 := by
  change weylSApply (endomorphism r (weylSApply (basisVector 6))) 6 = _
  weyl_coordinate

private theorem weylS_coord_7 (r : Space F) :
    params F (Adjoint.action F weylS (fromParams F r)) 7 = r 12 := by
  change weylSApply (endomorphism r (weylSApply (basisVector 7))) 6 = _
  weyl_coordinate

private theorem weylS_coord_8 (r : Space F) :
    params F (Adjoint.action F weylS (fromParams F r)) 8 = r 8 := by
  change weylSApply (endomorphism r (weylSApply (basisVector 1))) 7 = _
  weyl_coordinate

private theorem weylS_coord_9 (r : Space F) :
    params F (Adjoint.action F weylS (fromParams F r)) 9 = r 5 := by
  change weylSApply (endomorphism r (weylSApply (basisVector 2))) 7 = _
  weyl_coordinate

private theorem weylS_coord_10 (r : Space F) :
    params F (Adjoint.action F weylS (fromParams F r)) 10 = r 11 := by
  change weylSApply (endomorphism r (weylSApply (basisVector 4))) 7 = _
  weyl_coordinate

private theorem weylS_coord_11 (r : Space F) :
    params F (Adjoint.action F weylS (fromParams F r)) 11 = r 10 := by
  change weylSApply (endomorphism r (weylSApply (basisVector 5))) 7 = _
  weyl_coordinate

private theorem weylS_coord_12 (r : Space F) :
    params F (Adjoint.action F weylS (fromParams F r)) 12 = r 7 := by
  change weylSApply (endomorphism r (weylSApply (basisVector 6))) 7 = _
  weyl_coordinate

private theorem weylS_coord_13 (r : Space F) :
    params F (Adjoint.action F weylS (fromParams F r)) 13 = r 6 := by
  change weylSApply (endomorphism r (weylSApply (basisVector 7))) 7 = _
  weyl_coordinate

/-- The actual Weyl map S on adjoint coordinates. -/
@[simp] theorem action_weylS (r : Space F) :
    action F weylS r = ![r 0, r 3, r 4, r 1, r 2, r 9, r 13, r 12, r 8, r 5, r 11, r 10, r 7, r 6] := by
  rw [action_apply]
  ext i
  fin_cases i
  · exact weylS_coord_0 F r
  · exact weylS_coord_1 F r
  · exact weylS_coord_2 F r
  · exact weylS_coord_3 F r
  · exact weylS_coord_4 F r
  · exact weylS_coord_5 F r
  · exact weylS_coord_6 F r
  · exact weylS_coord_7 F r
  · exact weylS_coord_8 F r
  · exact weylS_coord_9 F r
  · exact weylS_coord_10 F r
  · exact weylS_coord_11 F r
  · exact weylS_coord_12 F r
  · exact weylS_coord_13 F r

/-- The fourteen characters of the split torus, in the prescribed order. -/
def torusWeights (l m : Fˣ) : Fin 14 → Fˣ :=
  ![l*m, l^2/m, l, m^2/l, m, l/m^2, 1, l/m,
    1/(l*m), m/l^2, 1/l, 1/m, m/l, 1]

local macro "torus_coordinate" : tactic =>
  `(tactic| (simp [torusEquiv, torusLinear, Atlas.G2.torusWeights, torusWeights,
    endomorphism, basisVector] <;> field_simp <;> ring))

private theorem torus_coord_0 (l m : Fˣ) (r : Space F) :
    params F (Adjoint.action F (torus l m) (fromParams F r)) 0 =
      (torusWeights F l m 0 : F) * r 0 := by
  change (torusEquiv l m)
    (endomorphism r ((torusEquiv l m).symm (basisVector 7))) 1 = _
  torus_coordinate

private theorem torus_coord_1 (l m : Fˣ) (r : Space F) :
    params F (Adjoint.action F (torus l m) (fromParams F r)) 1 =
      (torusWeights F l m 1 : F) * r 1 := by
  change (torusEquiv l m)
    (endomorphism r ((torusEquiv l m).symm (basisVector 7))) 2 = _
  torus_coordinate

private theorem torus_coord_2 (l m : Fˣ) (r : Space F) :
    params F (Adjoint.action F (torus l m) (fromParams F r)) 2 =
      (torusWeights F l m 2 : F) * r 2 := by
  change (torusEquiv l m)
    (endomorphism r ((torusEquiv l m).symm (basisVector 7))) 4 = _
  torus_coordinate

private theorem torus_coord_3 (l m : Fˣ) (r : Space F) :
    params F (Adjoint.action F (torus l m) (fromParams F r)) 3 =
      (torusWeights F l m 3 : F) * r 3 := by
  change (torusEquiv l m)
    (endomorphism r ((torusEquiv l m).symm (basisVector 6))) 5 = _
  torus_coordinate

private theorem torus_coord_4 (l m : Fˣ) (r : Space F) :
    params F (Adjoint.action F (torus l m) (fromParams F r)) 4 =
      (torusWeights F l m 4 : F) * r 4 := by
  change (torusEquiv l m)
    (endomorphism r ((torusEquiv l m).symm (basisVector 7))) 5 = _
  torus_coordinate

private theorem torus_coord_5 (l m : Fˣ) (r : Space F) :
    params F (Adjoint.action F (torus l m) (fromParams F r)) 5 =
      (torusWeights F l m 5 : F) * r 5 := by
  change (torusEquiv l m)
    (endomorphism r ((torusEquiv l m).symm (basisVector 5))) 6 = _
  torus_coordinate

private theorem torus_coord_6 (l m : Fˣ) (r : Space F) :
    params F (Adjoint.action F (torus l m) (fromParams F r)) 6 =
      (torusWeights F l m 6 : F) * r 6 := by
  change (torusEquiv l m)
    (endomorphism r ((torusEquiv l m).symm (basisVector 6))) 6 = _
  torus_coordinate

private theorem torus_coord_7 (l m : Fˣ) (r : Space F) :
    params F (Adjoint.action F (torus l m) (fromParams F r)) 7 =
      (torusWeights F l m 7 : F) * r 7 := by
  change (torusEquiv l m)
    (endomorphism r ((torusEquiv l m).symm (basisVector 7))) 6 = _
  torus_coordinate

private theorem torus_coord_8 (l m : Fˣ) (r : Space F) :
    params F (Adjoint.action F (torus l m) (fromParams F r)) 8 =
      (torusWeights F l m 8 : F) * r 8 := by
  change (torusEquiv l m)
    (endomorphism r ((torusEquiv l m).symm (basisVector 1))) 7 = _
  torus_coordinate

private theorem torus_coord_9 (l m : Fˣ) (r : Space F) :
    params F (Adjoint.action F (torus l m) (fromParams F r)) 9 =
      (torusWeights F l m 9 : F) * r 9 := by
  change (torusEquiv l m)
    (endomorphism r ((torusEquiv l m).symm (basisVector 2))) 7 = _
  torus_coordinate

private theorem torus_coord_10 (l m : Fˣ) (r : Space F) :
    params F (Adjoint.action F (torus l m) (fromParams F r)) 10 =
      (torusWeights F l m 10 : F) * r 10 := by
  change (torusEquiv l m)
    (endomorphism r ((torusEquiv l m).symm (basisVector 4))) 7 = _
  torus_coordinate

private theorem torus_coord_11 (l m : Fˣ) (r : Space F) :
    params F (Adjoint.action F (torus l m) (fromParams F r)) 11 =
      (torusWeights F l m 11 : F) * r 11 := by
  change (torusEquiv l m)
    (endomorphism r ((torusEquiv l m).symm (basisVector 5))) 7 = _
  torus_coordinate

private theorem torus_coord_12 (l m : Fˣ) (r : Space F) :
    params F (Adjoint.action F (torus l m) (fromParams F r)) 12 =
      (torusWeights F l m 12 : F) * r 12 := by
  change (torusEquiv l m)
    (endomorphism r ((torusEquiv l m).symm (basisVector 6))) 7 = _
  torus_coordinate

private theorem torus_coord_13 (l m : Fˣ) (r : Space F) :
    params F (Adjoint.action F (torus l m) (fromParams F r)) 13 =
      (torusWeights F l m 13 : F) * r 13 := by
  change (torusEquiv l m)
    (endomorphism r ((torusEquiv l m).symm (basisVector 7))) 7 = _
  torus_coordinate

/-- The actual torus conjugation is diagonal with these fourteen weights. -/
@[simp] theorem action_torus (l m : Fˣ) (r : Space F) :
    action F (torus l m) r =
      fun i => (torusWeights F l m i : F) * r i := by
  rw [action_apply]
  ext i
  fin_cases i
  · exact torus_coord_0 F l m r
  · exact torus_coord_1 F l m r
  · exact torus_coord_2 F l m r
  · exact torus_coord_3 F l m r
  · exact torus_coord_4 F l m r
  · exact torus_coord_5 F l m r
  · exact torus_coord_6 F l m r
  · exact torus_coord_7 F l m r
  · exact torus_coord_8 F l m r
  · exact torus_coord_9 F l m r
  · exact torus_coord_10 F l m r
  · exact torus_coord_11 F l m r
  · exact torus_coord_12 F l m r
  · exact torus_coord_13 F l m r

end Atlas.G2.Restricted.Adjoint.Coordinates
