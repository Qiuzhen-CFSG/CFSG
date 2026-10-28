/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionUnipotent.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionDiagonal
public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionUnipotentData
public import Theory.AtlasPort.Janko2.Algebra.IcosianReductionConjugation

/-!
# IcosianReflectionUnipotent

Edge reflection words have explicit monomial forms whose reductions supply unipotent
parameters. Coordinate-axis checks and finite-field calculations prove the formulas.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionUnipotent.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes
open scoped Matrix Quaternion

def icosianReflectionEdgeWord (k : Fin 3) (p : Fin 2) : icosianHermitianGroup :=
  icosianReflectionEdgeGenerator k p * icosianReflectionEdgeGenerator 0 p

def icosianReflectionEdgeMonomial (k : Fin 3) (p : Fin 2) : IcosianUnitMonomial :=
  ⟨fun i => if i=0 then icosianReflectionEdgeUnit k
    else if i=icosianReflectionEdgePartner p then (icosianReflectionEdgeUnit k)⁻¹ else 1,1⟩

def icosianReflectionEdgeRaw (k : Fin 3) (p : Fin 2)
    (x : IcosianRationalCoordinates) : IcosianRationalCoordinates :=
  icosianReflection (icosianReflectionEdgeRoot k p)
    (icosianReflection (icosianReflectionEdgeRoot 0 p) x)

def icosianReflectionEdgeDiagonalRaw (k : Fin 3) (p : Fin 2)
    (x : IcosianRationalCoordinates) (i : Fin 3) : IcosianQuaternion :=
  if i=0 then (icosianReflectionEdgeUnitIntegral k).val*x i
  else if i=icosianReflectionEdgePartner p then star (icosianReflectionEdgeUnitIntegral k).val*x i
  else x i

theorem icosianReflectionEdgeGenerator_apply (k : Fin 3) (p : Fin 2)
    (x : IcosianRationalCoordinates) :
    (icosianReflectionEdgeGenerator k p).val x =
      icosianReflection (icosianReflectionEdgeRoot k p) x := rfl

theorem icosianReflectionEdgeWord_apply (k : Fin 3) (p : Fin 2)
    (x : IcosianRationalCoordinates) :
    (icosianReflectionEdgeWord k p).val x = icosianReflectionEdgeRaw k p x := by
  simp only [icosianReflectionEdgeWord,Subgroup.coe_mul,LinearEquiv.mul_apply,
    icosianReflectionEdgeGenerator_apply,icosianReflectionEdgeRaw]

theorem icosianReflectionEdgeUnit_value (k : Fin 3) :
    (icosianMonomialUnits (icosianReflectionEdgeUnit k) : IcosianQuaternion) =
      (icosianReflectionEdgeUnitIntegral k).val := rfl

theorem icosianReflectionUnit_inverse_value (u : icosianNormOneGroup) :
    (icosianMonomialUnits u⁻¹ : IcosianQuaternion) =
      star (icosianMonomialUnits u : IcosianQuaternion) := rfl

theorem icosianReflectionEdgePartner_ne_zero (p : Fin 2) :
    icosianReflectionEdgePartner p ≠ 0 := by fin_cases p <;> decide

theorem icosianReflectionEdgeMonomial_apply (k : Fin 3) (p : Fin 2)
    (x : IcosianRationalCoordinates) (i : Fin 3) :
    icosianMonomialRepresentation (icosianReflectionEdgeMonomial k p) x i =
      icosianReflectionEdgeDiagonalRaw k p x i := by
  rw [icosianReflectionMonomial_apply]
  have he : (1 : Equiv.Perm (Fin 3)).symm = Equiv.refl _ := rfl
  have hp0 := icosianReflectionEdgePartner_ne_zero p
  by_cases h0 : i=0
  · simp [icosianReflectionEdgeMonomial,icosianReflectionEdgeDiagonalRaw,he,h0,
      icosianReflectionEdgeUnit_value]
  · by_cases hp : i=icosianReflectionEdgePartner p
    · simp [icosianReflectionEdgeMonomial,icosianReflectionEdgeDiagonalRaw,he,hp0,hp,
        icosianReflectionUnit_inverse_value,icosianReflectionEdgeUnit_value]
    · simp [icosianReflectionEdgeMonomial,icosianReflectionEdgeDiagonalRaw,he,h0,hp,
        icosianMonomialUnits]

set_option maxHeartbeats 1000000 in
-- These are the 54 basis-coordinate checks for six two-reflection words.
theorem icosianReflectionEdgeRaw_axes :
    ∀ k p i j, icosianReflectionEdgeRaw k p (Pi.single i 1) j =
      icosianReflectionEdgeDiagonalRaw k p (Pi.single i 1) j := by
  intro k p i j
  fin_cases k <;> fin_cases p <;> fin_cases i <;> fin_cases j <;>
    apply QuaternionAlgebra.ext <;> decide +kernel

/-- Two actual root reflections supply paired quaternion units on either
coordinate pair. Their reductions give the two F2-basis unipotents. -/
theorem icosianReflectionEdgeWord_linear (k : Fin 3) (p : Fin 2) :
    (icosianReflectionEdgeWord k p).val =
      icosianMonomialRepresentation (icosianReflectionEdgeMonomial k p) := by
  apply icosian_right_linear_ext
  · exact (icosianReflectionEdgeWord k p).property.1
  · exact icosianMonomialRepresentation_right_linear _
  · intro i
    funext j
    rw [icosianReflectionEdgeWord_apply,icosianReflectionEdgeMonomial_apply]
    exact icosianReflectionEdgeRaw_axes k p i j

theorem icosianReflectionEdgeUnit_inverse_reduction (k : Fin 3) :
    icosianModuloTwo (icosianNormOneToOrder (icosianReflectionEdgeUnit k)⁻¹) =
      !![1,icosianReflectionEdgeParameter k;0,1] := by
  have he : icosianNormOneToOrder ((icosianReflectionEdgeUnit k)⁻¹) =
      icosianOrderStar (icosianReflectionEdgeUnitIntegral k) := by apply Subtype.ext; rfl
  rw [he,icosianModuloTwo_star,icosianReflectionEdgeUnit_reduction]
  fin_cases k <;> decide +kernel

theorem icosianReflectionMonomial_reduction_apply (g : IcosianUnitMonomial) (i : Fin 3) :
    ((icosianMonomialReduction g).left i).val =
      icosianModuloTwo (icosianNormOneToOrder (g.left i)) := rfl

theorem icosianReflectionEdgeMonomial_reduction (k : Fin 3) (p : Fin 2) (i : Fin 3) :
    ((icosianMonomialReduction (icosianReflectionEdgeMonomial k p)).left i).val =
      !![1, (if i=0 ∨ i=icosianReflectionEdgePartner p then icosianReflectionEdgeParameter k else 0);0,1] := by
  rw [icosianReflectionMonomial_reduction_apply]
  have hp0 := icosianReflectionEdgePartner_ne_zero p
  have hu : icosianNormOneToOrder (icosianReflectionEdgeUnit k) =
      icosianReflectionEdgeUnitIntegral k := by apply Subtype.ext; rfl
  by_cases h0 : i=0
  · simp only [icosianReflectionEdgeMonomial,h0,if_true,true_or,hu,
      icosianReflectionEdgeUnit_reduction]
  · by_cases hp : i=icosianReflectionEdgePartner p
    · simp [icosianReflectionEdgeMonomial,hp0,hp,
        icosianReflectionEdgeUnit_inverse_reduction]
    · simp [icosianReflectionEdgeMonomial,h0,hp]
      ext r j <;> fin_cases r <;> fin_cases j <;> rfl

theorem icosianReflectionEdgeParameters_span : ∀ t : GoldenFour,
    t=0 ∨ t=1 ∨ t=goldenFourTau+1 ∨ t=1+(goldenFourTau+1) := by decide +kernel

end Atlas.Conway

