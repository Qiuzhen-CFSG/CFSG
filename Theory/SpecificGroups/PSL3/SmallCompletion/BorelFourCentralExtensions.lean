module

public import Theory.SpecificGroups.PSL3.SmallCompletion.BorelFourCoordinates
public import Theory.SpecificGroups.PSL3.LinearThreeLocalAffine
public import Theory.Representation.SL2FourNaturalExtensions.CentralCocycle

/-!
# Central Frobenius correction on the literal line endpoint

The natural affine cocycle is transported through the existing exact
projective line-local equivalence. Its formulas retain the original
unitriangular embedding and the whole diagonal cubic torus.
-/

public noncomputable section
open Subgroup Matrix SemidirectProduct
open scoped MatrixGroups
namespace Matrix.PSL3.SmallCompletion
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.LinearAmbientGeometry Matrix.PSL3Even.UnipotentGeometry
open Representation.SL2FourNatural Representation.SL2FourNaturalExtensions

/-- Original unitriangular element regarded in the actual projective line endpoint. -/
@[expose] def lineUnipotent (u : U F) : lineLocal F :=
  lineLocalProjectEquiv F
    ⟨specialLinear F u,(mem_lineLocalSL_iff F _).mpr ⟨rfl,rfl,rfl⟩⟩

/-- The endpoint marking retains the original projective unipotent element. -/
theorem lineUnipotent_val (u : U F) :
    (lineUnipotent u : PSL(3,F)) = projective F u := rfl

/-- The full line endpoint automorphism realizing the first central shear. -/
@[expose] def lineCentralCorrection (k : F) : MulAut (lineLocal F) :=
  (MulAut.congr (lineLocalEquivAffine F).symm) (centralCorrection k)

private theorem line_coordinates (u : U F) :
    lineLocalEquivAffine F (lineUnipotent u) =
      ⟨Multiplicative.ofAdd ![u.c,u.y],upper u.x⟩ := by
  rw [lineUnipotent,lineLocalEquivAffine_project]
  rfl

/-- The restriction is the precise Frobenius shear in the original U coordinates. -/
theorem lineCentralCorrection_unipotent (k : F) (u : U F) :
    lineCentralCorrection k (lineUnipotent u) =
      lineUnipotent ⟨u.x,u.y,u.c+k*u.x^2⟩ := by
  apply (lineLocalEquivAffine F).injective
  change lineLocalEquivAffine F ((lineLocalEquivAffine F).symm
    (centralCorrection k (lineLocalEquivAffine F (lineUnipotent u)))) = _
  rw [MulEquiv.apply_symm_apply,line_coordinates,line_coordinates]
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    rw [centralCorrection_left]
    funext i
    fin_cases i <;> simp [rowProduct,upper,fieldFrobenius_apply]
  · rfl

private def lineDiagonalSL (t : Fˣ) : lineLocalSL F :=
  ⟨torusSL F (t^2,1),(mem_lineLocalSL_iff F _).mpr (by simp [torusSL_val])⟩

/-- The same full projective torus, regarded in the line endpoint. -/
@[expose] def lineTorus (t : Fˣ) : lineLocal F :=
  lineLocalProjectEquiv F
    ⟨torusSL F (t^2,1),(mem_lineLocalSL_iff F _).mpr (by simp [torusSL_val])⟩

/-- No torus element has been discarded during the endpoint transport. -/
theorem lineTorus_val (t : Fˣ) :
    (lineTorus t : PSL(3,F)) =
      (simultaneousTorus F t : PSL(3,F)) := by
  change torusMap F (t^2,1)=torusMap F (t,t⁻¹)
  apply mul_inv_eq_one.mp
  rw [←map_inv,←map_mul,BorelQuotient.torusMap_eq_one_iff]
  have ht : t^3=1 := by
    have hh := pow_card_eq_one' (x:=t)
    rw [Nat.card_units,Nat.card_eq_fintype_card,card_field] at hh
    exact hh
  constructor
  · simp [pow_two]
  · simpa [pow_two] using ht

/-- This actual endpoint automorphism fixes the full native cubic torus. -/
theorem lineCentralCorrection_torus (k : F) (t : Fˣ) :
    lineCentralCorrection k (lineTorus t) = lineTorus t := by
  change lineCentralCorrection k (lineLocalProjectEquiv F (lineDiagonalSL t)) =
    lineLocalProjectEquiv F (lineDiagonalSL t)
  apply (lineLocalEquivAffine F).injective
  change lineLocalEquivAffine F ((lineLocalEquivAffine F).symm
    (centralCorrection k (lineLocalEquivAffine F _))) = _
  rw [MulEquiv.apply_symm_apply,lineLocalEquivAffine_project]
  have hd : (lineLocalAffineEquiv F (lineDiagonalSL t)).left=1 := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  have hform : lineLocalAffineEquiv F (lineDiagonalSL t)=
      inr (lineLocalAffineEquiv F (lineDiagonalSL t)).right := by
    apply SemidirectProduct.ext
    · exact hd
    · rfl
  rw [hform]
  apply centralCorrection_diagonal
  · rfl
  · rfl

end Matrix.PSL3.SmallCompletion
