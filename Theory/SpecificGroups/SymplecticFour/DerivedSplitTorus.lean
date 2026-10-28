module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Torus
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.CharP.Two
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The full split torus in the derived symplectic Borel

The symplectic Weyl matrix inverts both diagonal coordinates. Every unit
is a square in a finite field of characteristic two, so the commutator
identity places the full two-parameter torus in the literal derived group.
Its two first diagonal entries prove faithfulness in the derived Borel.

Source: the standard symplectic diagonal and Weyl matrices; used for the
rank-two exclusion in Aschbacher--Smith 9.2.7, pp.731--732.
-/

public noncomputable section
open Matrix Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.DerivedSplitTorus
variable {F : Type*} [Field F]

private abbrev tor := CentralRootGeometry.diagonalTorusHom (F := F)

private theorem weyl_intertwine (a : Fˣ × Fˣ) :
    SymplecticGroup.symJ (Fin 2) F * tor a = tor a⁻¹ * SymplecticGroup.symJ (Fin 2) F := by
  apply Subtype.ext
  change J _ _ * diagonal _ = diagonal _ * J _ _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.J, Matrix.fromBlocks]

private theorem tor_square_commutator (a : Fˣ × Fˣ) :
    ⁅tor a, SymplecticGroup.symJ (Fin 2) F⁆ = tor (a * a) := by
  calc
    ⁅tor a, SymplecticGroup.symJ (Fin 2) F⁆ =
        tor a * (SymplecticGroup.symJ (Fin 2) F * tor a⁻¹) *
          (SymplecticGroup.symJ (Fin 2) F)⁻¹ := by
      simp only [commutatorElement_def, map_inv, mul_assoc]
    _ = tor a * (tor a * SymplecticGroup.symJ (Fin 2) F) *
          (SymplecticGroup.symJ (Fin 2) F)⁻¹ := by rw [weyl_intertwine, inv_inv]
    _ = tor (a * a) := by simp [map_mul, mul_assoc]

/-- Both diagonal coordinates lie in the literal derived symplectic group. -/
theorem diagonal_mem_derived [Finite F] [CharP F 2] (a b : Fˣ) :
    diagonalTorus a b ∈ commutator (Sp F) := by
  have hs (a : Fˣ) : ∃ u : Fˣ, a = u*u := by
    obtain ⟨v,hv⟩ := isSquare_of_charTwo' (a : F)
    have hv0 : v ≠ 0 := by intro h; simp [h] at hv
    exact ⟨Units.mk0 v hv0,Units.ext hv⟩
  obtain ⟨v,hv⟩ := hs a
  obtain ⟨w,hw⟩ := hs b
  have h : (a,b) = (v,w)*(v,w) := Prod.ext hv hw
  change tor (a,b) ∈ commutator (Sp F)
  rw [h,←tor_square_commutator]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The full split torus embeds into the actual derived-group flag Borel. -/
def embedding [Finite F] [CharP F 2] :
    (Fˣ × Fˣ) →* (borel (F := F)).subgroupOf (commutator (Sp F)) :=
  ((CentralRootGeometry.diagonalTorusHom (F := F)).codRestrict _
    (fun x => diagonal_mem_derived x.1 x.2)).codRestrict _
    (fun x => diagonalTorus_mem_borel x.1 x.2)

theorem embedding_injective [Finite F] [CharP F 2] :
    Function.Injective (embedding (F := F)) := by
  intro a b h
  apply Prod.ext
  · apply Units.ext
    exact congrArg (fun x : (borel (F := F)).subgroupOf (commutator (Sp F)) =>
      x.val.val.val (.inl 0) (.inl 0)) h
  · apply Units.ext
    exact congrArg (fun x : (borel (F := F)).subgroupOf (commutator (Sp F)) =>
      x.val.val.val (.inl 1) (.inl 1)) h
end Theory.SpecificGroups.SymplecticFour.DerivedSplitTorus
