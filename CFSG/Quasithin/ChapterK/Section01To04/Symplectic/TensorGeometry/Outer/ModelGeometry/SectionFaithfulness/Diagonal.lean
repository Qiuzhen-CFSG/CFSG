module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.ModelGeometry.Sections

/-!
# Diagonal coordinates on the actual Hermitian middle section

The diagonal map sends a transpose-fixed Hermitian matrix to its four
base-field diagonal entries. It is surjective. Displacements have zero
diagonal; the known dimensions 10 and 6 identify its kernel with the
literal displacement comap. The induced equivalence therefore uses the
published fixed/displacement quotient, with its quotient-map equation.

Source: Aschbacher–Smith, K.3.4.2, printed pp.456–457, following the
field-section calculation of H.4.4(6), printed p.381.
-/

@[expose] public section

open Matrix Representation
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model.Geometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  (σ : F ≃ₐ[k] F) (hσ : Function.Involutive σ)
  [FiniteDimensional k F] (hdeg : Module.finrank k F = 2) (hne : σ ≠ AlgEquiv.refl)

local instance : AddCommGroup (Space σ hσ) := inferInstance
local instance : AddCommGroup (fieldFixed σ hσ) := inferInstance

/-- Diagonal coordinates in the base field. -/
def diagonalMap : fieldFixed σ hσ →ₗ[k] Vector k where
  toFun X i := (coefficientEquiv σ hdeg hne).symm ((fixedCoordinates σ hσ X).1 i)
  map_add' X Y := by
    ext i
    rw [map_add]
    exact map_add (coefficientEquiv σ hdeg hne).symm _ _
  map_smul' c X := by
    ext i
    rw [map_smul]
    exact map_smul (coefficientEquiv σ hdeg hne).symm c _

lemma diagonalMap_entry (X : fieldFixed σ hσ) (i : Index) :
    algebraMap k F (diagonalMap σ hσ hdeg hne X i) = X.val.val i i := by
  exact congrArg Subtype.val ((coefficientEquiv σ hdeg hne).apply_symm_apply _)

lemma diagonalMap_surjective : Function.Surjective (diagonalMap σ hσ hdeg hne) := by
  intro v
  refine ⟨(fixedCoordinates σ hσ).symm (fun i => coefficientEquiv σ hdeg hne (v i), 0), ?_⟩
  have he := (fixedCoordinates σ hσ).apply_symm_apply
    (fun i => coefficientEquiv σ hdeg hne (v i), 0)
  ext i
  have hi := congrArg (fun z : (Index → fixedCoefficients σ) × (Upper → fixedCoefficients σ) =>
    z.1 i) he
  change (coefficientEquiv σ hdeg hne).symm _ = v i
  rw [show _ = coefficientEquiv σ hdeg hne (v i) from hi]
  exact (coefficientEquiv σ hdeg hne).symm_apply_apply _

lemma mem_ker_diagonalMap (X : fieldFixed σ hσ) :
    X ∈ LinearMap.ker (diagonalMap σ hσ hdeg hne) ↔ ∀ i, X.val.val i i = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h i
    rw [← diagonalMap_entry σ hσ hdeg hne X i, h]
    exact map_zero _
  · intro h
    ext i
    apply (algebraMap k F).injective
    rw [diagonalMap_entry, h, Pi.zero_apply, map_zero]

lemma ker_diagonalMap [CharP F 2] :
    LinearMap.ker (diagonalMap σ hσ hdeg hne) = movedInFixed σ hσ := by
  have hle : movedInFixed σ hσ ≤ LinearMap.ker (diagonalMap σ hσ hdeg hne) := by
    intro X hX
    exact (mem_ker_diagonalMap σ hσ hdeg hne X).mpr
      (fun i => moved_diagonal_zero σ hσ ⟨X.val, hX⟩ i)
  symm
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have hd := (diagonalMap σ hσ hdeg hne).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (diagonalMap_surjective σ hσ hdeg hne),
    finrank_fieldFixed σ hσ hdeg hne] at hd
  have he := (Submodule.comapSubtypeEquivOfLe (fieldMoved_le_fieldFixed σ hσ)).finrank_eq
  change Module.finrank k (movedInFixed σ hσ) = Module.finrank k (fieldMoved σ hσ) at he
  rw [he, finrank_fieldMoved σ hσ hdeg hne]
  have hv : Module.finrank k (⊤ : Submodule k (Vector k)) = 4 := by
    simp [Theory.SpecificGroups.SymplecticFour.Vector]
  rw [hv] at hd
  omega

/-- The diagonal map on the literal fixed/displacement quotient. -/
def middleDiagonal [CharP F 2] : Middle σ hσ →ₗ[k] Vector k :=
  (movedInFixed σ hσ).liftQ (diagonalMap σ hσ hdeg hne)
    (le_of_eq (ker_diagonalMap σ hσ hdeg hne).symm)

lemma middleDiagonal_mk [CharP F 2] (X : fieldFixed σ hσ) :
    middleDiagonal σ hσ hdeg hne ((movedInFixed σ hσ).mkQ X) =
      diagonalMap σ hσ hdeg hne X := rfl

/-- The natural four coordinates on the literal middle quotient. -/
def middleEquiv [CharP F 2] : Middle σ hσ ≃ₗ[k] Vector k :=
  LinearEquiv.ofBijective (middleDiagonal σ hσ hdeg hne) (by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply le_antisymm _ bot_le
      intro X hX
      induction X using Submodule.Quotient.induction_on with
      | _ X =>
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        rw [← ker_diagonalMap σ hσ hdeg hne]
        exact hX
    · intro v
      obtain ⟨X, hX⟩ := diagonalMap_surjective σ hσ hdeg hne v
      exact ⟨(movedInFixed σ hσ).mkQ X, hX⟩)

lemma middleEquiv_mk [CharP F 2] (X : fieldFixed σ hσ) :
    middleEquiv σ hσ hdeg hne ((movedInFixed σ hσ).mkQ X) =
      diagonalMap σ hσ hdeg hne X := rfl
end
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model.Geometry
