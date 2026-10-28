module

public import Theory.SpecificGroups.HaradaNorton.Simplicity.Reduction
public import Theory.SpecificGroups.HaradaNorton.Simplicity.Center.CyclicRows
public import Theory.SpecificGroups.HaradaNorton.Simplicity.Center.FirstRow
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Centerlessness from the commutant of the fixed HN matrices

Perfectness makes the determinant of every element one. A scalar matrix in
dimension 133 over GF(5) with determinant one is the identity, since 133 is
coprime to four. Thus a scalar joint commutant of the two generators implies
centerlessness. The certified cyclic-row argument further reduces the concrete
commutant calculation to its zeroth row.

The first-row rigidity certificate completes this calculation, giving trivial
center under perfectness. Neither absolute irreducibility nor simplicity of
the ATLAS group is assumed.
Source of the matrices: `../MatrixSources.md`.
-/

namespace HaradaNorton

set_option maxRecDepth 10000

/-- Perfectness annihilates the determinant character of the fixed matrix group. -/
public theorem det_matrixHom_eq_one_of_isPerfect [Group.IsPerfect HN] (g : HN) :
    (matrixHom g).det = 1 := by
  let f : HN →* (ZMod 5)ˣ := (Matrix.detMonoidHom.comp matrixHom).toHomUnits
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have h : (⟨f g, g, rfl⟩ : f.range) = 1 := Subsingleton.elim _ _
  have hf := congrArg (fun x : f.range => x.val) h
  have hv := congrArg (fun u : (ZMod 5)ˣ => (u : ZMod 5)) hf
  simpa only [f, MonoidHom.coe_toHomUnits, MonoidHom.comp_apply,
    Matrix.coe_detMonoidHom, OneMemClass.coe_one, Units.val_one] using hv

private theorem scalar_eq_one_of_pow_133_eq_one (c : ZMod 5) (h : c ^ 133 = 1) :
    c = 1 := by
  have hf : ∀ c : ZMod 5, c ^ 133 = 1 → c = 1 := by decide +kernel
  exact hf c h

/-- The only scalar matrix in the perfect HN matrix group is the identity. -/
public theorem eq_one_of_matrixHom_scalar [Group.IsPerfect HN]
    (g : HN) (c : ZMod 5) (hc : matrixHom g = c • (1 : Matrix133)) : g = 1 := by
  have hp : c ^ 133 = 1 := by
    simpa [hc, Matrix.det_smul] using det_matrixHom_eq_one_of_isPerfect g
  apply matrixHom_injective
  simpa [scalar_eq_one_of_pow_133_eq_one c hp] using hc

/-- A scalar joint commutant suffices for centerlessness under perfectness. -/
public theorem center_eq_bot_of_scalar_commutant [Group.IsPerfect HN]
    (hscalar : ∀ M : Matrix133, M * aMatrix = aMatrix * M →
      M * bMatrix = bMatrix * M → ∃ c : ZMod 5, M = c • (1 : Matrix133)) :
    Subgroup.center HN = ⊥ := by
  apply bot_unique
  intro g hg
  change g = 1
  have hcomm (x : HN) : matrixHom g * matrixHom x = matrixHom x * matrixHom g := by
    simpa only [map_mul] using congrArg matrixHom (Subgroup.mem_center_iff.mp hg x).symm
  obtain ⟨c, hc⟩ := hscalar (matrixHom g) (by simpa using hcomm a) (by simpa using hcomm b)
  exact eq_one_of_matrixHom_scalar g c hc

/-- Only the zeroth row of a commuting matrix remains to be certified. -/
public theorem center_eq_bot_of_commutant_row_zero [Group.IsPerfect HN]
    (hrow : ∀ M : Matrix133, M * aMatrix = aMatrix * M →
      M * bMatrix = bMatrix * M →
      ∀ j : Fin 133, M 0 j = if j = 0 then M 0 0 else 0) :
    Subgroup.center HN = ⊥ := by
  apply center_eq_bot_of_scalar_commutant
  intro M ha hb
  exact ⟨M 0 0, commuting_matrix_eq_scalar_of_row_zero M ha hb (M 0 0) (hrow M ha hb)⟩

/-- The fixed HN matrix group has trivial center whenever it is perfect. -/
public theorem center_eq_bot_of_isPerfect [Group.IsPerfect HN] :
    Subgroup.center HN = ⊥ :=
  center_eq_bot_of_commutant_row_zero commuting_matrix_row_zero

end HaradaNorton
