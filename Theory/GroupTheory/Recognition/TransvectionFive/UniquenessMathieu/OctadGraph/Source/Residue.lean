module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.RowGeometry
public import Theory.GroupTheory.GraphUniquenessSystem.CosetResidue
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Cosets

/-!
# Concrete point-residue coordinates for the Mathieu source cosets

The vertices, lines, and planes are respectively the literal left cosets
of N_G(U₁), N_G(A₁), and N_G(A₂). Incidence means a common representative.
The proved row-parabolic identities identify all lines and all planes through
the base point with the three- and two-dimensional subspaces of the row module.
The formulas retain the original conjugation action and marked intersections.

These are point-residue bijections from genuine SourceNormalizer.LocalData.
They do not assume or prove global flag transitivity or the §41.4 comparison.

Source: Aschbacher, *Sporadic Groups* (1994), 41.1, printed pp.219–220.
-/

public noncomputable section
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer GraphUniquenessSystem
open BinaryLinear.FourParabolicAction
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z) (D : LocalData F)

/-- Source points are the literal cosets of N_G(U₁). -/
abbrev Point := G ⧸ rowNormalizer F
/-- Source lines are the literal cosets of N_G(A₁). -/
abbrev Line := G ⧸ planeNormalizer F
/-- Source planes are the literal cosets of N_G(A₂). -/
abbrev Plane := G ⧸ threeSpaceNormalizer F

/-- Line incidence uses common representatives in G. -/
abbrev PointLineIncident : Point F → Line F → Prop :=
  Cosets.Incident (rowNormalizer F) (planeNormalizer F)
/-- Plane incidence uses common representatives in G. -/
abbrev PointPlaneIncident : Point F → Plane F → Prop :=
  Cosets.Incident (rowNormalizer F) (threeSpaceNormalizer F)

/-- The marked line flags are the hyperplanes of the actual row module. -/
def lineFlagEquiv :
    (rowNormalizer F ⧸ (planeNormalizer F).subgroupOf (rowNormalizer F)) ≃
      {W : Submodule (ZMod 2) (Fin 4 → ZMod 2) // Module.finrank (ZMod 2) W = 3} :=
  ((Subgroup.quotientEquivOfEq (line_parabolic_comap F D).symm).trans
    (cosetSubspaceEquiv (rowAction F D) (rowSubspace F F.plane)
      (rowAction_surjective F D))).trans
    (Equiv.subtypeEquivRight (fun W => by rw [row_plane_finrank F]))

/-- The marked plane flags are the two-spaces of the same row module. -/
def planeFlagEquiv :
    (rowNormalizer F ⧸ (threeSpaceNormalizer F).subgroupOf (rowNormalizer F)) ≃
      {W : Submodule (ZMod 2) (Fin 4 → ZMod 2) // Module.finrank (ZMod 2) W = 2} :=
  ((Subgroup.quotientEquivOfEq (plane_parabolic_comap F D).symm).trans
    (cosetSubspaceEquiv (rowAction F D) (rowSubspace F F.threeSpace)
      (rowAction_surjective F D))).trans
    (Equiv.subtypeEquivRight (fun W => by rw [row_threeSpace_finrank F]))

@[simp] theorem lineFlagEquiv_mk (g : rowNormalizer F) :
    (lineFlagEquiv F D (QuotientGroup.mk g)).val =
      (rowSubspace F F.plane).map (rowAction F D g).toLinearMap := by
  simp [lineFlagEquiv, Subgroup.quotientEquivOfEq_mk]

@[simp] theorem planeFlagEquiv_mk (g : rowNormalizer F) :
    (planeFlagEquiv F D (QuotientGroup.mk g)).val =
      (rowSubspace F F.threeSpace).map (rowAction F D g).toLinearMap := by
  simp [planeFlagEquiv, Subgroup.quotientEquivOfEq_mk]

/-- Lines incident with the actual source point, as concrete row hyperplanes. -/
def lineResidueEquiv :
    {l : Line F // PointLineIncident F (Cosets.vertex (rowNormalizer F) 1) l} ≃
      {W : Submodule (ZMod 2) (Fin 4 → ZMod 2) // Module.finrank (ZMod 2) W = 3} :=
  (Cosets.residueEquiv (rowNormalizer F) (planeNormalizer F)).symm.trans
    (lineFlagEquiv F D)

/-- Planes incident with the same actual source point, as concrete row two-spaces. -/
def planeResidueEquiv :
    {p : Plane F // PointPlaneIncident F (Cosets.vertex (rowNormalizer F) 1) p} ≃
      {W : Submodule (ZMod 2) (Fin 4 → ZMod 2) // Module.finrank (ZMod 2) W = 2} :=
  (Cosets.residueEquiv (rowNormalizer F) (threeSpaceNormalizer F)).symm.trans
    (planeFlagEquiv F D)

/-- The line identification uses the actual image of the marked row intersection. -/
theorem lineResidueEquiv_representative (g : rowNormalizer F) :
    (lineResidueEquiv F D
      ((Cosets.residueEquiv (rowNormalizer F) (planeNormalizer F)) (QuotientGroup.mk g))).val =
        (rowSubspace F F.plane).map (rowAction F D g).toLinearMap := by
  simp [lineResidueEquiv]

/-- The plane identification retains the same original row coordinates. -/
theorem planeResidueEquiv_representative (g : rowNormalizer F) :
    (planeResidueEquiv F D
      ((Cosets.residueEquiv (rowNormalizer F) (threeSpaceNormalizer F)) (QuotientGroup.mk g))).val =
        (rowSubspace F F.threeSpace).map (rowAction F D g).toLinearMap := by
  simp [planeResidueEquiv]

/-- The line coordinates respect the original row-normalizer action. -/
theorem lineFlagEquiv_smul (g : rowNormalizer F)
    (q : rowNormalizer F ⧸ (planeNormalizer F).subgroupOf (rowNormalizer F)) :
    (lineFlagEquiv F D (g • q)).val =
      (lineFlagEquiv F D q).val.map (rowAction F D g).toLinearMap := by
  induction q using QuotientGroup.induction_on with
  | H a =>
    change (lineFlagEquiv F D (QuotientGroup.mk (g * a))).val = _
    rw [lineFlagEquiv_mk, lineFlagEquiv_mk, map_mul, ← Submodule.map_comp]
    rfl

/-- The plane coordinates respect that same action. -/
theorem planeFlagEquiv_smul (g : rowNormalizer F)
    (q : rowNormalizer F ⧸ (threeSpaceNormalizer F).subgroupOf (rowNormalizer F)) :
    (planeFlagEquiv F D (g • q)).val =
      (planeFlagEquiv F D q).val.map (rowAction F D g).toLinearMap := by
  induction q using QuotientGroup.induction_on with
  | H a =>
    change (planeFlagEquiv F D (QuotientGroup.mk (g * a))).val = _
    rw [planeFlagEquiv_mk, planeFlagEquiv_mk, map_mul, ← Submodule.map_comp]
    rfl

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
