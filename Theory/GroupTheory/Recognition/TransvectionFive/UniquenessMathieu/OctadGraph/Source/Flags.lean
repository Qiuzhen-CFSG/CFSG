module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.Residue
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Flags
import Mathlib.Tactic.FinCases

/-!
# The marked point-residue flag geometry

The original first-row matrix coordinates show that U₁ ∩ A₂ lies in
U₁ ∩ A₁. Extension of subspace isomorphisms gives transitivity on all
nested pairs of dimensions two and three. Combined with the literal coset
bijections, this identifies common representatives in N_G(U₁) with inclusion
of the corresponding subspaces, both for local cosets and ambient objects.

The ambient theorem retains the common representative in the point
stabilizer. It describes the marked flag orbit; it does not replace the
outstanding global flag-transitivity proof in 41.1, or claim 41.4.

Source: Aschbacher, *Sporadic Groups* (1994), 41.1, printed pp.219–220.
-/

public noncomputable section
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer Subgroup BinaryLinear.TransvectionFiveLocal
open GraphUniquenessSystem.Cosets

private theorem model_row_intersections_nested :
    Model.row ⊓ Model.threeSpace ≤ Model.plane := by
  rintro g ⟨hr, ht⟩
  let a : Model.row := ⟨g, hr⟩
  have hz := (RectangleCoordinates.mem3_iff g).mp ht 0 1 (by decide)
  have he := modelRowCoordinates_matrix a
  change g.val = _ at he
  have h0 : (modelRowCoordinates a).toAdd 0 = 0 := by
    change g.val 0 1 = 0 at hz
    rw [he] at hz
    simpa [Matrix.single] using hz
  apply (RectangleCoordinates.mem2_iff g).mpr
  intro i j hij
  rw [he]
  fin_cases i <;> fin_cases j <;> simp_all [Matrix.single]

variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

/-- The actual row intersections are nested in the order used by source 41.1. -/
theorem row_intersections_nested : F.row ⊓ F.threeSpace ≤ F.plane := by
  rintro a ⟨hr, ht⟩
  let ac : Subgroup.centralizer ({z} : Set G) := ⟨a, F.pullback_le Model.row hr⟩
  apply (F.mem_pullback_iff Model.plane ac).mpr
  exact model_row_intersections_nested
    ⟨(F.mem_pullback_iff Model.row ac).mp hr,
      (F.mem_pullback_iff Model.threeSpace ac).mp ht⟩

/-- The row two-space lies in the marked row hyperplane. -/
theorem row_subspaces_nested : rowSubspace F F.threeSpace ≤ rowSubspace F F.plane := by
  intro v hv
  exact row_intersections_nested F
    ⟨((rowCoordinates F).symm (Multiplicative.ofAdd v)).property, hv⟩

variable (D : LocalData F)

/-- The row normalizer realizes every flag of the two marked dimensions. -/
theorem row_flag_transitive
    (A B : Submodule (ZMod 2) (Fin 4 → ZMod 2))
    (hA : Module.finrank (ZMod 2) A = 2)
    (hB : Module.finrank (ZMod 2) B = 3) (hAB : A ≤ B) :
    ∃ g : rowNormalizer F,
      (rowSubspace F F.threeSpace).map (rowAction F D g).toLinearMap = A ∧
      (rowSubspace F F.plane).map (rowAction F D g).toLinearMap = B := by
  obtain ⟨f, hf⟩ := BinaryLinear.FourParabolicAction.exists_linearEquiv_map_flag
    (rowSubspace F F.threeSpace) (rowSubspace F F.plane) A B
    (row_subspaces_nested F) hAB
    ((row_threeSpace_finrank F).trans hA.symm)
    ((row_plane_finrank F).trans hB.symm)
  obtain ⟨g, rfl⟩ := rowAction_surjective F D f
  exact ⟨g, hf⟩

/-- Common representatives inside the point stabilizer correspond exactly to
nested subspaces. Global flag transitivity is not asserted by this local theorem. -/
theorem row_coset_flag_iff
    (p : rowNormalizer F ⧸ (threeSpaceNormalizer F).subgroupOf (rowNormalizer F))
    (l : rowNormalizer F ⧸ (planeNormalizer F).subgroupOf (rowNormalizer F)) :
    GraphUniquenessSystem.Cosets.Incident
      ((threeSpaceNormalizer F).subgroupOf (rowNormalizer F))
      ((planeNormalizer F).subgroupOf (rowNormalizer F)) p l ↔
      (planeFlagEquiv F D p).val ≤ (lineFlagEquiv F D l).val := by
  constructor
  · rintro ⟨g, rfl, rfl⟩
    simpa only [GraphUniquenessSystem.Cosets.vertex, planeFlagEquiv_mk, lineFlagEquiv_mk]
      using Submodule.map_mono (f := (rowAction F D g).toLinearMap) (row_subspaces_nested F)
  · intro h
    obtain ⟨g, hp, hl⟩ := row_flag_transitive F D
      (planeFlagEquiv F D p).val (lineFlagEquiv F D l).val
      (planeFlagEquiv F D p).property (lineFlagEquiv F D l).property h
    refine ⟨g, (planeFlagEquiv F D).injective ?_, (lineFlagEquiv F D).injective ?_⟩
    · apply Subtype.ext
      exact (planeFlagEquiv_mk F D g).trans hp
    · apply Subtype.ext
      exact (lineFlagEquiv_mk F D g).trans hl

/-- On the actual ambient cosets, a common representative in N_G(U₁)
corresponds exactly to an incident two-space–hyperplane pair. This identifies
the marked flag orbit; global ambient flag transitivity is still required. -/
theorem row_residue_flag_iff
    (p : {p : Plane F // PointPlaneIncident F
      (GraphUniquenessSystem.Cosets.vertex (rowNormalizer F) 1) p})
    (l : {l : Line F // PointLineIncident F
      (GraphUniquenessSystem.Cosets.vertex (rowNormalizer F) 1) l}) :
    (∃ g : rowNormalizer F,
      GraphUniquenessSystem.Cosets.vertex (threeSpaceNormalizer F) (g : G) = p.val ∧
      GraphUniquenessSystem.Cosets.vertex (planeNormalizer F) (g : G) = l.val) ↔
      (planeResidueEquiv F D p).val ≤ (lineResidueEquiv F D l).val := by
  constructor
  · rintro ⟨g, hp, hl⟩
    have hp' : residueEquiv (rowNormalizer F) (threeSpaceNormalizer F)
        (QuotientGroup.mk g) = p := Subtype.ext ((residueEquiv_mk _ _ g).trans hp)
    have hl' : residueEquiv (rowNormalizer F) (planeNormalizer F)
        (QuotientGroup.mk g) = l := Subtype.ext ((residueEquiv_mk _ _ g).trans hl)
    rw [← hp', ← hl', planeResidueEquiv_representative, lineResidueEquiv_representative]
    exact Submodule.map_mono (row_subspaces_nested F)
  · intro h
    obtain ⟨g, hp, hl⟩ := row_flag_transitive F D
      (planeResidueEquiv F D p).val (lineResidueEquiv F D l).val
      (planeResidueEquiv F D p).property (lineResidueEquiv F D l).property h
    have hp' := (planeResidueEquiv F D).injective
      (Subtype.ext ((planeResidueEquiv_representative F D g).trans hp))
    have hl' := (lineResidueEquiv F D).injective
      (Subtype.ext ((lineResidueEquiv_representative F D g).trans hl))
    exact ⟨g, (residueEquiv_mk _ _ g).symm.trans (congrArg Subtype.val hp'),
      (residueEquiv_mk _ _ g).symm.trans (congrArg Subtype.val hl')⟩

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
