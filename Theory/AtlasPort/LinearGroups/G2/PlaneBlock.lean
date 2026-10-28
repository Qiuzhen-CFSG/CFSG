module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/PlaneBlock.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Theory.AtlasPort.LinearGroups.G2.DistinguishedPlane
public import Theory.AtlasPort.LinearGroups.G2.PointOrbits
public import Mathlib.GroupTheory.GroupAction.Primitive

/-! Products in the distinguished plane determine its first line. A block stabilizer would act transitively on the plane points while fixing that line, a contradiction. -/

@[expose] public section

noncomputable section
namespace Atlas.G2
open Atlas.SplitOctonion
open scoped Pointwise LinearAlgebra.Projectivization
variable {K : Type*} [Field K]

def planePoints : Set (SingularPoints K) :=
  {p | p.val.submodule ≤ distinguishedPlane}

theorem mk_mem_planePoints_iff (x : Carrier K) (hx : x ≠ 0)
    (ht : trace x = 0) (hn : SplitOctonion.norm x = 0) :
    singularPointMk K x hx ht hn ∈ planePoints ↔ x ∈ distinguishedPlane := by
  change (Projectivization.mk K x hx).submodule ≤ distinguishedPlane ↔ _
  rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]

theorem mem_planePoints_iff (p : SingularPoints K) :
    p ∈ planePoints ↔ inLowerPlane p.val.rep := by
  have hm := mk_mem_planePoints_iff p.val.rep p.val.rep_nonzero p.property.1 p.property.2
  rw [singularPointMk_rep] at hm
  rw [hm]
  constructor
  · intro hx
    exact ⟨hx 3 (by decide),hx 4 (by decide),hx 5 (by decide),hx 6 (by decide),hx 7 (by decide)⟩
  · rintro ⟨h3,h4,h5,h6,h7⟩ i hi
    fin_cases i <;> simp_all

theorem planePoints_stabilizer_le :
    MulAction.stabilizer (Model K) (planePoints (K := K)) ≤ pointStabilizer := by
  intro g hg
  apply plane_preserver_mem_pointStabilizer
  intro x hx
  by_cases hz : x=0
  · simp [hz]
  have he := distinguishedPlane_coordinates hx
  have ht : trace x = 0 := by rw [he]; simp [trace]
  have hn : SplitOctonion.norm x = 0 := by rw [he]; simp [SplitOctonion.norm]
  have hm := (mk_mem_planePoints_iff x hz ht hn).mpr hx
  have hgB : g • planePoints = planePoints (K := K) := hg
  have him : g • singularPointMk K x hz ht hn ∈ planePoints := by
    rw [← hgB,Set.smul_mem_smul_set_iff]
    exact hm
  rw [singularPointMk_smul] at him
  exact (mk_mem_planePoints_iff _ _ _ _).mp him

theorem firstPoint_mem_planePoints : firstPoint (K := K) ∈ planePoints := by
  apply (mk_mem_planePoints_iff _ _ _ _).mpr
  exact basis_mem_distinguishedPlane 0 (by decide)

/-- The candidate plane cannot be a block: its product intrinsically distinguishes x1. -/
theorem planePoints_not_block : ¬ MulAction.IsBlock (Model K) (planePoints (K := K)) := by
  intro hB
  let p : SingularPoints K := singularPointMk K (basisVector 1)
    (by intro h; have hh := congrFun h 1; simp [basisVector] at hh)
    (by simp [trace,basisVector]) (by simp [SplitOctonion.norm,basisVector])
  have hp : p ∈ planePoints := (mk_mem_planePoints_iff _ _ _ _).mpr
    (basis_mem_distinguishedPlane 1 (by decide))
  rw [← hB.orbit_stabilizer_eq firstPoint_mem_planePoints] at hp
  obtain ⟨g,hg⟩ := hp
  have he : g.val • firstPoint (K := K) = firstPoint :=
    planePoints_stabilizer_le g.property
  have hpoint : p = firstPoint := hg.symm.trans he
  have hmk := congrArg Subtype.val hpoint
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp hmk
  have hc := congrFun ha 1
  simp [basisVector] at hc

end Atlas.G2
