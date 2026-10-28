/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianPointNormalizations.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootLocalOrbits
public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionShapeLinks
public import Theory.AtlasPort.Janko2.Conway.IcosianLocalGeometryTransport

/-!
# IcosianPointNormalizations

Four local monomial orbits are connected by explicit root reflections. These point
normalizers transport local orthogonal geometry and prove the 525-frame count.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianPointNormalizations.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped Matrix

def icosianCoordinateAxisNormalizer (i : Fin 3) : icosianHermitianGroup :=
  icosianMonomialToHermitian (icosianPureBlockPermutation (Equiv.swap 0 i))

theorem icosianCoordinateAxisNormalizer_mem (i : Fin 3) :
    icosianCoordinateAxisNormalizer i∈icosianCoordinateFrameStabilizer :=
  icosianMonomial_mem_frameStabilizer _

theorem icosianCoordinateAxisNormalizer_axis (i : Fin 3) :
    icosianCoordinateAxisNormalizer i • icosianRootAxisPoint 0=icosianRootAxisPoint i := by
  simpa [icosianCoordinateAxisNormalizer] using icosianPureBlockPermutation_axis (Equiv.swap 0 i) 0

def icosianShapeSeedRoot : Fin 4 → IcosianRoot := ![
  icosianAxisRoot (0,1),icosianReflectedAxisRoot icosianLocalCRoot 0,
  icosianReflectedAxisRoot icosianLocalCRoot 1,icosianReflectedAxisRoot icosianLocalDRoot 2]

def icosianShapeSeedNormalizer : Fin 4 → icosianHermitianGroup := ![
  1,icosianRootReflectionOf icosianLocalCRoot,
  icosianRootReflectionOf icosianLocalCRoot*icosianCoordinateAxisNormalizer 1,
  icosianRootReflectionOf icosianLocalDRoot*icosianCoordinateAxisNormalizer 2]

theorem icosianShapeSeedNormalizer_axis (i : Fin 4) :
    icosianShapeSeedNormalizer i • icosianRootAxisPoint 0=icosianRootToPoint (icosianShapeSeedRoot i) := by
  fin_cases i
  · exact one_smul _ _
  · exact (icosianReflectedAxisRoot_point _ _).symm
  · change (icosianRootReflectionOf icosianLocalCRoot*icosianCoordinateAxisNormalizer 1) • _=_
    rw [mul_smul,icosianCoordinateAxisNormalizer_axis]
    exact (icosianReflectedAxisRoot_point _ _).symm
  · change (icosianRootReflectionOf icosianLocalDRoot*icosianCoordinateAxisNormalizer 2) • _=_
    rw [mul_smul,icosianCoordinateAxisNormalizer_axis]
    exact (icosianReflectedAxisRoot_point _ _).symm

theorem icosianShapeSeedRoot_shape (i : Fin 4) : HasIcosianRootShape (icosianShapeSeedRoot i) i := by
  fin_cases i
  · exact (icosianRootShape_axis _).mpr (icosianAxisRoot_axis (0,1))
  · exact icosianReflection_C_axis0_shape
  · exact icosianReflection_C_axis1_shape
  · exact icosianReflection_D_axis2_shape

/-- Structural normalizations use only the complete local monomial orbits and
three explicitly verified reflection links between the four coordinate shapes. -/
theorem icosianRootPoint_normalizers_in (K : Subgroup icosianHermitianGroup)
    (hH : icosianCoordinateFrameStabilizer≤K)
    (hR : ∀ r : IcosianRoot,icosianRootReflectionOf r∈K)
    (p : IcosianRootPoint) :
    ∃ g : icosianHermitianGroup,g∈K ∧ g • icosianRootAxisPoint 0=p := by
  obtain ⟨i,hp⟩ := icosianRootPointShape_exhaustive p
  have hs : HasIcosianRootPointShape (icosianRootToPoint (icosianShapeSeedRoot i)) i :=
    ⟨icosianShapeSeedRoot i,rfl,icosianShapeSeedRoot_shape i⟩
  obtain ⟨a,ha⟩ := (icosianRootPoint_local_orbit i _).mpr hp
  obtain ⟨b,hb⟩ := (icosianRootPoint_local_orbit i _).mpr hs
  change a.val • icosianRootLocalRepresentative i=p at ha
  change b.val • icosianRootLocalRepresentative i=icosianRootToPoint (icosianShapeSeedRoot i) at hb
  have hg : icosianShapeSeedNormalizer i∈K := by
    fin_cases i
    · exact K.one_mem
    · exact hR _
    · exact K.mul_mem (hR _) (hH (icosianCoordinateAxisNormalizer_mem 1))
    · exact K.mul_mem (hR _) (hH (icosianCoordinateAxisNormalizer_mem 2))
  refine ⟨a.val*b.val⁻¹*icosianShapeSeedNormalizer i,
    K.mul_mem (K.mul_mem (hH a.property) (K.inv_mem (hH b.property))) hg,?_⟩
  rw [mul_smul,mul_smul,icosianShapeSeedNormalizer_axis,← hb,inv_smul_smul]
  exact ha

/-- Actual full Hermitian normalizers, prior to any full-group order or reflection-generation theorem. -/
theorem icosianRootPoint_normalizers (p : IcosianRootPoint) :
    ∃ g : icosianHermitianGroup,g • icosianRootAxisPoint 0=p := by
  obtain ⟨g,_,hg⟩ := icosianRootPoint_normalizers_in ⊤ (by intro _ _; trivial)
    (fun _ => trivial) p
  exact ⟨g,hg⟩

theorem icosianRootNeighbors_card (p : IcosianRootPoint) : Nat.card (IcosianRootNeighbors p)=10 := by
  obtain ⟨g,hg⟩ := icosianRootPoint_normalizers p
  exact icosianRootNeighbors_card_of_normalizer p g hg

theorem icosianRootPoint_completion (p q : IcosianRootPoint)
    (hpq : IcosianRootPointOrthogonal p q) :
    ∃! r : IcosianRootPoint,IcosianRootPointOrthogonal p r ∧ IcosianRootPointOrthogonal q r := by
  obtain ⟨g,hg⟩ := icosianRootPoint_normalizers p
  exact icosianRoot_completion_of_normalizer p g hg q hpq

/-- All actual quaternionic root frames: independent finite-incidence count. -/
theorem icosianRootFrames_card : Nat.card IcosianRootFrame=525 :=
  icosianRootFrame_card_of_normalizers icosianRootPoint_normalizers

end Atlas.Conway
