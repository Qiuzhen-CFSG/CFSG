/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianCoordinateAxisOrbits.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianReferenceNormCoordinates
public import Theory.AtlasPort.Janko2.Conway.IcosianMonomialPointNorms
public import Theory.AtlasPort.Janko2.GroupTheory.StabilizerInvariantOrbits

/-!
# IcosianCoordinateAxisOrbits

The lifted monomial stabilizer is transitive on each fixed-shape, fixed-norm class
relative to an axis. Reference representatives and coordinate swaps construct the
transport.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianCoordinateAxisOrbits.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

attribute [local instance] icosianLiftedRootPointAction

@[instance_reducible]
def icosianLiftedAxisAction : MulAction icosianLiftedMonomial (Fin 3) where
  smul g i := g.val.right i
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

attribute [local instance] icosianLiftedAxisAction

theorem icosianReference_axis_transitive (a : Fin 4) (i j : Fin 3)
    (h : icosianRootPointNormWord (icosianRootLocalRepresentative a) i=
      icosianRootPointNormWord (icosianRootLocalRepresentative a) j) :
    ∃ g : icosianLiftedMonomial,
      g • icosianRootLocalRepresentative a=icosianRootLocalRepresentative a ∧ g • i=j := by
  have he : (icosianRootLocalVector a).val i=(icosianRootLocalVector a).val j := by
    apply icosianRootLocalVector_equal_norm
    simpa only [← icosianRootLocalVector_toPoint,icosianRootPointNormWord_toPoint] using h
  refine ⟨icosianPureBlockPermutation (Equiv.swap i j),?_,?_⟩
  · apply Subtype.ext
    change icosianMonomialToHermitian (icosianPureBlockPermutation (Equiv.swap i j)) •
      (icosianRootLocalRepresentative a).val=(icosianRootLocalRepresentative a).val
    rw [← icosianRootLocalVector_toPoint]
    exact icosianEqualCoordinate_swap_fixes _ _ _ he
  · change (Equiv.swap i j) i=j
    exact Equiv.swap_apply_left _ _

/-- The axis-fixing subgroup of the complete coordinate-frame stabilizer is
transitive on every fixed norm-shape and fixed coordinate-zero norm class. -/
theorem icosianCoordinateAxis_shape_norm_transitive (a : Fin 4)
    (p q : IcosianRootPoint) (hp : HasIcosianRootPointShape p a)
    (hq : HasIcosianRootPointShape q a)
    (hn : icosianRootPointNormWord p 0=icosianRootPointNormWord q 0) :
    ∃ g : icosianCoordinateFrameStabilizer,
      g.val • icosianRootAxisPoint 0=icosianRootAxisPoint 0 ∧ g.val • p=q := by
  have hr (x : IcosianRootPoint) (hx : HasIcosianRootPointShape x a) :
      x∈MulAction.orbit icosianLiftedMonomial (icosianRootLocalRepresentative a) := by
    obtain ⟨g,hg⟩ := (icosianRootPoint_local_orbit a x).mpr hx
    obtain ⟨m,hm⟩ := (show g.val∈icosianMonomialToHermitian.range from
      icosianMonomial_range_eq_frameStabilizer.symm ▸ g.property)
    refine ⟨m,?_⟩
    change icosianMonomialToHermitian m • icosianRootLocalRepresentative a=x
    change g.val • icosianRootLocalRepresentative a=x at hg
    simpa only [hm] using hg
  obtain ⟨g,hg,hpq⟩ := Atlas.stabilizer_transitive_of_reference_invariant
    icosianRootPointNormWord (fun g x i => icosianMonomialPoint_norm_invariant g x i)
    (icosianRootLocalRepresentative a) (0 : Fin 3)
    (icosianReference_axis_transitive a) p q (hr p hp) (hr q hq) hn
  refine ⟨⟨icosianMonomialToHermitian g,icosianMonomial_mem_frameStabilizer g⟩,?_,hpq⟩
  apply Subtype.ext
  change icosianMonomialToHermitian g • (icosianRootAxisPoint 0).val=
    (icosianRootAxisPoint 0).val
  rw [icosianRootAxisPoint_val,icosianMonomial_axis]
  exact congrArg icosianAxisPoint hg

end Atlas.Conway
