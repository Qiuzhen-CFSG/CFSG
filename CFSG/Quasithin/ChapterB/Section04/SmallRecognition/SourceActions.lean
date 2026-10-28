module

public import Theory.Representation.BinaryLinearRecognition.OrthogonalEight
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Actual actions and parabolics for the small recognition lemmas

The point stabilizer is computed in the supplied representation. The orthogonal
model is the checked deleted A₈ action, pulled back along the actual exceptional
PSL₄(2) isomorphism. An endpoint parabolic is a stabilizer of a one- or
three-dimensional subspace of the natural four-space. The source seed records
the common Sylow two-subgroup and the dimension-three span of the H-orbit;
it asserts no module recognition or existence of an intertwiner.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), B.4.12(2) and B.4.13, printed pp.97–98.
The imported exceptional comparison preserves its ATLAS attribution and license.
-/

@[expose] public section

open Representation
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterB.SmallRecognition

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- C_G(v) in the original linear action. -/
def vectorStabilizer (ρ : Representation (ZMod 2) G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by change ρ 1 v = v; simp
  mul_mem' := by
    intro g h hg hh
    change ρ g v = v at hg
    change ρ h v = v at hh
    change ρ (g * h) v = v
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change ρ g v = v at hg
    change ρ g⁻¹ v = v
    have h := congrArg (ρ g⁻¹) hg
    simpa only [ρ.inv_self_apply] using h.symm

/-- The literal split quadratic six-space. -/
abbrev OrthogonalSpace := ClassicalOrthogonal.VectorD 3 (ZMod 2)

/-- The orthogonal action retains the given PSL₄ marking. -/
noncomputable def orthogonalAction (e : G ≃* PSL(4, ZMod 2)) :
    Representation (ZMod 2) G OrthogonalSpace :=
  BinaryLinearRecognition.orthogonalEightAction.comp
    (e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).toMonoidHom

/-- The actual natural four-space action belonging to the same marking. -/
noncomputable def naturalFourAction (e : G ≃* PSL(4, ZMod 2)) :
    G →* BinaryLinear.GL (Fin 4 → ZMod 2) :=
  (e.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide))).toMonoidHom

/-- An endpoint maximal parabolic of the actual natural four-space. -/
def IsEndpointParabolic (e : G ≃* PSL(4, ZMod 2)) (H : Subgroup G) : Prop :=
  ∃ A : Submodule (ZMod 2) (Fin 4 → ZMod 2),
    (Module.finrank (ZMod 2) A = 1 ∨ Module.finrank (ZMod 2) A = 3) ∧
      H = (BinaryLinear.parabolic A).comap (naturalFourAction e)

/-- The local hypotheses of B.4.13. The global spanning hypothesis is kept
separate so that the local construction can produce an embedding first. -/
structure OrthogonalSeed (e : G ≃* PSL(4, ZMod 2))
    (ρ : Representation (ZMod 2) G V) (v : V) where
  nonzero : v ≠ 0
  point : OrthogonalSpace
  point_ne_zero : point ≠ 0
  point_singular : ClassicalOrthogonal.formD 3 (ZMod 2) point = 0
  stabilizer : vectorStabilizer ρ v = vectorStabilizer (orthogonalAction e) point
  H : Subgroup G
  endpoint : IsEndpointParabolic e H
  T : Sylow 2 G
  sylow_point : (T : Subgroup G) ≤ vectorStabilizer ρ v
  sylow_endpoint : (T : Subgroup G) ≤ H
  orbit_rank : Module.finrank (ZMod 2)
    (Submodule.span (ZMod 2) (Set.range fun h : H => ρ h v)) = 3

end CFSG.Quasithin.ChapterB.SmallRecognition
