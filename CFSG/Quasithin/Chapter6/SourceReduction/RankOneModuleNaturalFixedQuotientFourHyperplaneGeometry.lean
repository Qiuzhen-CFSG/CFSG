module

public import Theory.Representation.OrthogonalFourMinusRankOne.InnerClassification.Lines
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.FieldTheory.Finite.Trace

/-!
# Canonical nonsingular trace hyperplanes in the Hermitian model

The trace of the polar pairing identifies a genuine binary hyperplane for
each nonzero pole. For a canonical pole offDiagonal(z), the fixed-field root
line zK stabilizes that hyperplane, and its entire fixed plane is orthogonal
to the pole. The upper-root fixed singular line also lies in the hyperplane.

These are canonical-coordinate statements. An arbitrary escaping hyperplane
must first be moved into these coordinates by an actual layer conjugation;
the fixed-space containment is false for arbitrary hyperplanes with a fixed
Sylow subgroup. Source: Aschbacher–Smith, 6.1.4, printed p.665.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter6.Source.FourHyperplaneGeometry
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.HermitianEquiv
open Representation.OrthogonalFourMinus.RankOne
open Matrix.SpecialLinearGroup
variable (s : ℕ) [NeZero s]

local instance geometryFixedAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance geometryBinaryModule : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- The binary trace of the polar functional at the specified actual pole. -/
def tracePolarFunctional (v : Space s) : Space s →ₗ[ZMod 2] ZMod 2 :=
  (((Algebra.trace (ZMod 2) (fixedField s)).toAddMonoidHom).comp
    (((form s).polarBilin v).toAddMonoidHom)).toZModLinearMap 2

/-- The binary hyperplane belonging to the literal nonzero pole. -/
def traceHyperplane (v : Space s) : Submodule (ZMod 2) (Space s) :=
  (tracePolarFunctional s v).ker

/-- Trace-polar coordinates lose no nonzero pole. -/
theorem tracePolarFunctional_ne_zero {v : Space s} (hv : v ≠ 0) :
    tracePolarFunctional s v ≠ 0 := by
  intro hz
  apply hv
  apply (form_nonsingular s).1 v
  intro w
  apply (traceForm_nondegenerate (ZMod 2) (fixedField s)).1
  intro a
  have he := LinearMap.congr_fun hz (a • w)
  change Algebra.trace (ZMod 2) (fixedField s) ((form s).polarBilin v (a • w)) = 0 at he
  rw [map_smul,smul_eq_mul] at he
  simpa only [Algebra.traceForm_apply,mul_comm] using he

/-- The kernel of the trace-polar functional has binary corank one. -/
theorem traceHyperplane_finrank {v : Space s} (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (traceHyperplane s v) + 1 =
      Module.finrank (ZMod 2) (Space s) :=
  Module.Dual.finrank_ker_add_one_of_ne_zero (tracePolarFunctional_ne_zero s hv)

/-- Every nonzero canonical off-diagonal pole is nonsingular. -/
theorem offDiagonal_nonsingular {z : Field s} (hz : z ≠ 0) :
    form s (offDiagonal s z) ≠ 0 := by
  rw [form_eq_coordinates,coordinates_offDiagonal]
  simp only [zero_mul,zero_sub]
  exact neg_ne_zero.mpr ((norm_eq_zero_iff s z).not.mpr hz)

/-- The root line zK fixes the canonical nonsingular pole offDiagonal(z). -/
theorem rootLine_fixes_offDiagonal {z : Field s} (hz : z ≠ 0)
    {g : Matrix.SpecialLinearGroup (Fin 2) (Field s)} (hg : g ∈ rootLine s z) :
    action s g (offDiagonal s z) = offDiagonal s z := by
  obtain ⟨k,rfl⟩ := (mem_rootLine_iff s z g).mp hg
  by_cases hk : k = 0
  · subst k
    simp only [Subfield.coe_zero,mul_zero,upper,transvection_coeff_zero,map_one,Module.End.one_apply]
  have hk0 : k.val ≠ 0 := fun h => hk (Subtype.ext h)
  apply (root_fixed_iff s (mul_ne_zero hz hk0) _).mpr
  refine ⟨rfl,?_⟩
  change z * k.val * conjugation s z + conjugation s (z * k.val) * z = 0
  have hkfix : conjugation s k.val = k.val := k.property
  rw [map_mul,hkfix]
  calc
    _ = (z * conjugation s z * k.val) + (z * conjugation s z * k.val) := by ring
    _ = 0 := CharTwo.add_self_eq_zero _

/-- The canonical root line preserves the actual trace hyperplane. -/
theorem rootLine_le_traceHyperplane_stabilizer {z : Field s} (hz : z ≠ 0) :
    rootLine s z ≤ subspaceStabilizer (SL2.BinarySmall.hermitian s)
      (traceHyperplane s (offDiagonal s z)) := by
  apply le_subspaceStabilizer
  intro g hg X hX
  change Algebra.trace (ZMod 2) (fixedField s)
    ((form s).polarBilin (offDiagonal s z) (action s g X)) = 0
  have he := polar_preserved s (orthogonalAction s g) (offDiagonal s z) X
  change (form s).polarBilin (action s g (offDiagonal s z)) (action s g X) = _ at he
  rw [rootLine_fixes_offDiagonal s hz hg] at he
  rw [he]
  exact hX

/-- The whole fixed plane of zK is orthogonal to the canonical pole. -/
theorem rootLine_fixed_polar_zero {z : Field s} (hz : z ≠ 0)
    {X : Space s} (hX : X ∈ fixedSpace (SL2.BinarySmall.hermitian s) (rootLine s z)) :
    (form s).polarBilin (offDiagonal s z) X = 0 := by
  have hx := (root_fixed_iff s hz X).mp
    (hX ⟨upper s z,upper_mem_rootLine s z⟩)
  apply Subtype.ext
  rw [coe_polar_coordinates,coordinates_offDiagonal]
  change 0 * X.val 1 1 + 0 * X.val 0 0 -
    (z * conjugation s (X.val 0 1) + X.val 0 1 * conjugation s z) = 0
  simpa only [zero_mul,zero_add,zero_sub,mul_comm,neg_eq_zero] using hx.2

/-- The canonical root-line fixed plane is contained in its trace hyperplane. -/
theorem rootLine_fixed_le_traceHyperplane {z : Field s} (hz : z ≠ 0) :
    fixedSpace (SL2.BinarySmall.hermitian s) (rootLine s z) ≤
      traceHyperplane s (offDiagonal s z) := by
  intro X hX
  change Algebra.trace (ZMod 2) (fixedField s) ((form s).polarBilin (offDiagonal s z) X) = 0
  rw [rootLine_fixed_polar_zero s hz hX,map_zero]

/-- The upper-root fixed singular line lies in every canonical trace hyperplane. -/
theorem upper_fixed_le_traceHyperplane {z : Field s} (hz : z ≠ 0) :
    fixedSpace (SL2.BinarySmall.hermitian s) (upperUnipotent (Field s)) ≤
      traceHyperplane s (offDiagonal s z) := by
  intro X hX
  apply rootLine_fixed_le_traceHyperplane s hz
  intro g
  exact hX ⟨g.val,rootLine_le_upper s z g.property⟩

/-- Inside the canonical Sylow root group, the stabilizer's fixed space is
contained in the specified nonsingular trace hyperplane. -/
theorem upper_stabilizer_fixed_le_traceHyperplane {z : Field s} (hz : z ≠ 0) :
    fixedSpace (SL2.BinarySmall.hermitian s)
      (upperUnipotent (Field s) ⊓ subspaceStabilizer (SL2.BinarySmall.hermitian s)
        (traceHyperplane s (offDiagonal s z))) ≤
      traceHyperplane s (offDiagonal s z) := by
  intro X hX
  apply rootLine_fixed_le_traceHyperplane s hz
  intro g
  exact hX ⟨g.val,rootLine_le_upper s z g.property,
    rootLine_le_traceHyperplane_stabilizer s hz g.property⟩

end CFSG.Quasithin.Chapter6.Source.FourHyperplaneGeometry
