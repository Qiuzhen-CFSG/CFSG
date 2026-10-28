module
public import Theory.Representation.OrthogonalFourMinusRankOne.RootActors

/-!
# Fixed spaces of outer fixed-field root involutions

For the Hermitian SL₂ action over the quadratic extension of K, the outer
operator upper(u) times conjugation has displacement
(trace(z) + u b) times the matrix [u,1;1,0]. Its fixed space is therefore a
K-hyperplane. Every inner or outer displacement lies in the fixed plane of
the fixed-field root group, which all these operators fix pointwise.

These explicit formulas use the existing left action and upper-right
coordinate conventions. They supply the local outer-actor calculations of
Aschbacher–Smith, K.3.1.2, printed p.454, with ratios as in D.2.1, p.178.
-/

@[expose] public noncomputable section
namespace Representation.OrthogonalFourMinus.RankOne
open Representation.OrthogonalFourMinus
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.HermitianEquiv
open Representation.BinaryOffender Matrix.SpecialLinearGroup
variable (s : ℕ) [NeZero s]
local instance outerSubgroupFixedAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance outerSubgroupBinarySpace : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

def outerRootAction (u : fixedField s) : Space s →ₗ[fixedField s] Space s :=
  (action s (upper s u.val)).comp (conjugationLinear s).toLinearMap

def bottomFunctional : Space s →ₗ[fixedField s] fixedField s where
  toFun X := ⟨X.val 1 1, entry_fixed s X 1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def outerRootFunctional (u : fixedField s) : Space s →ₗ[fixedField s] fixedField s :=
  traceFunctional s + u • bottomFunctional s

theorem outerRootAction_displacement (u : fixedField s) (X : Space s) :
    (outerRootAction s u X - X).val =
      !![u.val * ((outerRootFunctional s u X).val), (outerRootFunctional s u X).val;
        (outerRootFunctional s u X).val, 0] := by
  have hu : conjugation s u.val = u.val := u.property
  change (action s (upper s u.val) (conjugationLinear s X)).val - X.val =
    !![u.val * (X.val 0 1 + X.val 1 0 + u.val * X.val 1 1),
      X.val 0 1 + X.val 1 0 + u.val * X.val 1 1;
      X.val 0 1 + X.val 1 0 + u.val * X.val 1 1, 0]
  rw [action_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, transvection_coe, adjoint, conjugationLinear,
      Matrix.mul_apply, Fin.sum_univ_two, hu, sub_eq_add_neg, CharTwo.neg_eq] <;>
    ring_nf
  all_goals simp only [CharTwo.two_eq_zero, mul_zero, zero_add]

/-- The literal cyclic outer fixed hyperplane, in K-linear model coordinates. -/
def outerRootFixedHyperplane (u : fixedField s) : Submodule (fixedField s) (Space s) :=
  (outerRootFunctional s u).ker

theorem outerRoot_fixed_iff (u : fixedField s) (X : Space s) :
    outerRootAction s u X = X ↔
      traceFunctional s X = u * bottomFunctional s X := by
  rw [← sub_eq_zero]
  constructor
  · intro he
    have h01 := congrArg (fun Y : Space s => Y.val 0 1) he
    have hf : outerRootFunctional s u X = 0 := by
      apply Subtype.ext
      change (outerRootAction s u X - X).val 0 1 = 0 at h01
      rw [outerRootAction_displacement] at h01
      exact h01
    exact CharTwo.add_eq_zero.mp hf
  · intro he
    have hf : outerRootFunctional s u X = 0 := CharTwo.add_eq_zero.mpr he
    apply Subtype.ext
    rw [outerRootAction_displacement, hf]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem mem_outerRootFixedHyperplane_iff (u : fixedField s) (X : Space s) :
    X ∈ outerRootFixedHyperplane s u ↔ outerRootAction s u X = X := by
  rw [outerRoot_fixed_iff]
  exact CharTwo.add_eq_zero

theorem outerRootFunctional_surjective (u : fixedField s) :
    Function.Surjective (outerRootFunctional s u) := by
  apply LinearMap.surjective_iff_ne_zero.mpr
  intro hz
  obtain ⟨z, hzne⟩ := exists_conjugation_ne s
  have he := congrArg (fun f : Space s →ₗ[fixedField s] fixedField s =>
    (f (offDiagonal s z)).val) hz
  have he' : z + conjugation s z = 0 := by
    change z + conjugation s z + u.val * 0 = 0 at he
    simpa using he
  exact hzne (CharTwo.add_eq_zero.mp he').symm

theorem outerRootFixedHyperplane_finrank (u : fixedField s) :
    Module.finrank (fixedField s) (outerRootFixedHyperplane s u) = 3 := by
  have hr := (outerRootFunctional s u).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (outerRootFunctional_surjective s u),
    finrank_top, Module.finrank_self, finrank_space] at hr
  change Module.finrank (fixedField s) (outerRootFunctional s u).ker = 3
  omega

/-- Restriction of scalars for any actual K-subspace of the model. -/
theorem model_subspace_binary_finrank (P : Submodule (fixedField s) (Space s)) :
    Module.finrank (ZMod 2) P = s * Module.finrank (fixedField s) P := by
  have hc := Module.natCard_eq_pow_finrank (K := fixedField s) (V := P)
  rw [card_fixedField, ← pow_mul] at hc
  have hb := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := P)
  have he : 2 ^ Module.finrank (ZMod 2) P =
      2 ^ (s * Module.finrank (fixedField s) P) := by
    simpa only [Nat.card_zmod] using hb.symm.trans hc
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) he

/-- A nonzero fixed-field root fixes the whole root fixed plane. -/
theorem fixedField_root_fixed_iff {u : fixedField s} (hu : u ≠ 0) (X : Space s) :
    action s (upper s u.val) X = X ↔
      X ∈ fixedSpace (SL2.BinarySmall.hermitian s) (fixedRootGroup s) := by
  have hu0 : u.val ≠ 0 := fun hz => hu (Subtype.ext hz)
  have huf : conjugation s u.val = u.val := u.property
  rw [root_fixed_iff s hu0, mem_fixedSpace_fixedRootGroup_iff]
  rw [huf, ← mul_add, mul_eq_zero, or_iff_right hu0, CharTwo.add_eq_zero]

/-- All the inner and outer displacements land in the same fixed K-plane. -/
theorem rootDifference_mem_fixedRoot (u : fixedField s) (X : Space s) :
    rootDifference s u.val X ∈ fixedSpace (SL2.BinarySmall.hermitian s) (fixedRootGroup s) := by
  rw [mem_fixedSpace_fixedRootGroup_iff, rootDifference_val]
  have hu : conjugation s u.val = u.val := u.property
  simp [map_mul, hu, entry_fixed]

theorem outerRootDifference_mem_fixedRoot (u : fixedField s) (X : Space s) :
    outerRootAction s u X - X ∈ fixedSpace (SL2.BinarySmall.hermitian s) (fixedRootGroup s) := by
  rw [mem_fixedSpace_fixedRootGroup_iff, outerRootAction_displacement]
  exact ⟨rfl, (outerRootFunctional s u X).property⟩

theorem outerRoot_fixes_fixedRoot (u : fixedField s) {X : Space s}
    (hX : X ∈ fixedSpace (SL2.BinarySmall.hermitian s) (fixedRootGroup s)) :
    outerRootAction s u X = X := by
  obtain ⟨hb, hz⟩ := (mem_fixedSpace_fixedRootGroup_iff s X).mp hX
  rw [outerRoot_fixed_iff]
  apply Subtype.ext
  change X.val 0 1 + X.val 1 0 = u.val * X.val 1 1
  rw [← entry_conjugate s X 1 0, hz, hb, mul_zero, CharTwo.add_self_eq_zero]

end Representation.OrthogonalFourMinus.RankOne
