module

public import Theory.Representation.Mathieu.M22James.Unitary
public import Theory.Representation.BinaryOffender.CubicInversionContainment

/-!
# The native cubic point in the Mathieu module

The actual binary ATLAS group acts by its twelve-dimensional column action.
Its derived subgroup is the genuine triple cover, with the same representation
and central F₄ scalars as the James model. The native outer involution inverts
the distinguished cubic scalar. The commutator of a binary line with that
scalar subgroup is exactly its F₄-point, hence has binary dimension two and
order four when the line is nonzero.

This proves the first point calculation used in Aschbacher–Smith 14.4.12,
printed pp.1011–1012, and preserves the literal native action needed for the
conjugation-quotient adapter. It does not assume that a supplied line is the
fixed space of the source Sylow subgroup. The native ATLAS attribution and
matrix conventions are retained in the imported `M22James.Model` sources.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Sporadic.Mathieu M22TripleCover
open M22TripleCover.Uniqueness.PointRestriction (fieldModule fieldTower field_scalar field_smul_formula)
open Representation.SL2FourNatural (F)

noncomputable section

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry
namespace Native

abbrev Group := actionGroup

noncomputable def representation : Representation (ZMod 2) Group BinarySpace :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    ((Units.coeHom Matrix12).comp actionGroup.subtype)

def componentInclusion : M22TripleCover →* Group :=
  Subgroup.inclusion derivedGroup_le_actionGroup

theorem representation_component (g : M22TripleCover) (v : BinarySpace) :
    representation (componentInclusion g) v = binaryRepresentation g v := rfl

theorem representation_faithful : Function.Injective representation := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  exact Matrix.toLinAlgEquiv'.injective he

def centralScalar : Group := componentInclusion scalar

def outerInvolution : Group := ⟨unitC, unitC_mem_actionGroup⟩

theorem centralScalar_cube : centralScalar ^ 3 = 1 := by
  change componentInclusion scalar ^ 3 = 1
  rw [← map_pow, coreScalar_pow_three, map_one]

theorem outerInvolution_square : outerInvolution * outerInvolution = 1 := by
  apply Subtype.ext
  exact (pow_two unitC).symm.trans unitC_pow_two

theorem outerInvolution_inverts :
    outerInvolution * centralScalar = centralScalar ^ 2 * outerInvolution := by
  apply Subtype.ext
  exact (mul_inv_eq_iff_eq_mul.mp unitC_conj_scalarUnit)

theorem centralScalar_quadratic :
    representation centralScalar ^ 2 + representation centralScalar + 1 = 0 :=
  scalar_operator_quadratic

theorem centralScalar_fixed_iff (v : BinarySpace) :
    representation centralScalar v = v ↔ v = 0 := scalar_fixed_iff v

local instance : Module F BinarySpace :=
  fieldModule binaryRepresentation binaryRepresentation_faithful
local instance : IsScalarTower (ZMod 2) F BinarySpace :=
  fieldTower binaryRepresentation binaryRepresentation_faithful

noncomputable def fieldPoint (v : BinarySpace) : Submodule F BinarySpace :=
  Submodule.span F {v}

noncomputable def binaryPoint (v : BinarySpace) : Submodule (ZMod 2) BinarySpace :=
  (fieldPoint v).restrictScalars (ZMod 2)

def binaryLine (v : BinarySpace) : Submodule (ZMod 2) BinarySpace :=
  Submodule.span (ZMod 2) {v}

theorem binaryLine_le_point (v : BinarySpace) : binaryLine v ≤ binaryPoint v := by
  apply Submodule.span_le.mpr
  intro w hw
  rw [Set.mem_singleton_iff.mp hw]
  exact Submodule.mem_span_singleton_self v

theorem centralScalar_smul (v : BinarySpace) :
    representation centralScalar v = (QuadraticAlgebra.omega : F) • v :=
  field_scalar binaryRepresentation binaryRepresentation_faithful v

theorem centralScalar_pow_smul (n : ℕ) (v : BinarySpace) :
    representation (centralScalar ^ n) v = (QuadraticAlgebra.omega : F) ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, map_mul, Module.End.mul_apply, centralScalar_smul]
    rw [← centralScalar_smul, ← Module.End.mul_apply, ← map_mul, ← pow_succ,
      pow_succ', map_mul, Module.End.mul_apply, ih, centralScalar_smul,
      smul_smul, pow_succ']

private theorem neg_eq_self (v : BinarySpace) : -v = v := by
  rw [← neg_one_smul (ZMod 2), show (-1 : ZMod 2) = 1 by decide, one_smul]

theorem scalar_moved_line_eq_point (v : BinarySpace) :
    subspaceCommutator representation (binaryLine v) (zpowers centralScalar) =
      binaryPoint v := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro w ⟨a, ha, u, hu, rfl⟩
    have hf : IsOfFinOrder centralScalar :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by decide, centralScalar_cube⟩
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp
      (hf.mem_zpowers_iff_mem_range_orderOf.mp ha)
    rw [centralScalar_pow_smul]
    exact (fieldPoint v).sub_mem
      ((fieldPoint v).smul_mem _ (binaryLine_le_point v hu)) (binaryLine_le_point v hu)
  · let M := subspaceCommutator representation (binaryLine v) (zpowers centralScalar)
    have h₁ : representation centralScalar v - v ∈ M :=
      Submodule.subset_span ⟨centralScalar, mem_zpowers centralScalar, v,
        Submodule.mem_span_singleton_self v, rfl⟩
    have h₂ : representation (centralScalar ^ 2) v - v ∈ M :=
      Submodule.subset_span ⟨centralScalar ^ 2, (zpowers centralScalar).pow_mem
        (mem_zpowers centralScalar) 2, v, Submodule.mem_span_singleton_self v, rfl⟩
    have he : (representation centralScalar v - v) +
        (representation (centralScalar ^ 2) v - v) = v := by
      have hq := LinearMap.congr_fun centralScalar_quadratic v
      change representation centralScalar (representation centralScalar v) +
        representation centralScalar v + v = 0 at hq
      have hs : representation centralScalar (representation centralScalar v) +
          representation centralScalar v = v := by
        exact (eq_neg_of_add_eq_zero_left hq).trans (neg_eq_self v)
      rw [map_pow, pow_two, Module.End.mul_apply]
      have hz : v + v = 0 := by
        simpa only [show (2 : ZMod 2) = 0 by decide, zero_smul] using
          (two_smul (ZMod 2) v).symm
      calc
        _ = (representation centralScalar (representation centralScalar v) +
            representation centralScalar v) - (v + v) := by abel
        _ = v := by rw [hs, hz, sub_zero]
    have hv : v ∈ M := he ▸ M.add_mem h₁ h₂
    have hsv : representation centralScalar v ∈ M := by
      simpa only [sub_add_cancel] using M.add_mem h₁ hv
    intro w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [field_smul_formula]
    exact M.add_mem (M.smul_mem a.re hv) (M.smul_mem a.im hsv)

theorem fieldPoint_finrank {v : BinarySpace} (hv : v ≠ 0) :
    Module.finrank F (fieldPoint v) = 1 :=
  finrank_span_singleton hv

theorem binaryPoint_card {v : BinarySpace} (hv : v ≠ 0) :
    Nat.card (binaryPoint v) = 4 := by
  change Nat.card (fieldPoint v) = 4
  rw [Module.natCard_eq_pow_finrank (K := F), fieldPoint_finrank hv,
    Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field, pow_one]

theorem binaryPoint_finrank {v : BinarySpace} (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (binaryPoint v) = 2 := by
  have h := Module.finrank_mul_finrank (ZMod 2) F (fieldPoint v)
  rw [QuadraticAlgebra.finrank_eq_two, fieldPoint_finrank hv] at h
  exact h.symm.trans (by norm_num)

end Native
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry
