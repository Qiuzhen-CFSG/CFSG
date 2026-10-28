module
public import Theory.SpecificGroups.Rudvalis.Model.CubicElementary.Marked
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
import all Theory.SpecificGroups.Rudvalis.Model.PointCoreBound

/-!
# A quaternion subgroup centralizing the marked Rudvalis cubic

Eight explicit coordinates in the certified Sylow normal forms give an
injective homomorphism from Q₈ to the native Rudvalis carrier. The existing
two-point decoder verifies its multiplication. Full permutation checks for
the two quaternion generators show that its image centralizes the aligned
max6 cubic; the remaining elements follow from the homomorphism laws.

This intentional internal extension imports PointCoreBound's private decoder
and involution alignment without changing that module's public boundary.
Its core membership and conjugacy transport are proved in the companion
modules. The actual source consumer is Chapter13's original odd-actor pair.
Source: Aschbacher--Smith J.2.3(7), p.433, and 4.2.13, pp.611--612.
The original ATLAS words, left-action convention and attribution are retained
in SylowOvergroups.Definitions and LocalOrder/source/Generate.py.
-/

public section
namespace Rudvalis.PointQuaternion
open Subgroup SylowOvergroups
open SylowOvergroups.RadicalCoverage.SylowCertificate
open SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder
open SylowOvergroups.RadicalCoverage.LocalCover
open Max6Certificate CoreQuotients.Max6Blocks
open PointCoreBound
set_option maxRecDepth 30000
set_option Elab.async false

private def index : QuaternionGroup 2 → Fin 16384
  | .a i => ![0,1148,6144,7292] ⟨i.val,i.val_lt⟩
  | .xa i => ![3772,10944,5820,12992] ⟨i.val,i.val_lt⟩

private theorem index_injective : Function.Injective index := by decide +kernel

private theorem mul_check : ∀ a b : QuaternionGroup 2,
    normalMap (index (a*b)) 0 = normalMap (index a) (normalMap (index b) 0) ∧
    normalMap (index (a*b)) 1 = normalMap (index a) (normalMap (index b) 1) := by
  decide +kernel


/-- An actual quaternion group in the marked Rudvalis Sylow subgroup. -/
def embedding : QuaternionGroup 2 →* Model where
  toFun a := candidateNormalForm (index a)
  map_one' := by
    apply candidate_ext _ _ (candidateNormalForm_mem _) candidate.one_mem
    · rw [normal_smul,one_smul]; decide +kernel
    · rw [normal_smul,one_smul]; decide +kernel
  map_mul' a b := by
    apply candidate_ext _ _ (candidateNormalForm_mem _)
      (candidate.mul_mem (candidateNormalForm_mem _) (candidateNormalForm_mem _))
    · simpa only [mul_smul,normal_smul] using (mul_check a b).1
    · simpa only [mul_smul,normal_smul] using (mul_check a b).2

theorem embedding_injective : Function.Injective embedding := by
  intro a b h
  exact index_injective (normalForm_injective h)

private theorem embedding_smul (a : QuaternionGroup 2) (x : Fin 4060) :
    embedding a • x = normalMap (index a) x := normal_smul _ _

private def cubicMap (x : Fin 4060) : Fin 4060 :=
  AlignmentData.gapPerm.symm ((((LocalCardinality.Max6.L0.gen 0)^2 *
    LocalCardinality.Max6.L0.gen 1)^2) (AlignmentData.gapPerm x))

private theorem cubic_smul (x : Fin 4060) :
    MulAut.conj conjugator CubicElementary.cubic • x = cubicMap x := by
  change (conjugator.val * CubicElementary.cubic.val * conjugator.val⁻¹) x = _
  rw [conjugator_val,CubicElementary.cubic_val]
  rfl

private theorem commutation_check_a : ∀ x : Fin 4060,
    normalMap 1148 (cubicMap x) = cubicMap (normalMap 1148 x) := by
  apply Data.allFin
  decide +kernel


private theorem commutation_check_xa : ∀ x : Fin 4060,
    normalMap 3772 (cubicMap x) = cubicMap (normalMap 3772 x) := by
  apply Data.allFin
  decide +kernel


/-- The marked quaternion centralizes the conjugate of the actual max6 cubic. -/
theorem embedding_commutes (a : QuaternionGroup 2) :
    Commute (embedding a) (MulAut.conj conjugator CubicElementary.cubic) := by
  have hgen (u : QuaternionGroup 2)
      (h : ∀ x : Fin 4060, normalMap (index u) (cubicMap x) =
        cubicMap (normalMap (index u) x)) :
      Commute (embedding u) (MulAut.conj conjugator CubicElementary.cubic) := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change (embedding u * MulAut.conj conjugator CubicElementary.cubic) • x =
      (MulAut.conj conjugator CubicElementary.cubic * embedding u) • x
    simpa only [mul_smul,embedding_smul,cubic_smul] using h x
  have ha := hgen (.a 1) commutation_check_a
  have hb := hgen (.xa 0) commutation_check_xa
  have hforms : ∀ u : QuaternionGroup 2, ∃ k : Fin 4,
      u = (QuaternionGroup.a 1)^k.val ∨
        u = QuaternionGroup.xa 0 * (QuaternionGroup.a 1)^k.val := by decide +kernel
  obtain ⟨k,hk | hk⟩ := hforms a
  · rw [hk,map_pow]
    exact ha.pow_left _
  · rw [hk,map_mul,map_pow]
    exact hb.mul_left (ha.pow_left _)

end Rudvalis.PointQuaternion
