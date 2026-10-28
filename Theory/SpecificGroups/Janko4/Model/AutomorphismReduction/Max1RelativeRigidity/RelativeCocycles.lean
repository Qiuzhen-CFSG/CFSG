module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.RelativeCocycles.WordSoundness
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.RelativeCocycles.Constraints

import Mathlib.Tactic.Group

/-!
# Relative rigidity in the actual ATLAS max1 subgroup of J₄

An automorphism fixing the elementary kernel pointwise has a right displacement
cocycle in that kernel. If its displacement on `C_M(v)` lies in `⟨v⟩`, the five
checked stabilizer words force its two generator displacements to be `(0,0)`
or `(0,6)`. These are exactly the displacements of conjugation by one or v.
The actual two-generator extensionality theorem completes the argument.

The finite constraints are proved here, without assuming vanishing of the
whole first cohomology group or innerness of any larger automorphism group.
Source: literal ATLAS `J4G1-max1W1`; local motivation: GLS3 Table 5.3i.
-/
@[expose] public section
namespace Janko4.Max1RelativeRigidity
open RelativeCocycles
open Cardinality Cardinality.KernelCount
attribute [local irreducible] basis modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

private lemma aut_ext_delta (phi psi : MulAut M)
    (hx : delta phi x = delta psi x) (hy : delta phi y = delta psi y) : phi = psi := by
  apply aut_ext phi psi
  · exact mul_left_cancel hx
  · exact mul_left_cancel hy

private lemma delta_conj_one (g : M) : delta (MulAut.conj 1) g = eval 0 := by
  change g⁻¹ * (1 * g * (1 : M)⁻¹) = eval 0
  simpa only [inv_one, one_mul, mul_one, inv_mul_cancel] using eval_zero.symm

private lemma delta_conj_v_x : delta (MulAut.conj v) x = eval 0 := by
  change x⁻¹ * (v * x * v⁻¹) = _
  rw [← eval_three, eval_inv]
  calc
    x⁻¹ * (eval 3 * x * eval 3) = (x⁻¹ * eval 3 * x) * eval 3 := by group
    _ = eval (actX 3 ^^^ 3) := by rw [eval_xor, eval_actX]
    _ = eval 0 := by congr 1

private lemma delta_conj_v_y : delta (MulAut.conj v) y = eval 6 := by
  change y⁻¹ * (v * y * v⁻¹) = _
  rw [← eval_three, eval_inv]
  calc
    y⁻¹ * (eval 3 * y * eval 3) = (y⁻¹ * eval 3 * y) * eval 3 := by group
    _ = eval (actY 3 ^^^ 3) := by rw [eval_xor, eval_actY]
    _ = eval 6 := by congr 1

/-- A pointwise kernel fixer whose displacement on `C_M(v)` lies in `⟨v⟩`
is conjugation by either one or the actual kernel element `v`. -/
theorem relative_cocycle_rigidity (phi : MulAut M)
    (hfix : ∀ e : K, phi (e : M) = (e : M))
    (hrelative : ∀ h : M, Commute h v → h⁻¹ * phi h ∈ Subgroup.zpowers v) :
    ∃ epsilon : Fin 2, phi = MulAut.conj (v ^ epsilon.val) := by
  obtain ⟨a, ha⟩ := eval_surjective ⟨delta phi x, displacement_mem phi hfix x⟩
  obtain ⟨b, hb⟩ := eval_surjective ⟨delta phi y, displacement_mem phi hfix y⟩
  have ha' : delta phi x = eval a := ha.symm
  have hb' : delta phi y = eval b := hb.symm
  have hc := relative_word_constraint phi a b ha' hb' hrelative
  obtain ⟨rfl, hb0 | hb6⟩ := five_word_constraints a b
    (hc word0 word0_fixes) (hc word1 word1_fixes) (hc word2 word2_fixes)
    (hc word3 word3_fixes) (hc word4 word4_fixes)
  · refine ⟨0, ?_⟩
    change phi = MulAut.conj (v ^ (0 : ℕ))
    rw [pow_zero]
    apply aut_ext_delta
    · exact ha'.trans (delta_conj_one x).symm
    · exact (hb'.trans (congrArg eval hb0)).trans (delta_conj_one y).symm
  · refine ⟨1, ?_⟩
    change phi = MulAut.conj (v ^ (1 : ℕ))
    rw [pow_one]
    apply aut_ext_delta
    · exact ha'.trans delta_conj_v_x.symm
    · exact (hb'.trans (congrArg eval hb6)).trans delta_conj_v_y.symm

end Janko4.Max1RelativeRigidity
