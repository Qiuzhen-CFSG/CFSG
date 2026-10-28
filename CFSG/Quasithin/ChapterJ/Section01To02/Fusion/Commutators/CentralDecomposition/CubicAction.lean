module

public import CFSG.Quasithin.ChapterJ.Defs
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

/-!
# Cubic fixed points in the marked natural action

A determinant-one matrix fixing the first basis vector is upper unipotent,
so its square is one in characteristic two. Completing any nonzero vector
to a determinant-one matrix gives the same conclusion for its stabilizer.
An element of order three therefore fixes only zero. The alternating-group
marking in `L2FourAction` transports this fact to the actual S₅ action.

Equivariance then puts centralizers of a cubic image in the literal kernel
of a natural section. The central decomposition applies this to Q/HC and
to Ru2's U/Z; no fixed-space assumption is added to either section.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, J.2.2(3)
and J.2.4, printed pp.432–434 (PDF pp.443–445).
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ
open Subgroup Representation
open Representation.SL2FourNatural

namespace CubicNatural
private theorem stabilizer_standard_square (g : SL) (hg : action g ![1, 0] = ![1, 0]) :
    g ^ 2 = 1 := by
  have h00 : g.val 0 0 = 1 := by
    simpa [action_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hg 0
  have h10 : g.val 1 0 = 0 := by
    simpa [action_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hg 1
  have h11 : g.val 1 1 = 1 := by
    have hd : Matrix.det g.val = 1 := g.property
    rw [Matrix.det_fin_two, h00, h10] at hd
    simpa using hd
  apply Subtype.ext
  simp only [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h10, h11,
      CharTwo.add_self_eq_zero]

private theorem fixed_square (g : SL) {v : V} (hv : v ≠ 0) (hg : action g v = v) :
    g ^ 2 = 1 := by
  obtain ⟨a, ha⟩ := exists_first_column v hv
  have hfix : action (a⁻¹ * g * a) ![1, 0] = ![1, 0] := by
    simp only [map_mul, LinearEquiv.mul_apply, ha, hg]
    rw [← ha]
    simp
  have hh := stabilizer_standard_square (a⁻¹ * g * a) hfix
  have he : (a⁻¹ * g * a) ^ 2 = a⁻¹ * g ^ 2 * a := by simp only [pow_two]; group
  rw [he] at hh
  have := congrArg (fun x : SL => a * x * a⁻¹) hh
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_one,
    mul_inv_cancel] using this

private theorem cubic_fixed (g : SL) (h3 : g ^ 3 = 1) (hne : g ≠ 1)
    {v : V} (hv : action g v = v) : v = 0 := by
  by_contra hn
  have h2 := fixed_square g hn hv
  apply hne
  simpa [pow_succ, h2] using h3
end CubicNatural

/-- A cubic permutation has no nonzero fixed vector in the marked natural action. -/
theorem L2FourAction.cubic_fixed_eq_zero (r : L2FourAction) {g : S5}
    (hg : orderOf g = 3) {v : FourSpace} (hv : r.action g v = v) : v = 0 := by
  have hg3 : g ^ 3 = 1 := by rw [← hg, pow_orderOf_eq_one]
  have hsign : Equiv.Perm.sign g = 1 := by
    have hs : (Equiv.Perm.sign g) ^ 3 = 1 := by
      rw [← map_pow, hg3, map_one]
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, Int.units_pow_two, one_mul] at hs
    exact hs
  let a : SL2FourNatural.SL := r.marking.symm ⟨g, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩
  have ha : (r.marking a : S5) = g := congrArg Subtype.val (r.marking.apply_symm_apply _)
  have ha3 : a ^ 3 = 1 := by
    apply r.marking.injective
    apply Subtype.ext
    simpa only [map_pow, Subgroup.coe_pow, ha, map_one, Subgroup.coe_one] using hg3
  have hane : a ≠ 1 := by
    intro he
    have hg1 : g = 1 := by simpa only [he, map_one, Subgroup.coe_one] using ha.symm
    rw [hg1, orderOf_one] at hg
    omega
  apply CubicNatural.cubic_fixed a ha3 hane
  rw [← r.restriction, ha]
  exact hv

variable {G : Type*} [Group G]
/-- Fixed elements lift into the literal kernel of a marked natural section. -/
theorem L2FourAction.centralizer_le_kernel_of_cubic_image {H A C B : Subgroup G}
    (r : L2FourAction) (q : H →* S5)
    (s : BinaryConjugationSection H A C (r.action.comp q))
    (hBH : B ≤ H) (b : B) (hb : orderOf (q ⟨b, hBH b.property⟩) = 3) :
    A ⊓ centralizer (B : Set G) ≤ C := by
  intro a ha
  apply (s.coordinates_eq_one_iff ⟨a, ha.1⟩).mp
  apply Multiplicative.toAdd.injective
  change (s.coordinates ⟨a, ha.1⟩).toAdd = 0
  apply r.cubic_fixed_eq_zero hb
  have he := s.equivariant ⟨b, hBH b.property⟩ ⟨a, ha.1⟩
  have hc : (b : G) * a * (b : G)⁻¹ = a := by
    rw [ha.2 b b.property, mul_inv_cancel_right]
  have hx : (⟨(b : G) * a * (b : G)⁻¹,
      (mem_normalizer_iff.mp (s.normalized (hBH b.property)) a).mp ha.1⟩ : A) =
      ⟨a, ha.1⟩ := Subtype.ext hc
  rw [hx] at he
  exact he.symm
end CFSG.Quasithin.ChapterJ
