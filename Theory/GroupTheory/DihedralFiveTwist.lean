module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Algebra.Group.Subgroup.MulOpposite
public import Mathlib.Tactic

/-!
# Centralizing twists of involutions normalizing D₁₀

An automorphism of D₁₀ whose square is the identity sends the marked
rotation to itself or its inverse. Thus an involution t normalizing D₁₀
and commuting with a marked reflection v has either t or tv centralizing
D₁₀. Commutation with v preserves the square-one relation.

The rotation calculation uses only the five possible exponents, checked
by the kernel. All embeddings and the ambient conjugation are retained.
This supplies the dihedral selection in Aschbacher–Smith, Proposition
8.2.8(6), printed p.719 (PDF p.736 of refs/quasithin.pdf), with its actual
quotient application in TensorRecognition.CodeInputs.
-/

public section

namespace DihedralGroup
private theorem automorphism_square_rotation (a : MulAut (DihedralGroup 5))
    (ha : ∀ d, a (a d) = d) : a (r 1) = r 1 ∨ a (r 1) = (r 1)⁻¹ := by
  have ho := a.orderOf_eq (r 1)
  cases he : a (r 1) with
  | sr i => simp only [he, orderOf_sr, orderOf_r_one] at ho; omega
  | r i =>
    have hpow : a (r i) = r i ^ i.val := by
      calc
        a (r i) = a ((r 1) ^ i.val) := by rw [r_one_pow, ZMod.natCast_zmod_val]
        _ = a (r 1) ^ i.val := map_pow a _ _
        _ = r i ^ i.val := by rw [he]
    have hh : r i ^ i.val = (r 1 : DihedralGroup 5) := (hpow.symm.trans (by rw [← he, ha]))
    have hh' : i * (i.val : ZMod 5) = 1 := r.inj (by simpa only [r_pow] using hh)
    have hi : i = 1 ∨ i = -1 := by
      exact (show ∀ j : ZMod 5, j * (j.val : ZMod 5) = 1 → j = 1 ∨ j = -1 by decide +kernel) i hh'
    rcases hi with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

end DihedralGroup

namespace Subgroup
variable {G : Type*} [Group G]
private theorem exists_twist_centralizing_rotation (D : Subgroup G) (e : D ≃* DihedralGroup 5) (t : G)
    (ht : t ∈ normalizer (D : Set G)) (ht2 : t ^ 2 = 1)
    (hc : Commute t (e.symm (.sr 0) : G)) :
    ∃ s : G, (s = t ∨ s = t * (e.symm (.sr 0) : G)) ∧ s ^ 2 = 1 ∧
      Commute s (e.symm (.r 1) : G) := by
  let a : MulAut (DihedralGroup 5) :=
    (e.symm.trans (D.normalizerMonoidHom ⟨t, ht⟩)).trans e
  have ha (d) : a (a d) = d := by
    change e (D.normalizerMonoidHom ⟨t, ht⟩
      (e.symm (e (D.normalizerMonoidHom ⟨t, ht⟩ (e.symm d))))) = d
    rw [e.symm_apply_apply]
    apply e.symm.injective
    rw [e.symm_apply_apply]
    apply Subtype.ext
    change t * (t * (e.symm d : G) * t⁻¹) * t⁻¹ = (e.symm d : G)
    have htt : t * t = 1 := by simpa only [pow_two] using ht2
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    rw [hti]
    calc
      _ = (t * t) * (e.symm d : G) * (t * t) := by group
      _ = _ := by rw [htt, one_mul, mul_one]
  have hrot := DihedralGroup.automorphism_square_rotation a ha
  let x : G := e.symm (.r 1)
  let v : G := e.symm (.sr 0)
  have hx (d) : (e.symm (a d) : G) = t * (e.symm d : G) * t⁻¹ := by
    change (e.symm (e (D.normalizerMonoidHom ⟨t, ht⟩ (e.symm d))) : G) = _
    rw [e.symm_apply_apply]
    rfl
  have hv : v * x * v⁻¹ = x⁻¹ := by
    change ((e.symm (.sr 0) * e.symm (.r 1) * (e.symm (.sr 0))⁻¹ : D) : G) = _
    rw [← map_inv, ← map_mul, ← map_mul]
    have hr : (DihedralGroup.sr 0 * .r 1 * (.sr 0)⁻¹ : DihedralGroup 5) = (.r 1)⁻¹ := by simp
    rw [hr, map_inv]
    rfl
  have hv2 : v ^ 2 = 1 := by
    change ((e.symm (.sr 0) ^ 2 : D) : G) = _
    rw [← map_pow]
    have hh : (DihedralGroup.sr 0 : DihedralGroup 5)^2 = 1 := by simp [pow_two]
    rw [hh, map_one]
    rfl
  rcases hrot with hrot | hrot
  · refine ⟨t, Or.inl rfl, ht2, ?_⟩
    have hh : t * x * t⁻¹ = x := by rw [← hx, hrot]
    exact (mul_inv_eq_iff_eq_mul.mp hh)
  · refine ⟨t * v, Or.inr rfl, ?_, ?_⟩
    · rw [hc.mul_pow, ht2, hv2, one_mul]
    · have hh : t * x * t⁻¹ = x⁻¹ := by rw [← hx, hrot, map_inv]; rfl
      show (t * v) * x = x * (t * v)
      calc
        _ = t * (v * x * v⁻¹) * v := by group
        _ = t * x⁻¹ * v := by rw [hv]
        _ = (t * x * t⁻¹)⁻¹ * (t * v) := by group
        _ = x * (t * v) := by rw [hh, inv_inv]
/-- An involution normalizing D₁₀ and fixing its marked reflection can be
multiplied by that reflection to centralize the whole dihedral group. The
chosen element still has square one. -/
theorem exists_involution_twist_centralizing_dihedral_five
    (D : Subgroup G) (e : D ≃* DihedralGroup 5) (t : G)
    (ht : t ∈ normalizer (D : Set G)) (ht2 : t ^ 2 = 1)
    (hc : Commute t (e.symm (.sr 0) : G)) :
    ∃ s : G, (s = t ∨ s = t * (e.symm (.sr 0) : G)) ∧ s ^ 2 = 1 ∧
      ∀ d : D, Commute s (d : G) := by
  obtain ⟨s, hs, hs2, hsx⟩ := exists_twist_centralizing_rotation D e t ht ht2 hc
  have hsv : Commute s (e.symm (.sr 0) : G) := by
    rcases hs with rfl | rfl
    · exact hc
    · exact hc.mul_left (Commute.refl _)
  refine ⟨s, hs, hs2, ?_⟩
  intro d
  obtain ⟨a, rfl⟩ := e.symm.surjective d
  have hr (i : ZMod 5) :
      (e.symm (.r i) : G) = (e.symm (.r 1) : G) ^ i.val := by
    change (D.subtype.comp e.symm.toMonoidHom) (.r i) = _
    rw [show (DihedralGroup.r i : DihedralGroup 5) = (.r 1) ^ i.val by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val], map_pow]
    rfl
  cases a with
  | r i => rw [hr]; exact hsx.pow_right _
  | sr i =>
    have hsr : (DihedralGroup.sr i : DihedralGroup 5) = .sr 0 * .r i := by simp
    rw [hsr, map_mul, coe_mul, hr]
    exact hsv.mul_right (hsx.pow_right _)

end Subgroup

