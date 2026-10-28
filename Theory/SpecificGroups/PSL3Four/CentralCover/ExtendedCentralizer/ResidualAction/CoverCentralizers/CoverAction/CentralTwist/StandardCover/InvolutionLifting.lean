module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InvolutionClasses.RootCoverage
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraphField.Monomial

/-!
# Involution lifting through elementary central kernels of PSL₃(4)

All projective involutions are conjugate: the root-coverage theorem puts each
in the highest-root group, and a determinant-one diagonal matrix scales its
nonzero parameter to one. In a central extension with kernel of exponent two,
squares are independent of the lift and invariant under projective conjugacy.

The first root plane contains three independent binary vectors. The seven
nonzero products of chosen lifts therefore have a common central square.
The commutator product identity forces that square to be one. Consequently
every lift of every projective involution is an involution. Perfectness and a
multiplier presentation are not needed for this elementary argument.

Source: Aschbacher--Smith I.2.2(3b), printed pp.409--410; the four-cover use in
15.3.38, printed pp.1136--1137, combined manuscript of 1 March 2004.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.CentralTwist
private theorem comm_of_equal_squares {G : Type*} [Group G] (x y t : G)
    (ht : t ∈ center G) (ht2 : t ^ 2 = 1)
    (hx : x ^ 2 = t) (hy : y ^ 2 = t) (hxy : (x * y) ^ 2 = t) :
    ⁅x, y⁆ = t := by
  have hi (u : G) (hu : u ^ 2 = t) : u⁻¹ = u * t := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, ← pow_two, hu, ← pow_two, ht2]
  rw [commutatorElement_def, hi x hx, hi y hy]
  calc
    x * y * (x * t) * (y * t) = x * y * x * (t * y) * t := by group
    _ = x * y * x * (y * t) * t := by rw [← mem_center_iff.mp ht y]
    _ = (x * y) ^ 2 * t ^ 2 := by simp only [pow_two]; group
    _ = t := by rw [hxy, ht2, mul_one]

private theorem seven_squares {G : Type*} [Group G] (x y z t : G)
    (ht : t ∈ center G) (ht2 : t ^ 2 = 1)
    (hx : x ^ 2 = t) (hy : y ^ 2 = t) (hz : z ^ 2 = t)
    (hxy : (x * y) ^ 2 = t) (hxz : (x * z) ^ 2 = t)
    (hyz : (y * z) ^ 2 = t) (hxyz : (x * (y * z)) ^ 2 = t) : t = 1 := by
  have h1 := comm_of_equal_squares x y t ht ht2 hx hy hxy
  have h2 := comm_of_equal_squares x z t ht ht2 hx hz hxz
  have h3 := comm_of_equal_squares x (y*z) t ht ht2 hx hyz hxyz
  rw [commutatorElement_mul_right_eq_mul_conj, h1, h2,
    mul_assoc t y t, mem_center_iff.mp ht y, ← mul_assoc,
    mul_inv_cancel_right, ← pow_two, ht2] at h3
  exact h3.symm

private theorem square_eq_of_same_image {G B : Type*} [Group G] [Group B]
    (f : G →* B) (hc : f.ker ≤ center G) (hs : ∀ z ∈ f.ker, z ^ 2 = 1)
    (x y : G) (h : f x = f y) : x ^ 2 = y ^ 2 := by
  have hk : x * y⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have hcomm : Commute (x * y⁻¹) y := (mem_center_iff.mp (hc hk) y).symm
  have hh := hcomm.mul_pow 2
  simpa only [inv_mul_cancel_right, hs _ hk, one_mul] using hh

private theorem square_eq_of_conjugate_image {G B : Type*} [Group G] [Group B]
    (f : G →* B) (hf : Function.Surjective f)
    (hc : f.ker ≤ center G) (hs : ∀ z ∈ f.ker, z ^ 2 = 1)
    (x y : G) (hx : f x ^ 2 = 1) (h : IsConj (f x) (f y)) : x ^ 2 = y ^ 2 := by
  obtain ⟨b, hb⟩ := isConj_iff.mp h
  obtain ⟨v, rfl⟩ := hf b
  have he : f (v * x * v⁻¹) = f y := by simpa only [map_mul, map_inv] using hb
  have hxc : x ^ 2 ∈ center G := hc (by rw [MonoidHom.mem_ker, map_pow]; exact hx)
  calc
    x ^ 2 = (v * x * v⁻¹) ^ 2 := by
      rw [show (v * x * v⁻¹) ^ 2 = v * x ^ 2 * v⁻¹ by simp [pow_two, mul_assoc],
        mem_center_iff.mp hxc v, mul_inv_cancel_right]
    _ = y ^ 2 := square_eq_of_same_image f hc hs _ _ he

open PSL3Even.UnipotentGeometry
private theorem projective_involution_conjugate_root_one (v : PSL)
    (hv : v ^ 2 = 1) (hne : v ≠ 1) :
    IsConj v (projective F ⟨0,0,1⟩) := by
  obtain ⟨b, hb⟩ := InvolutionClasses.projective_conjugate_root v hv
  obtain ⟨t, ht⟩ := (mem_projectiveCenter F _).mp hb
  have ht0 : t ≠ 0 := by
    intro he
    subst t
    have hu : projective F ⟨0,0,0⟩ = 1 := (projective F).map_one
    rw [hu] at ht
    have he : v = 1 := by
      have hh := congrArg (fun u : PSL => b⁻¹ * u * b) ht
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, mul_one, inv_mul_cancel]
        using hh.symm
    exact hne he
  let d : SL := ⟨!![t⁻¹,0,0; 0,t,0; 0,0,1], by simp [Matrix.det_fin_three, ht0]⟩
  have hd : d * specialLinear F ⟨0,0,t⟩ = specialLinear F ⟨0,0,1⟩ * d := by
    apply Subtype.ext
    change d.val * matrix F ⟨0,0,t⟩ = matrix F ⟨0,0,1⟩ * d.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [d, matrix, Matrix.mul_apply, Fin.sum_univ_three, ht0]
  have hp := congrArg (QuotientGroup.mk' (center SL)) hd
  change (d : PSL) * projective F ⟨0,0,t⟩ = projective F ⟨0,0,1⟩ * (d : PSL) at hp
  apply isConj_iff.mpr
  refine ⟨(d : PSL) * b, ?_⟩
  calc
    ((d : PSL) * b) * v * ((d : PSL) * b)⁻¹ =
      (d : PSL) * (b * v * b⁻¹) * (d : PSL)⁻¹ := by group
    _ = projective F ⟨0,0,1⟩ := by rw [← ht, hp, mul_inv_cancel_right]

private theorem projective_involutions_conjugate (u v : PSL)
    (hu : u ^ 2 = 1) (hu1 : u ≠ 1) (hv : v ^ 2 = 1) (hv1 : v ≠ 1) : IsConj u v :=
  (projective_involution_conjugate_root_one u hu hu1).trans
    (projective_involution_conjugate_root_one v hv hv1).symm

private theorem axis_mul (s t u v : F) :
    projective F ⟨s,0,t⟩ * projective F ⟨u,0,v⟩ = projective F ⟨s+u,0,t+v⟩ := by
  rw [← map_mul]
  congr 1
  apply U.ext <;> simp

/-- Every lift of a projective element of square one has square one when the
central kernel has exponent two. -/
theorem square_eq_one_of_elementary_kernel {E : Type*} [Group E]
    (f : E →* PSL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hs : ∀ z ∈ f.ker, z ^ 2 = 1)
    (x : E) (hx : (f x) ^ 2 = 1) : x ^ 2 = 1 := by
  by_cases hxe : f x = 1
  · exact hs x hxe
  have hsame (s t : F) (hst : s ≠ 0 ∨ t ≠ 0) (y : E)
      (hy : f y = projective F ⟨s,0,t⟩) : y ^ 2 = x ^ 2 := by
    apply square_eq_of_conjugate_image f hf hc hs
    · rw [hy, ← map_pow, (square_eq_one_iff F _).mpr (Or.inr rfl), map_one]
    · apply projective_involutions_conjugate
      · rw [hy, ← map_pow, (square_eq_one_iff F _).mpr (Or.inr rfl), map_one]
      · intro he
        have he' : (⟨s,0,t⟩ : U F) = 1 :=
          projective_injective F ((hy.symm.trans he).trans (map_one _).symm)
        rcases hst with h | h
        · exact h (congrArg U.x he')
        · exact h (congrArg U.c he')
      · exact hx
      · exact hxe
  obtain ⟨y, hy⟩ := hf (projective F ⟨1,0,0⟩)
  obtain ⟨z, hz⟩ := hf (projective F ⟨ProjectiveGraphField.omega,0,0⟩)
  obtain ⟨w, hw⟩ := hf (projective F ⟨0,0,1⟩)
  have hxk : x ^ 2 ∈ f.ker := by rw [MonoidHom.mem_ker, map_pow]; exact hx
  have homega : (1 : F) + ProjectiveGraphField.omega ≠ 0 := by
    intro he
    have hh := add_eq_zero_iff_eq_neg.mp he
    rw [CharTwo.neg_eq] at hh
    exact ProjectiveGraphField.omega_ne_one hh.symm
  apply seven_squares y z w (x ^ 2) (hc hxk) (hs _ hxk)
  · exact hsame 1 0 (Or.inl one_ne_zero) y hy
  · exact hsame _ 0 (Or.inl ProjectiveGraphField.omega_ne_zero) z hz
  · exact hsame 0 1 (Or.inr one_ne_zero) w hw
  · apply hsame _ 0 (Or.inl homega)
    rw [map_mul, hy, hz, axis_mul, zero_add]
  · apply hsame 1 1 (Or.inr one_ne_zero)
    rw [map_mul, hy, hw, axis_mul, add_zero, zero_add]
  · apply hsame _ 1 (Or.inr one_ne_zero)
    rw [map_mul, hz, hw, axis_mul, add_zero, zero_add]
  · apply hsame _ 1 (Or.inr one_ne_zero)
    rw [map_mul, map_mul, hy, hz, hw, axis_mul, axis_mul, add_zero, zero_add, zero_add]

end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.CentralTwist
