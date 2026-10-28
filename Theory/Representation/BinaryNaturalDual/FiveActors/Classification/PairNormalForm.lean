module

public import Theory.Representation.BinaryNaturalDual.FiveActors.Classification.PairModel
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Normal form for a nonquadratic commuting involution pair in GL₅(2)

For the displacement maps `x = s - 1` and `y = t - 1`, a vector `v` with
`x (y v) ≠ 0` generates four independent vectors `(v, xv, yv, xyv)`.
Extend these to a basis. Square-zero forces the image of its fifth vector
under each displacement into the first four dimensions. Commutation makes
the leading coefficients equal, so subtracting a linear combination of
`v`, `xv`, and `yv` makes that fifth vector fixed by both operators.
The coordinate equivalence of this adjusted basis is the actual conjugator
to `regularS` and `regularT` from `PairModel`.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
H.9.2(3), printed pp.390–391 (PDF pp.401–402). This linear-algebra argument
supplies the pair-normal-form input to the alternative high-rank actor
placement proof; it does not assume radical placement or pair classification.
-/

open Module
namespace BinaryNaturalDual.FiveActors.Classification

private theorem regular_four_independent
    (x y : X →ₗ[ZMod 2] X)
    (hx : ∀ u, x (x u) = 0) (hy : ∀ u, y (y u) = 0)
    (hc : ∀ u, y (x u) = x (y u)) (v : X) (hv : x (y v) ≠ 0) :
    LinearIndependent (ZMod 2) ![v, x v, y v, x (y v)] := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  simp only [Fin.sum_univ_four] at ha
  change a 0 • v + a 1 • x v + a 2 • y v + a 3 • x (y v) = 0 at ha
  have h0 : a 0 = 0 := by
    have h := congrArg (fun u => x (y u)) ha
    simp only [map_add, map_smul, hc, hx, hy, map_zero, smul_zero, add_zero] at h
    exact (smul_eq_zero.mp h).resolve_right hv
  have h1 : a 1 = 0 := by
    have h := congrArg y ha
    simp only [map_add, map_smul, hc, hy, map_zero, smul_zero, h0,
      zero_smul, zero_add, add_zero] at h
    exact (smul_eq_zero.mp h).resolve_right hv
  have h2 : a 2 = 0 := by
    have h := congrArg x ha
    simp only [map_add, map_smul, hx, map_zero, smul_zero, h0,
      zero_smul, zero_add, add_zero] at h
    exact (smul_eq_zero.mp h).resolve_right hv
  have h3 : a 3 = 0 := by
    simp only [h0, h1, h2, zero_smul, zero_add] at ha
    exact (smul_eq_zero.mp ha).resolve_right hv
  intro i
  fin_cases i <;> assumption

private theorem exists_regular_basis
    (x y : X →ₗ[ZMod 2] X)
    (hx : ∀ u, x (x u) = 0) (hy : ∀ u, y (y u) = 0)
    (hc : ∀ u, y (x u) = x (y u)) (v : X) (hv : x (y v) ≠ 0) :
    ∃ b : Basis (Fin 5) (ZMod 2) X,
      b 0 = v ∧ b 1 = x v ∧ b 2 = y v ∧ b 3 = x (y v) := by
  classical
  obtain ⟨w, hw⟩ := exists_linearIndependent_snoc_of_lt_finrank
    (regular_four_independent x y hx hy hc v hv)
    (by change 4 < Module.finrank (ZMod 2) (Fin 5 → ZMod 2); simp)
  let b : Basis (Fin 5) (ZMod 2) X := basisOfPiSpaceOfLinearIndependent hw
  have hb : ∀ i, b i = (Fin.snoc ![v, x v, y v, x (y v)] w : Fin 5 → X) i := by
    intro i
    exact congrFun (coe_basisOfPiSpaceOfLinearIndependent hw) i
  refine ⟨b, ?_, ?_, ?_, ?_⟩ <;> rw [hb] <;> rfl

/-- The fifth column of a square-zero map extending two regular chains. -/
private theorem square_zero_last_image
    (b : Basis (Fin 5) (ZMod 2) X) (x : X →ₗ[ZMod 2] X)
    (hx : ∀ u, x (x u) = 0)
    (h0 : x (b 0) = b 1) (h1 : x (b 1) = 0)
    (h2 : x (b 2) = b 3) (h3 : x (b 3) = 0) :
    ∃ p q : ZMod 2, x (b 4) = p • b 1 + q • b 3 := by
  let a := b.equivFun (x (b 4))
  have ha : a 0 • b 0 + a 1 • b 1 + a 2 • b 2 + a 3 • b 3 +
      a 4 • b 4 = x (b 4) := by
    have h := b.sum_equivFun (x (b 4))
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    change a 0 • b 0 + (a 1 • b 1 + (a 2 • b 2 +
      (a 3 • b 3 + a 4 • b 4))) = x (b 4) at h
    simpa only [add_assoc] using h
  have haa := congrArg x ha
  simp only [map_add, map_smul, h0, h1, h2, h3, hx, smul_zero, add_zero] at haa
  have h4 : a 4 = 0 := by
    have h := congrArg (fun u => b.equivFun u 4) haa
    have he : b.equivFun (x (b 4)) 4 = a 4 := rfl
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Basis.equivFun_self, he, map_zero, Pi.zero_apply] at h
    simp at h
    exact h
  have hh : a 0 • b 1 + a 2 • b 3 = 0 := by
    simpa only [h4, zero_smul, add_zero] using haa
  have hz0 : a 0 = 0 := by
    have h := congrArg (fun u => b.equivFun u 1) hh
    simpa using h
  have hz2 : a 2 = 0 := by
    have h := congrArg (fun u => b.equivFun u 3) hh
    simpa using h
  refine ⟨a 1, a 3, ?_⟩
  simpa only [hz0, hz2, h4, zero_smul, zero_add, add_zero] using ha.symm

/-- Correct an arbitrary fifth basis vector to one killed by both displacements. -/
private theorem exists_fixed_extension
    (x y : X →ₗ[ZMod 2] X)
    (hx : ∀ u, x (x u) = 0) (hy : ∀ u, y (y u) = 0)
    (hc : ∀ u, y (x u) = x (y u)) (v : X) (hv : x (y v) ≠ 0) :
    ∃ w : X, x w = 0 ∧ y w = 0 ∧
      LinearIndependent (ZMod 2) ![v, x v, y v, x (y v), w] := by
  classical
  obtain ⟨b, hb0, hb1, hb2, hb3⟩ := exists_regular_basis x y hx hy hc v hv
  have hx0 : x (b 0) = b 1 := by rw [hb0, hb1]
  have hx1 : x (b 1) = 0 := by rw [hb1, hx]
  have hx2 : x (b 2) = b 3 := by rw [hb2, hb3]
  have hx3 : x (b 3) = 0 := by rw [hb3, hx]
  have hy0 : y (b 0) = b 2 := by rw [hb0, hb2]
  have hy1 : y (b 1) = b 3 := by rw [hb1, hc, hb3]
  have hy2 : y (b 2) = 0 := by rw [hb2, hy]
  have hy3 : y (b 3) = 0 := by rw [hb3, hc, hy, map_zero]
  obtain ⟨p, q, hx4⟩ := square_zero_last_image b x hx hx0 hx1 hx2 hx3
  let b' := b.reindex (Equiv.swap (1 : Fin 5) 2)
  have hb' : ∀ i, b' i = b ((Equiv.swap (1 : Fin 5) 2) i) := by
    intro i
    simp [b']
  have hy'0 : y (b' 0) = b' 1 := by simpa [hb', Equiv.swap_apply_def] using hy0
  have hy'1 : y (b' 1) = 0 := by simpa [hb', Equiv.swap_apply_def] using hy2
  have hy'2 : y (b' 2) = b' 3 := by simpa [hb', Equiv.swap_apply_def] using hy1
  have hy'3 : y (b' 3) = 0 := by simpa [hb', Equiv.swap_apply_def] using hy3
  obtain ⟨p', r, hy4⟩ := square_zero_last_image b' y hy hy'0 hy'1 hy'2 hy'3
  have hy4 : y (b 4) = p' • b 2 + r • b 3 := by simpa [hb', Equiv.swap_apply_def] using hy4
  have hp : p = p' := by
    have h := hc (b 4)
    rw [hx4, hy4] at h
    simp only [map_add, map_smul, hy1, hy3, hx2, hx3, smul_zero, add_zero] at h
    have h' := congrArg (fun u => b.equivFun u 3) h
    simpa using h'
  rw [← hp] at hy4
  let w := b 4 - p • b 0 - r • b 1 - q • b 2
  have hwx : x w = 0 := by
    simp only [w, map_sub, map_smul, hx4, hx0, hx1, hx2, smul_zero, sub_zero]
    abel
  have hwy : y w = 0 := by
    simp only [w, map_sub, map_smul, hy4, hy0, hy1, hy2, smul_zero, sub_zero]
    abel
  refine ⟨w, hwx, hwy, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro a ha
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at ha
  change a 0 • v + (a 1 • x v + (a 2 • y v + (a 3 • x (y v) + a 4 • w))) = 0 at ha
  rw [← hb3, ← hb2, ← hb1, ← hb0] at ha
  have ha4 : a 4 = 0 := by
    have h := congrArg (fun u => b.equivFun u 4) ha
    simpa [w] using h
  apply Fintype.linearIndependent_iff.mp b.linearIndependent a
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change a 0 • b 0 + (a 1 • b 1 + (a 2 • b 2 + (a 3 • b 3 + a 4 • b 4))) = 0
  simpa only [ha4, zero_smul, add_zero] using ha

private theorem displacement_sq_zero (s : G) (hs : s ^ 2 = 1) :
    ∀ u, s (s u - u) - (s u - u) = 0 := by
  intro u
  have hss : s (s u) = u := by
    change (s * s) u = (1 : G) u
    rw [← pow_two, hs]
  rw [map_sub, hss]
  ext i
  change (u i - s u i) - (s u i - u i) = 0
  calc
    _ = (u i + u i) - (s u i + s u i) := by ring
    _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, sub_self]

private theorem displacement_commute (s t : G) (hst : s * t = t * s) :
    ∀ u, t (s u - u) - (s u - u) = s (t u - u) - (t u - u) := by
  intro u
  have h : s (t u) = t (s u) := congrArg (fun f : G => f u) hst
  rw [map_sub, map_sub, h]
  abel

/-- Every nonquadratic commuting pair of square-one elements of the actual
`GL₅(2)` is simultaneously conjugate to the marked regular four-plus-one pair. -/
public theorem regular_pair_normal_form
    (s t : G) (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (hst : s * t = t * s)
    (hn : ∃ v : X, s (t v - v) ≠ t v - v) :
    ∃ g : G, MulAut.conj g s = regularS ∧ MulAut.conj g t = regularT := by
  classical
  let x : X →ₗ[ZMod 2] X := s.toLinearMap - LinearMap.id
  let y : X →ₗ[ZMod 2] X := t.toLinearMap - LinearMap.id
  have hx : ∀ u, x (x u) = 0 := displacement_sq_zero s hs
  have hy : ∀ u, y (y u) = 0 := displacement_sq_zero t ht
  have hc : ∀ u, y (x u) = x (y u) := displacement_commute s t hst
  obtain ⟨v, hv⟩ := hn
  have hv' : x (y v) ≠ 0 := sub_ne_zero.mpr hv
  obtain ⟨w, hwx, hwy, hw⟩ := exists_fixed_extension x y hx hy hc v hv'
  let b : Basis (Fin 5) (ZMod 2) X := basisOfPiSpaceOfLinearIndependent hw
  have hb : ∀ i, b i = ![v, x v, y v, x (y v), w] i := by
    intro i
    exact congrFun (coe_basisOfPiSpaceOfLinearIndependent hw) i
  have hxbi : ∀ i, x (b i) = ![b 1, 0, b 3, 0, 0] i := by
    intro i
    fin_cases i <;> simp [hb, hx, hwx]
  have hybi : ∀ i, y (b i) = ![b 2, b 3, 0, 0, 0] i := by
    intro i
    fin_cases i <;> simp [hb, hc, hy, hwy]
  have hsx : ∀ u, s u = u + x u := by
    intro u
    change s u = u + (s u - u)
    abel
  have hty : ∀ u, t u = u + y u := by
    intro u
    change t u = u + (t u - u)
    abel
  let g : G := b.equivFun
  have hgs : g * s = regularS * g := by
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    change b.equivFun (s (b i)) = regularS (b.equivFun (b i))
    rw [hsx, map_add, hxbi]
    ext j
    fin_cases i <;> fin_cases j <;> simp [regularS]
  have hgt : g * t = regularT * g := by
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    change b.equivFun (t (b i)) = regularT (b.equivFun (b i))
    rw [hty, map_add, hybi]
    ext j
    fin_cases i <;> fin_cases j <;> simp [regularT]
  refine ⟨g, ?_, ?_⟩
  · change g * s * g⁻¹ = regularS
    rw [hgs, mul_inv_cancel_right]
  · change g * t * g⁻¹ = regularT
    rw [hgt, mul_inv_cancel_right]

end BinaryNaturalDual.FiveActors.Classification
