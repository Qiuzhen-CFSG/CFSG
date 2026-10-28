module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.Relations

/-!
# The linear radical in a central quotient

The literal Ree commutator identities force six main curves to vanish in
any quotient in which the radical curves are central. The first B₂ block
becomes additive there: its central curve vanishes by the Tits-twisted
multiplication law. A nonidentity torus scalar then kills that first curve.
No normality, perfectness or quotient identification is assumed here.

Source: GLS3 2.4.5(d) and Table 2.4; the linear-side perfectness in
Aschbacher–Smith F.1.12(II), printed pp.263–264.
-/

public section
noncomputable section
namespace ReeF4.LargeLocalSeeds.LinearCommutators
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

private theorem additive_killed_of_dilation {F G : Type*} [Field F] [Group G]
    (x : F → G) (hadd : ∀ t u, x (t + u) = x t * x u)
    (a b : F) (hab : a ≠ b) (h : ∀ u, x (a * u) = x (b * u)) : ∀ t, x t = 1 := by
  intro t
  let u := (a - b)⁻¹ * t
  have he : (a - b) * u = t := by
    dsimp [u]
    rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hab), one_mul]
  have ha : a * u = t + b * u := by rw [← he]; ring
  have hh := h u
  rw [ha, hadd] at hh
  exact mul_right_cancel (hh.trans (one_mul _).symm)

private theorem twisted_pair_killed {G : Type*} [Group G] (m : ℕ)
    (c : CoefficientField m) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (a b : CoefficientField m → G) (hadd : ∀ t u, a (t + u) = a t * a u)
    (h : ∀ t u, a (titsEnd m t * u) = b (t * titsEnd m u)) :
    (∀ t, a t = 1) ∧ (∀ t, b t = 1) := by
  have hc : c ^ 2 ≠ c := by
    intro he
    exact hc1 (mul_left_cancel₀ hc0 (by simpa only [pow_two, mul_one] using he))
  have ha : ∀ t, a t = 1 := by
    apply additive_killed_of_dilation a hadd (c ^ 2) c hc
    intro u
    have hl := h (titsEnd m c) u
    have hr := h 1 (c * u)
    rw [titsEnd_twice] at hl
    simp only [map_one, one_mul, map_mul] at hr
    exact hl.trans hr.symm
  refine ⟨ha, ?_⟩
  intro t
  obtain ⟨u, rfl⟩ := (titsAutomorphism m).surjective t
  have hh := (h 1 u).symm
  simpa only [ha, one_mul, titsAutomorphism_apply, titsEnd_apply] using hh

/-- The eight main curves vanish, except for the omitted end-node Levi curve,
once the radical is central and a nonidentity scalar fixes its first curve.
The hypotheses are literal root equations and scalar conjugation data. -/
theorem central_rootImages_eq_one {G : Type*} [Group G] (m : ℕ)
    (c : CoefficientField m) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (x y : Fin 8 → CoefficientField m → G) (h : RootRelations m x y)
    (hcentral : ∀ i : Fin 8, i ≠ 7 → ∀ t g, Commute (x i t) g)
    (h1add : ∀ t u, x 1 (t + u) = x 1 t * x 1 u)
    (hy0add : ∀ t u, y 0 (t + u) = y 0 t * y 0 u)
    (h0mul : ∀ t u, x 0 t * x 0 u = x 0 (t + u) * y 0 (titsEnd m t * u))
    (a : CoefficientField m) (ha : a ≠ 1)
    (hscale : ∀ t, x 0 (a * t) = x 0 t) :
    ∀ i : Fin 8, i ≠ 7 → ∀ t, x i t = 1 := by
  rcases h with ⟨h3add, h2mul, h17, h03, h05, h07, h06⟩
  have hcomm (i : Fin 8) (hi : i ≠ 7) (j : Fin 8) (t u) :
      (x i t)⁻¹ * (x j u)⁻¹ * x i t * x j u = 1 := by
    rw [(hcentral i hi t (x j u)).inv_inv.eq]
    group
  have hp (t u) : x 3 (titsEnd m t * u) = (x 5 (t * titsEnd m u))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    exact (h17 t u).symm.trans (hcomm 1 (by decide) 7 t u)
  obtain ⟨h3, h5inv⟩ := twisted_pair_killed m c hc0 hc1 (x 3) (fun t => (x 5 t)⁻¹) h3add hp
  have h5 (t) : x 5 t = 1 := inv_eq_one.mp (h5inv t)
  have hy2 (t) : y 2 t = 1 := by
    simpa only [one_mul] using (h03 1 t).symm.trans (hcomm 0 (by decide) 3 1 t)
  have hy4 (t) : y 4 t = 1 := by
    simpa only [h3, one_mul, map_one, mul_one] using
      (h05 t 1).symm.trans (hcomm 0 (by decide) 5 t 1)
  have h2add (t u) : x 2 (t + u) = x 2 t * x 2 u := by
    simpa only [hy2, mul_one] using (h2mul t u).symm
  have hp24 (t u) : x 2 (titsEnd m t * u) = x 4 (t * titsEnd m u) := by
    have he := (h06 t u).symm.trans (hcomm 0 (by decide) 6 t u)
    simp only [h3, mul_one] at he
    exact inv_mul_eq_one.mp he
  obtain ⟨h2, h4⟩ := twisted_pair_killed m c hc0 hc1 _ _ h2add hp24
  have hp16 (t u) : x 1 ((t ^ 2 * titsEnd m t) * u) * x 6 (t * u) = 1 := by
    simpa only [h2, h3, hy4, h5, inv_one, mul_one] using
      (h07 t u).symm.trans (hcomm 0 (by decide) 7 t u)
  have hc : c ^ 2 * titsEnd m c ≠ c := by
    intro he
    have hh : c * titsEnd m c = 1 := mul_left_cancel₀ hc0 (by
      simpa only [pow_two, mul_assoc, mul_one] using he)
    have ht := congrArg (titsEnd m) hh
    rw [map_mul, titsEnd_twice, map_one, mul_comm] at ht
    exact hc1 (he.symm.trans ht)
  have h1 : ∀ t, x 1 t = 1 := by
    apply additive_killed_of_dilation (x 1) h1add (c ^ 2 * titsEnd m c) c hc
    intro u
    have hl := hp16 c u
    have hr := hp16 1 (c * u)
    simp only [one_pow, map_one, one_mul] at hr
    exact mul_right_cancel (hl.trans hr.symm)
  have h6 (t) : x 6 t = 1 := by
    simpa only [h1, one_mul] using hp16 1 t
  have hyp (t u) : y 0 (titsEnd m t * u) = y 0 (t * titsEnd m u) := by
    have he := (h0mul t u).symm.trans ((hcentral 0 (by decide) t (x 0 u)).eq.trans
      (h0mul u t))
    rw [add_comm u t, mul_comm (titsEnd m u) t] at he
    exact mul_left_cancel he
  have hy0 := (twisted_pair_killed m c hc0 hc1 _ _ hy0add hyp).1
  have h0add (t u) : x 0 (t + u) = x 0 t * x 0 u := by
    simpa only [hy0, mul_one] using (h0mul t u).symm
  have h0 : ∀ t, x 0 t = 1 := by
    apply additive_killed_of_dilation (x 0) h0add a 1 ha
    simpa only [one_mul] using hscale
  intro i hi t
  fin_cases i
  · exact h0 t
  · exact h1 t
  · exact h2 t
  · exact h3 t
  · exact h4 t
  · exact h5 t
  · exact h6 t
  · exact (hi rfl).elim

end ReeF4.LargeLocalSeeds.LinearCommutators
