module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.RootWords

/-!
# A generation argument from seven twisted root identities

In a quotient that kills the second and eighth root curves, the even-root
commutator first kills the fourth and sixth curves. Two more commutators kill
the central third and fifth parameters. The first-eighth commutator then
identifies the third and seventh curves with incompatible scalar dilations,
forcing both to vanish. The first-seventh commutator finally kills the fifth
curve. The scalar argument uses an element different from zero and one.

`RootRelations` consists of explicit word equations, to be proved separately
for the actual matrix words. We use the source right commutator
`a⁻¹ * b⁻¹ * a * b`, not Mathlib's opposite convention. Positions are zero
based. This argument includes the fifth curve, which represents the trivial
submodule in the nonsplit five-dimensional first radical layer.

Source: GLS3, 2.4.5(d) and the final Ree example of §3.2, in
`refs/KGroup/GLS3/chapter2.tex` and `chapter3.tex`. The application is
Aschbacher–Smith F.1.12(II)(i), printed pp.263–264.
-/

@[expose] public section
noncomputable section

namespace ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

/-- The seven literal multiplication and right-commutator identities used below.
No generation or fixed-point conclusion is part of this predicate. -/
def RootRelations {G : Type*} [Group G] (m : ℕ)
    (x y : Fin 8 → CoefficientField m → G) : Prop :=
  (∀ t u, x 3 (t + u) = x 3 t * x 3 u) ∧
  (∀ t u, x 2 t * x 2 u = x 2 (t + u) * y 2 (titsEnd m t * u)) ∧
  (∀ t u, (x 1 t)⁻¹ * (x 7 u)⁻¹ * x 1 t * x 7 u =
    x 3 (titsEnd m t * u) * x 5 (t * titsEnd m u)) ∧
  (∀ t u, (x 0 t)⁻¹ * (x 3 u)⁻¹ * x 0 t * x 3 u = y 2 (t * u)) ∧
  (∀ t u, (x 0 t)⁻¹ * (x 5 u)⁻¹ * x 0 t * x 5 u =
    x 3 (titsEnd m t * u) * y 4 (t * titsEnd m u)) ∧
  (∀ t u, (x 0 t)⁻¹ * (x 7 u)⁻¹ * x 0 t * x 7 u =
    x 1 ((t ^ 2 * titsEnd m t) * u) * (x 2 ((t * titsEnd m t) * u))⁻¹ *
    x 3 ((t ^ 2 * titsEnd m t ^ 2) * (u * titsEnd m u)) *
    y 4 ((t ^ 3 * titsEnd m t ^ 2) * (u ^ 2 * titsEnd m u)) *
    x 5 ((t ^ 2 * titsEnd m t) * (u * titsEnd m u)) * x 6 (t * u)) ∧
  (∀ t u, (x 0 t)⁻¹ * (x 6 u)⁻¹ * x 0 t * x 6 u =
    (x 2 (titsEnd m t * u))⁻¹ * x 3 ((t * titsEnd m t) * (u * titsEnd m u)) *
    x 4 (t * titsEnd m u))

/-- Literal root equations are preserved by homomorphisms, in particular by
the quotient by the normal closure of the end-root curve. -/
theorem RootRelations.map {G H : Type*} [Group G] [Group H] {m : ℕ}
    {x y : Fin 8 → CoefficientField m → G} (h : RootRelations m x y) (f : G →* H) :
    RootRelations m (fun i t => f (x i t)) (fun i t => f (y i t)) := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t u
  · simpa only [map_mul] using congrArg f (h1 t u)
  · simpa only [map_mul] using congrArg f (h2 t u)
  · simpa only [map_mul, map_inv] using congrArg f (h3 t u)
  · simpa only [map_mul, map_inv] using congrArg f (h4 t u)
  · simpa only [map_mul, map_inv] using congrArg f (h5 t u)
  · simpa only [map_mul, map_inv] using congrArg f (h6 t u)
  · simpa only [map_mul, map_inv] using congrArg f (h7 t u)

/-- An injective carrier map reflects the literal root equations. -/
theorem RootRelations.of_injective {G H : Type*} [Group G] [Group H] {m : ℕ}
    {x y : Fin 8 → CoefficientField m → G} (f : G →* H) (hf : Function.Injective f)
    (h : RootRelations m (fun i t => f (x i t)) (fun i t => f (y i t))) :
    RootRelations m x y := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t u <;> apply hf
  · simpa only [map_mul] using h1 t u
  · simpa only [map_mul] using h2 t u
  · simpa only [map_mul, map_inv] using h3 t u
  · simpa only [map_mul, map_inv] using h4 t u
  · simpa only [map_mul, map_inv] using h5 t u
  · simpa only [map_mul, map_inv] using h6 t u
  · simpa only [map_mul, map_inv] using h7 t u

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

/-- Killing the two end positions forces all seven radical root curves to vanish. -/
theorem rootImages_eq_one {G : Type*} [Group G] (m : ℕ)
    (c : CoefficientField m) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (x y : Fin 8 → CoefficientField m → G) (h : RootRelations m x y)
    (h2 : ∀ t, x 1 t = 1) (h8 : ∀ t, x 7 t = 1) :
    ∀ i : Fin 8, i ≠ 0 → ∀ t, x i t = 1 := by
  rcases h with ⟨h4add, h3mul, h28, h14, h16, h18, h17⟩
  have he (t u) : x 3 (titsEnd m t * u) * x 5 (t * titsEnd m u) = 1 := by
    simpa only [h2, h8, inv_one, one_mul] using (h28 t u).symm
  have hc : c ^ 2 ≠ c := by
    intro h
    have : c * c = c * 1 := by simpa only [pow_two, mul_one] using h
    exact hc1 (mul_left_cancel₀ hc0 this)
  have h4 : ∀ t, x 3 t = 1 := by
    apply additive_killed_of_dilation (x 3) h4add (c ^ 2) c hc
    intro u
    have hleft := he (titsEnd m c) u
    have hright := he 1 (c * u)
    rw [titsEnd_twice] at hleft
    simp only [map_one, one_mul, map_mul] at hright
    exact mul_right_cancel (hleft.trans hright.symm)
  have h6 : ∀ t, x 5 t = 1 := by
    intro t
    obtain ⟨u, rfl⟩ := (titsAutomorphism m).surjective t
    have hh := he 1 u
    simpa only [h4, one_mul, titsAutomorphism_apply, titsEnd_apply] using hh
  have hy3 : ∀ t, y 2 t = 1 := by
    intro t
    simpa only [h4, inv_one, mul_one, inv_mul_cancel, one_mul] using (h14 1 t).symm
  have hy5 : ∀ t, y 4 t = 1 := by
    intro t
    simpa only [h6, h4, inv_one, mul_one, inv_mul_cancel, one_mul, map_one]
      using (h16 t 1).symm
  have h3add : ∀ t u, x 2 (t + u) = x 2 t * x 2 u := by
    intro t u
    simpa only [hy3, mul_one] using (h3mul t u).symm
  have hp (t u) : x 2 ((t * titsEnd m t) * u) = x 6 (t * u) := by
    have hh := h18 t u
    simp only [h8, h2, h4, hy5, h6, inv_one, mul_one, inv_mul_cancel, one_mul] at hh
    exact inv_mul_eq_one.mp hh.symm
  have h37 (u) : x 2 u = x 6 u := by simpa only [map_one, one_mul] using hp 1 u
  have hcT : c * titsEnd m c ≠ c := by
    intro hh
    have hh' : titsEnd m c = 1 := mul_left_cancel₀ hc0 (by simpa using hh)
    exact hc1 ((titsEnd m).injective (hh'.trans (map_one _).symm))
  have h3 : ∀ t, x 2 t = 1 := by
    apply additive_killed_of_dilation (x 2) h3add (c * titsEnd m c) c hcT
    intro u
    exact (hp c u).trans (h37 (c * u)).symm
  have h7 : ∀ t, x 6 t = 1 := fun t => (h37 t).symm.trans (h3 t)
  have h5 : ∀ t, x 4 t = 1 := by
    intro t
    simpa only [h7, h3, h4, inv_one, mul_one, inv_mul_cancel, one_mul, map_one]
      using (h17 t 1).symm
  intro i hi t
  fin_cases i
  · exact (hi rfl).elim
  · exact h2 t
  · exact h3 t
  · exact h4 t
  · exact h5 t
  · exact h6 t
  · exact h7 t
  · exact h8 t

end ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
