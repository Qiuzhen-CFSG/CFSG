module

public import Theory.Character.Induction
public import Mathlib.GroupTheory.Coset.Basic

/-!
# Induction commutes with inflation

For a surjective homomorphism `π : H →* Q`, induction from a subgroup `K` of
`Q`, followed by pullback along `π`, equals induction from `K.comap π` of the
pulled-back function. In particular, an induced linear character inflates to
an induced linear character.

The proof groups the conjugation sum by fibers of `π`. Each fiber has order
`|ker π|`, and the same factor relates the orders of `K.comap π` and `K`, so
it cancels in the normalization. The source is the defining induction formula
in `Theory.Character.Induction`; the fiber-counting argument follows the
scalar-product calculation in `Theory.Character.Inflation`. No conjugacy
invariance of the input function is needed.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite

private theorem sum_comp_surjective
    {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    (π : G →* H) (hsurj : Function.Surjective π) (f : H → ℂ) :
    (∑ x : G, f (π x)) = (Nat.card π.ker : ℂ) * ∑ y : H, f y := by
  classical
  rw [← Fintype.sum_fiberwise π (fun x => f (π x))]
  have hfiber (y : H) : Fintype.card {x : G // π x = y} = Nat.card π.ker := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hsurj y)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have hconst (x : {x : G // π x = y}) : f (π x) = f y := congrArg f x.property
  simp only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hfiber]

private theorem card_comap {H Q : Type*} [Group H] [Fintype H] [Group Q] [Fintype Q]
    (π : H →* Q) (hsurj : Function.Surjective π) (K : Subgroup Q) :
    (Nat.card (K.comap π) : ℂ) = (Nat.card π.ker : ℂ) * (Nat.card K : ℂ) := by
  classical
  have h := sum_comp_surjective π hsurj (fun q => if q ∈ K then 1 else 0)
  simpa [← Subgroup.mem_comap, Fintype.card_subtype, Nat.card_eq_fintype_card] using h

/-- Pullback along a surjection commutes with induction from the inverse-image
subgroup, for arbitrary functions on the subgroup. -/
public theorem inducedClassFunction_comp_surjective
    {H Q : Type*} [Group H] [Fintype H] [Group Q] [Fintype Q]
    (π : H →* Q) (hsurj : Function.Surjective π) (K : Subgroup Q)
    (f : ClassFunction K) :
    (fun h => inducedClassFunction K f (π h)) =
      inducedClassFunction (K.comap π) (fun x => f (π.subgroupComap K x)) := by
  classical
  funext h
  let value : Q → ℂ := fun q =>
    if hq : q⁻¹ * π h * q ∈ K then f ⟨q⁻¹ * π h * q, hq⟩ else 0
  have hterm (x : H) :
      (if hx : x⁻¹ * h * x ∈ K.comap π then
        f (π.subgroupComap K ⟨x⁻¹ * h * x, hx⟩) else 0) = value (π x) := by
    simp only [value, Subgroup.mem_comap, map_mul, map_inv]
    split
    · congr 1
      apply Subtype.ext
      exact map_mul π (x⁻¹ * h) x |>.trans (by rw [map_mul, map_inv])
    · rfl
  have hker : (Nat.card π.ker : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  change (Nat.card K : ℂ)⁻¹ * (∑ q : Q, value q) = _
  simp only [inducedClassFunction, hterm]
  rw [sum_comp_surjective π hsurj value, card_comap π hsurj K, mul_inv_rev]
  simp only [mul_assoc, inv_mul_cancel_left₀ hker]

/-- Inflation of an induced linear character is induced from the linear
character composed with the canonical map `K.comap π →* K`. -/
public theorem inducedClassFunction_linear_comp_surjective
    {H Q : Type*} [Group H] [Fintype H] [Group Q] [Fintype Q]
    (π : H →* Q) (hsurj : Function.Surjective π) (K : Subgroup Q)
    (linear : K →* ℂ) :
    (fun h => inducedClassFunction K linear (π h)) =
      inducedClassFunction (K.comap π) (linear.comp (π.subgroupComap K)) :=
  inducedClassFunction_comp_surjective π hsurj K linear

/-- An induced linear character remains induced from a linear character after
inflation along any surjective homomorphism of finite groups. -/
public theorem exists_inducedClassFunction_linear_comp_surjective
    {H Q : Type*} [Group H] [Fintype H] [Group Q] [Fintype Q]
    (π : H →* Q) (hsurj : Function.Surjective π) (K : Subgroup Q)
    (linear : K →* ℂ) :
    ∃ (L : Subgroup H) (μ : L →* ℂ),
      (fun h => inducedClassFunction K linear (π h)) = inducedClassFunction L μ :=
  ⟨K.comap π, linear.comp (π.subgroupComap K),
    inducedClassFunction_linear_comp_surjective π hsurj K linear⟩
