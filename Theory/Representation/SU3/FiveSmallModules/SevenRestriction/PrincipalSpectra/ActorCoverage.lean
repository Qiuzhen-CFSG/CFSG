module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Inputs
public import Theory.GroupTheory.SylowPrimeOrderCoverage
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Covering all actors in the SU₃(5) spectral calculation

The ambient embedding in GL₃(25) shows that the unitary group order is not
divisible by 49. Thus an operator of order seven can be realized by an
element of order seven, with exactly the same operator, even when the original
actor has larger order. Sylow conjugacy reduces all remaining actors to the
six nonidentity powers of any fixed element of order seven.

This removes actor coverage from the finite principal-series calculation;
it does not assert its characteristic-polynomial certificates. The final
specialization uses the literal induced action and its actual subquotients.
Source application: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

public section

open BenderSuzuki.MatrixGroups

namespace Representation.SU3.FiveSmallModules.SevenRestriction

/-- The embedding into GL₃(25) suffices; no unitary order formula is needed. -/
theorem seven_sq_not_dvd_card_standardGroup {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hF : Nat.card F = 25) : ¬ 7 ^ 2 ∣ Nat.card (standardGroup J) := by
  let := Fintype.ofFinite F
  have hcard : Fintype.card F = 25 := by rwa [← Nat.card_eq_fintype_card]
  intro hd
  have h := hd.trans (Subgroup.card_subgroup_dvd_card
    (HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J).specialSubgroup)
  rw [Matrix.card_GL_field, hcard] at h
  norm_num [Fin.prod_univ_succ] at h

private theorem exists_prime_order_lift_preserving_image {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) {p : ℕ} (hp : p.Prime) (hn : ¬ p ^ 2 ∣ Nat.card G)
    (a : G) (ha : orderOf (f a) = p) :
    ∃ b : G, orderOf b = p ∧ f b = f a := by
  have hd : p ∣ orderOf a := ha ▸ orderOf_map_dvd f a
  have hc : p.Coprime (orderOf a / p) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro h
    apply hn
    rw [pow_two]
    exact ((Nat.dvd_div_iff_mul_dvd hd).mp h).trans (orderOf_dvd_natCard a)
  let b := a ^ (orderOf a / p)
  have hb : orderOf b = p := orderOf_pow_orderOf_div (orderOf_pos a).ne' hd
  have hm : f a ∈ Subgroup.zpowers (f b) := by
    dsimp only [b]
    rw [map_pow, mem_zpowers_pow_iff, ha]
    exact hc.symm
  obtain ⟨n, hne⟩ := Subgroup.mem_zpowers_iff.mp hm
  refine ⟨b ^ n, ?_, by simpa only [map_zpow] using hne⟩
  apply Nat.dvd_antisymm
  · rw [← hb]
    exact orderOf_dvd_of_mem_zpowers ((Subgroup.zpowers b).zpow_mem (Subgroup.mem_zpowers b) n)
  · rw [← ha, ← hne, ← map_zpow]
    exact orderOf_map_dvd f _

/-- Replace an order-seven operator by exactly the same operator from an
actual order-seven element, without any assumption on the representation kernel. -/
theorem exists_order_seven_actor_same_operator
    {F K U : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hF : Nat.card F = 25) [Field K] [AddCommGroup U] [Module K U]
    (ρ : Representation K (standardGroup J) U) (x : standardGroup J)
    (hx : orderOf (ρ x) = 7) :
    ∃ y : standardGroup J, orderOf y = 7 ∧ ρ y = ρ x := by
  have ho : orderOf (ρ.asGroupHom x) = 7 := by
    rw [← orderOf_units, Representation.asGroupHom_apply]
    exact hx
  obtain ⟨y, hy, he⟩ := exists_prime_order_lift_preserving_image ρ.asGroupHom
    (by decide) (seven_sq_not_dvd_card_standardGroup J hF) x ho
  exact ⟨y, hy, congrArg Units.val he⟩

/-- Any property of the operator transfers from actual order-seven elements.
Keeping the equality transport over an abstract vector space avoids unfolding
the large induced-module quotient in concrete applications. -/
theorem operator_property_of_order_seven_elements
    {F K U : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hF : Nat.card F = 25) [Field K] [AddCommGroup U] [Module K U]
    (ρ : Representation K (standardGroup J) U) (P : Module.End K U → Prop)
    (h : ∀ y : standardGroup J, orderOf y = 7 → orderOf (ρ y) = 7 → P (ρ y))
    (x : standardGroup J) (hx : orderOf (ρ x) = 7) : P (ρ x) := by
  obtain ⟨y, hy, he⟩ := exists_order_seven_actor_same_operator J hF ρ x hx
  exact he ▸ h y hy (by rwa [he])

/-- The six nonidentity powers of one order-seven element cover all such
actors up to conjugation. -/
theorem order_seven_conjugate_power {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hF : Nat.card F = 25) (r x : standardGroup J)
    (hr : orderOf r = 7) (hx : orderOf x = 7) :
    ∃ (k : ℕ) (g : standardGroup J), 0 < k ∧ k < 7 ∧ x = g * r ^ k * g⁻¹ := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨k, g, he⟩ := exists_conjugate_pow_of_orderOf_eq_prime
    (seven_sq_not_dvd_card_standardGroup J hF) hx hr
  refine ⟨k % 7, g, ?_, Nat.mod_lt _ (by decide), ?_⟩
  · by_contra hn
    have hk : k % 7 = 0 := by omega
    have hp : r ^ k = 1 := by
      rw [← pow_mod_orderOf, hr, hk, pow_zero]
    have hx1 : x = 1 := by simpa [hp] using he
    simp [hx1] at hx
  · simpa only [← hr, pow_mod_orderOf] using he

private theorem charpoly_conjugate {K G V : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (x g : G) :
    (ρ (g * x * g⁻¹)).charpoly = (ρ x).charpoly := by
  let e : V ≃ₗ[K] V := LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹)
    (by change ρ g * ρ g⁻¹ = 1; rw [← map_mul, mul_inv_cancel, map_one])
    (by change ρ g⁻¹ * ρ g = 1; rw [← map_mul, inv_mul_cancel, map_one])
  have he : ρ (g * x * g⁻¹) = e.conj (ρ x) := by
    ext v
    simp [e, map_mul, LinearEquiv.conj_apply]
  rw [he, LinearEquiv.charpoly_conj]

/-- Six characteristic-polynomial certificates cover every group element of
order seven, without a hypothesis on its operator order. -/
theorem charpoly_of_order_seven_generator_powers
    {F K U : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hF : Nat.card F = 25) [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (ρ : Representation K (standardGroup J) U)
    (r : standardGroup J) (hr : orderOf r = 7) (P : Polynomial K)
    (hP : ∀ k : ℕ, 0 < k → k < 7 → (ρ (r ^ k)).charpoly = P)
    (x : standardGroup J) (hx : orderOf x = 7) : (ρ x).charpoly = P := by
  obtain ⟨k, g, hk0, hk7, hconj⟩ := order_seven_conjugate_power J hF r x hr hx
  rw [hconj, charpoly_conjugate]
  exact hP k hk0 hk7

/-- Six characteristic-polynomial certificates imply the polynomial for
every operator of order seven, including operators coming from central lifts. -/
theorem charpoly_of_seven_generator_powers
    {F K U : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hF : Nat.card F = 25) [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (ρ : Representation K (standardGroup J) U)
    (r : standardGroup J) (hr : orderOf r = 7) (P : Polynomial K)
    (hP : ∀ k : ℕ, 0 < k → k < 7 → (ρ (r ^ k)).charpoly = P)
    (x : standardGroup J) (hx : orderOf (ρ x) = 7) : (ρ x).charpoly = P := by
  exact operator_property_of_order_seven_elements J hF ρ (fun a => a.charpoly = P)
    (fun y hy _ => charpoly_of_order_seven_generator_powers J hF ρ r hr P hP y hy) x hx

/-- Apply the actor reduction to a literal principal-series subquotient.
This discharges actor coverage once the six polynomial certificates are proved. -/
theorem principal_series_charpoly_of_seven_generator_powers
    {F K : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hF : Nat.card F = 25) [Field K] (χ : standardBorel J →* Kˣ)
    (S : Subrepresentation (ind (standardBorel J).subtype (scalarCharacter χ)))
    (T : Subrepresentation S.toRepresentation)
    (r : standardGroup J) (hr : orderOf r = 7)
    (hP : ∀ k : ℕ, 0 < k → k < 7 →
      (T.quotientRepresentation (r ^ k)).charpoly =
        sevenSpectrum K (Module.finrank K (S.toSubmodule ⧸ T.toSubmodule)))
    (x : standardGroup J) (hx : orderOf (T.quotientRepresentation x) = 7) :
    (T.quotientRepresentation x).charpoly =
      sevenSpectrum K (Module.finrank K (S.toSubmodule ⧸ T.toSubmodule)) :=
  charpoly_of_seven_generator_powers J hF T.quotientRepresentation r hr _ hP x hx

end Representation.SU3.FiveSmallModules.SevenRestriction
