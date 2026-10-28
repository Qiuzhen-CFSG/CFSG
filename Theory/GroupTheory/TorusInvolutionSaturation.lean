module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic

/-!
# Saturation of involutions by a torus square orbit

Let A be a central exponent-two layer in a normal subgroup R. If every
nonidentity element of K has no nonidentity fixed point in A, one nontrivial
square x² in A produces |K||A| distinct noninvolutions: the elements
(k x k⁻¹)a have distinct squares for distinct k, and distinct values for
distinct a. This argument does not require R, or a base of R, to be abelian.

When |R| = 2q², |A| = q, and there are at least q(q-1) noninvolutions,
any disjoint family of at least q² square-one elements exhausts the
square-one elements outside A. The second theorem expresses this as a
cardinality saturation principle, including the identity in A.

Source: the final counting argument of GLS, Volume 4, Chapter 2,
Lemma 15.6, `refs/KGroup/GLS4/Chapter2.tex`. The source application is in
`BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.ElementaryRank`.
-/

namespace Subgroup

/-- A free torus orbit of a nontrivial square, multiplied by a central
square-one layer, gives distinct noninvolutions. -/
public theorem noninvolution_card_ge_of_free_square_orbit
    {H : Type*} [Group H] [Finite H] (R A K : Subgroup H) [R.Normal]
    (hAR : A ≤ R) (hAsq : ∀ a ∈ A, a ^ 2 = 1)
    (hcentral : ∀ a ∈ A, ∀ x ∈ R, Commute a x)
    (hfree : ∀ k ∈ K, k ≠ 1 → A ⊓ centralizer ({k} : Set H) = ⊥)
    {x : H} (hx : x ∈ R) (hxA : x ^ 2 ∈ A) (hx2 : x ^ 2 ≠ 1) :
    Nat.card K * Nat.card A ≤ Nat.card {r : R // r ^ 2 ≠ 1} := by
  have hconj (k : K) : (k : H) * x * (k : H)⁻¹ ∈ R :=
    (inferInstance : R.Normal).conj_mem x hx k
  have hsquare (k : K) (a : A) :
      ((k : H) * x * (k : H)⁻¹ * a) ^ 2 = (k : H) * x ^ 2 * (k : H)⁻¹ := by
    rw [((hcentral a a.property _ (hconj k)).symm).mul_pow, hAsq a a.property,
      mul_one]
    exact (map_pow (MulAut.conj (k : H)) x 2).symm
  let f : K × A → {r : R // r ^ 2 ≠ 1} := fun p =>
    ⟨⟨(p.1 : H) * x * (p.1 : H)⁻¹ * p.2,
      R.mul_mem (hconj p.1) (hAR p.2.property)⟩, by
      intro hh
      have hh' := congrArg Subtype.val hh
      change ((p.1 : H) * x * (p.1 : H)⁻¹ * p.2) ^ 2 = 1 at hh'
      rw [hsquare] at hh'
      exact hx2 ((MulAut.conj (p.1 : H)).injective (hh'.trans (map_one _).symm))⟩
  have hf : Function.Injective f := by
    intro p q he
    have he' : (p.1 : H) * x * (p.1 : H)⁻¹ * p.2 =
        (q.1 : H) * x * (q.1 : H)⁻¹ * q.2 :=
      congrArg (fun v : {r : R // r ^ 2 ≠ 1} => (v.val : H)) he
    have hs := congrArg (fun v : H => v ^ 2) he'
    rw [hsquare, hsquare] at hs
    have hc : x ^ 2 ∈ centralizer ({(q.1 : H)⁻¹ * p.1} : Set H) := by
      apply mem_centralizer_singleton_iff.mpr
      have he := congrArg (fun v : H => (q.1 : H)⁻¹ * v * p.1) hs
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using he.symm
    have hk : (q.1 : H)⁻¹ * p.1 = 1 := by
      by_contra hk
      have hxbot : x ^ 2 ∈ (⊥ : Subgroup H) :=
        hfree _ (K.mul_mem (K.inv_mem q.1.property) p.1.property) hk ▸ ⟨hxA, hc⟩
      exact hx2 (mem_bot.mp hxbot)
    have hpq : p.1 = q.1 := Subtype.ext (inv_mul_eq_one.mp hk).symm
    have hab : p.2 = q.2 := by
      rw [hpq] at he'
      exact Subtype.ext (mul_left_cancel he')
    exact Prod.ext hpq hab
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf

/-- Saturation by a central square-one layer, a family of square-one elements,
and the complementary noninvolutions leaves no other square-one elements. -/
public theorem square_one_mem_of_saturated_card
    {H : Type*} [Group H] [Finite H] (R A : Subgroup H) {q : ℕ}
    (hq : 0 < q) (hAR : A ≤ R) (hR : Nat.card R = 2 * q ^ 2)
    (hA : Nat.card A = q) (hAsq : ∀ a ∈ A, a ^ 2 = 1)
    (hnon : q * (q - 1) ≤ Nat.card {r : R // r ^ 2 ≠ 1})
    (P : R → Prop) (hPsq : ∀ r, P r → r ^ 2 = 1)
    (hPA : ∀ r, P r → (r : H) ∉ A)
    (hPcard : q ^ 2 ≤ Nat.card {r : R // P r}) :
    ∀ x : R, x ^ 2 = 1 → (x : H) ∉ A → P x := by
  classical
  let f : A ⊕ {r : R // P r} → {r : R // r ^ 2 = 1}
    | Sum.inl a => ⟨⟨a, hAR a.property⟩, Subtype.ext (hAsq a a.property)⟩
    | Sum.inr a => ⟨a.val, hPsq a.val a.property⟩
  have hf : Function.Injective f := by
    intro a b he
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact congrArg (fun v : {r : R // r ^ 2 = 1} => (v.val : H)) he
      | inr b =>
        have hab : (a : H) = b.val :=
          congrArg (fun v : {r : R // r ^ 2 = 1} => (v.val : H)) he
        exact False.elim (hPA b.val b.property (hab ▸ a.property))
    | inr a =>
      cases b with
      | inl b =>
        have hab : (a.val : H) = b :=
          congrArg (fun v : {r : R // r ^ 2 = 1} => (v.val : H)) he
        exact False.elim (hPA a.val a.property (hab.symm ▸ b.property))
      | inr b =>
        apply congrArg Sum.inr
        have he' : a.val = b.val := congrArg (fun v : {r : R // r ^ 2 = 1} => v.val) he
        exact Subtype.ext he'
  have hcomp : Nat.card {r : R // r ^ 2 ≠ 1} =
      Nat.card R - Nat.card {r : R // r ^ 2 = 1} := by
    let := Fintype.ofFinite R
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have hsle : Nat.card {r : R // r ^ 2 = 1} ≤ Nat.card R :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hc : Nat.card {r : R // r ^ 2 = 1} ≤ Nat.card (A ⊕ {r : R // P r}) := by
    rw [Nat.card_sum, hA]
    rw [hcomp, hR] at hnon
    rw [hR] at hsle
    have hcalc : q * (q - 1) = q ^ 2 - q := by
      rw [Nat.mul_sub_left_distrib, mul_one, pow_two]
    rw [hcalc] at hnon
    have hqle : q ≤ q ^ 2 := by nlinarith
    omega
  have hsur := (hf.bijective_of_nat_card_le hc).surjective
  intro x hx hxA
  obtain ⟨a | a, he⟩ := hsur ⟨x, hx⟩
  · have he' : (a : H) = x :=
      congrArg (fun v : {r : R // r ^ 2 = 1} => (v.val : H)) he
    exact False.elim (hxA (he' ▸ a.property))
  · have he' : a.val = x := congrArg Subtype.val he
    exact he' ▸ a.property
end Subgroup
