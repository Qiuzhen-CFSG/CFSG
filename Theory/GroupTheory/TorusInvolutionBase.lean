module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic

/-!
# An abelian base from a transitive section and involution bounds

Let `A ≤ B ≤ R` have orders `q`, `q²`, and `2q²`, with `q > 2`.
Suppose `A` is central in `B` and has exponent two, and conjugation by `K`
is transitive on the nonidentity cosets of `A` in `B`. An upper bound `2q`
for elementary subgroups not contained in `A` makes `B` contain a
noninvolution. Transitivity then makes every element of `B ∖ A` a
noninvolution. A lower bound `q² + q` for the square-one elements of `R`
forces every element of `R ∖ B` to square to one. An outside involution
therefore inverts `B` elementwise, proving that `B` is abelian.

This is the counting step in GLS, Volume 4, Chapter 2, Lemma 15.7,
first paragraph, following the involution census in Lemma 15.6;
see `refs/KGroup/GLS4/Chapter2.tex`, lines 2703–2745. The theorem does not
supply the source section, its torus action, or the involution bounds.
-/

namespace Subgroup

private theorem square_card_compl {H : Type*} [Group H] [Finite H] :
    Nat.card {x : H // x ^ 2 ≠ 1} = Nat.card H - Nat.card {x : H // x ^ 2 = 1} := by
  classical
  let := Fintype.ofFinite H
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

private theorem abelian_of_outside_squares
    {H : Type*} [Group H] (R B : Subgroup H) (hBR : B < R)
    (hout : ∀ x ∈ R, x ∉ B → x ^ 2 = 1) :
    ∀ x ∈ B, ∀ y ∈ B, Commute x y := by
  obtain ⟨u, huR, huB⟩ := SetLike.exists_of_lt hBR
  have hu2 := hout u huR huB
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hu2)
  have hinv (x : H) (hx : x ∈ B) : u * x * u⁻¹ = x⁻¹ := by
    have hux : u * x ∉ B := fun hh => huB ((B.mul_mem_cancel_right hx).mp hh)
    have hux2 := hout (u * x) (R.mul_mem huR (hBR.le hx)) hux
    have hi : (u * x)⁻¹ = u * x :=
      inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hux2)
    calc
      u * x * u⁻¹ = (u * x)⁻¹ * u⁻¹ := by rw [hi]
      _ = x⁻¹ := by simp only [mul_inv_rev, huinv, mul_assoc, ← pow_two, hu2, mul_one]
  intro x hx y hy
  have hm := hinv (x * y) (B.mul_mem hx hy)
  have hxy : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := by
    calc
      x⁻¹ * y⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) := by rw [hinv x hx, hinv y hy]
      _ = u * (x * y) * u⁻¹ := by group
      _ = y⁻¹ * x⁻¹ := by rw [hm, mul_inv_rev]
  have he := congrArg (fun a : H => a⁻¹) hxy
  exact (show x * y = y * x from by simpa only [mul_inv_rev, inv_inv] using he.symm)

/-- Torus transitivity, an elementary-subgroup bound and an involution census
force the abelian noninvolution profile. No normality of `B` is assumed. -/
public theorem abelian_noninvolution_profile_of_transitive_section {H : Type*} [Group H] [Finite H] (R B A K : Subgroup H) {q : ℕ}
    (hq : 2 < q) (hBR : B ≤ R) (hAB : A ≤ B)
    (hR : Nat.card R = 2 * q ^ 2) (hB : Nat.card B = q ^ 2) (hA : Nat.card A = q)
    (hAsq : ∀ a ∈ A, a ^ 2 = 1)
    (hcentral : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (htrans : ∀ x ∈ B, x ∉ A → ∀ y ∈ B, y ∉ A →
      ∃ k ∈ K, ∃ a ∈ A, y = k * x * k⁻¹ * a)
    (hcount : q ^ 2 + q ≤ Nat.card {x : R // x ^ 2 = 1})
    (hbound : ∀ E : Subgroup H, E ≤ R → (∀ x ∈ E, x ^ 2 = 1) →
      ¬ E ≤ A → Nat.card E ≤ 2 * q) :
    (∀ x ∈ B, ∀ y ∈ B, Commute x y) ∧
    (∃ b ∈ B, b ^ 2 ≠ 1) ∧ (∀ x ∈ R, x ∉ B → x ^ 2 = 1) := by
  classical
  have hqpos : 0 < q := by omega
  have hBA : ¬ B ≤ A := by
    intro hle
    have hc := Subgroup.card_le_of_le hle
    rw [hB, hA] at hc
    nlinarith
  have hnon : ∃ b ∈ B, b ^ 2 ≠ 1 := by
    by_contra hn
    have hs : ∀ x ∈ B, x ^ 2 = 1 := by simpa using hn
    have hc := hbound B hBR hs hBA
    rw [hB] at hc
    nlinarith
  have hnonA : ∀ b ∈ B, b ∉ A → b ^ 2 ≠ 1 := by
    obtain ⟨x, hx, hx2⟩ := hnon
    have hxA : x ∉ A := fun hh => hx2 (hAsq x hh)
    intro b hb hbA
    obtain ⟨k, _, a, ha, rfl⟩ := htrans x hx hxA b hb hbA
    have hcB : k * x * k⁻¹ ∈ B := by
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using B.mul_mem hb (B.inv_mem (hAB ha))
    rw [((hcentral a ha _ hcB).symm).mul_pow, hAsq a ha, mul_one]
    intro hs
    apply hx2
    have hh : (MulAut.conj k) (x ^ 2) = (MulAut.conj k) 1 := by
      simpa only [map_pow, map_one, MulAut.conj_apply] using hs
    exact (MulAut.conj k).injective hh
  have hsqB : Nat.card {b : B // b ^ 2 = 1} = q := by
    let f : A ≃ {b : B // b ^ 2 = 1} := {
      toFun := fun a => ⟨⟨a, hAB a.property⟩, Subtype.ext (hAsq a a.property)⟩
      invFun := fun b => ⟨b.val, by
        by_contra hn
        exact hnonA b.val b.val.property hn (congrArg Subtype.val b.property)⟩
      left_inv := fun a => rfl
      right_inv := fun b => rfl }
    exact (Nat.card_congr f).symm.trans hA
  have hnonB : Nat.card {b : B // b ^ 2 ≠ 1} = q ^ 2 - q := by
    rw [square_card_compl, hB, hsqB]
  let f : {b : B // b ^ 2 ≠ 1} → {r : R // r ^ 2 ≠ 1} := fun b =>
    ⟨⟨b.val, hBR b.val.property⟩, fun hh => b.property (Subtype.ext (congrArg (fun r : R => (r : H)) hh))⟩
  have hf : Function.Injective f := by
    intro x y hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun b : {r : R // r ^ 2 ≠ 1} => (b.val : H)) hh
  have hsur : Function.Surjective f := (hf.bijective_of_nat_card_le (by
    rw [square_card_compl, hR, hnonB]
    have hqq : q ≤ q ^ 2 := by nlinarith
    omega)).surjective
  have hout : ∀ x ∈ R, x ∉ B → x ^ 2 = 1 := by
    intro x hx hxB
    by_contra hx2
    have hn : (⟨x, hx⟩ : R) ^ 2 ≠ 1 := fun hh => hx2 (congrArg Subtype.val hh)
    obtain ⟨b, hb⟩ := hsur ⟨⟨x, hx⟩, hn⟩
    have he : ((b : B) : H) = x := congrArg (fun r : {r : R // r ^ 2 ≠ 1} => (r.val : H)) hb
    exact hxB (he ▸ b.val.property)
  have hlt : B < R := lt_of_le_of_ne hBR (by
    intro he
    rw [he, hR] at hB
    nlinarith)
  exact ⟨abelian_of_outside_squares R B hlt hout, hnon, hout⟩

end Subgroup
