module

public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.FieldDegree
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Nonsquares in an order-two centralizer of PSL₂(8)

A square root `x` of a centralizer involution induces an automorphism of `L`
whose square is one. Semilinear coverage and the odd field degree show that
this automorphism is conjugation by some `l ∈ L`. The actual matrix model
has trivial center, so `l² = 1`. Moreover `x` commutes with `l`, and `xl⁻¹`
belongs to the order-two centralizer. Squaring now gives `x² = 1`.

This proves the nonsquareness step of GLS, Volume 4, Chapter 2, Lemma 15.7,
conditional only on the stated local normalization and centralizer order.
The ambient normalization must be supplied by the source application.
This direct calculation avoids the source's incorrect assertion that the
two-residual of the involution centralizer is `C₂ × PSL₂(8)`.

Source: `refs/KGroup/GLS4/Chapter2.tex`, final paragraph of Lemma 15.7;
GLS4, Chapter 4, Lemmas 3.1(a) and 3.4(c) for the matrix automorphisms.
-/

namespace Theory.PSL2
open Subgroup

/-- An automorphism of the actual PSL₂(8) matrix quotient whose square is one is inner. -/
public theorem binaryThree_involutive_inner (a : MulAut (BinaryGroup 3))
    (ha : a ^ 2 = 1) :
    ∃ g : BinaryGroup 3, a = MulAut.conj g := by
  obtain ⟨g, σ, rfl⟩ := Theory.PSL2.binary_semilinear_coverage (by decide : 2 ≤ 3) a
  have hs := (Theory.PSL2.semilinear_involution_data σ g ha).1
  have hσ : σ = RingEquiv.refl _ := by
    by_contra hne
    have heven := Theory.PSL2.even_of_binary_field_involution (by decide : 0 < 3) σ hs hne
    obtain ⟨m, hm⟩ := heven
    omega
  exact ⟨g, by rw [hσ, Theory.PSL2.fieldAut_refl, mul_one]⟩

/-- If `L ≃ PSL₂(8)` has centralizer of order two, its nonidentity centralizer
element has no square root among elements normalizing `L`. It suffices that
its own centralizer normalizes `L`, since every square root centralizes its square. -/
public theorem nonsquare_of_card_two_centralizer {G : Type*} [_root_.Group G] (L : Subgroup G)
    (e : L ≃* BinaryGroup 3)
    (hJ : Nat.card (centralizer (L : Set G)) = 2)
    {u : G} (hu : u ∈ centralizer (L : Set G)) (hne : u ≠ 1)
    (hN : centralizer ({u} : Set G) ≤ normalizer (L : Set G)) :
    ∀ x : G, x ^ 2 ≠ u := by
  intro x hsq
  have hxC : x ∈ centralizer ({u} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← hsq]
    exact (Commute.refl x).pow_right 2
  let xn : normalizer (L : Set G) := ⟨x, hN hxC⟩
  let a := L.normalizerMonoidHom xn
  have ha : a ^ 2 = 1 := by
    rw [← map_pow]
    apply MonoidHom.mem_ker.mp
    rw [normalizerMonoidHom_ker]
    change x ^ 2 ∈ centralizer (L : Set G)
    rwa [hsq]
  have hea : (MulAut.congr e a) ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  obtain ⟨g, hg⟩ := binaryThree_involutive_inner (MulAut.congr e a) hea
  let l := e.symm g
  have hal : a = MulAut.conj l := by
    apply (MulAut.congr e).injective
    rw [hg]
    ext y
    simp [MulAut.congr, MulAut.conj_apply, l]
  have hl2 : l ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    apply Theory.PSL2.psl2_conj_eq_one_implies
    rw [map_pow]
    simpa only [l, MulEquiv.apply_symm_apply, ← hg] using hea
  have hconj (y : L) : x * (y : G) * x⁻¹ = (l : G) * y * (l : G)⁻¹ := by
    exact congrArg Subtype.val (DFunLike.congr_fun hal y)
  have hxl : Commute x (l : G) := by
    apply mul_inv_eq_iff_eq_mul.mp
    simpa using hconj l
  have hj : x * (l : G)⁻¹ ∈ centralizer (L : Set G) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    have hh := hconj ⟨y, hy⟩
    dsimp at hh
    have hh' := congrArg (fun v : G => (l : G)⁻¹ * v * x) hh
    have hc : (l : G)⁻¹ * x * y = y * (l : G)⁻¹ * x := by
      simpa [mul_assoc] using hh'
    calc
      y * (x * (l : G)⁻¹) = y * ((l : G)⁻¹ * x) := by rw [hxl.inv_right.eq]
      _ = (l : G)⁻¹ * x * y := by rw [← mul_assoc, ← hc]
      _ = (x * (l : G)⁻¹) * y := by rw [hxl.inv_right.eq]
  have hj2 : (x * (l : G)⁻¹) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨x * (l : G)⁻¹, hj⟩ : centralizer (L : Set G)))
    rw [hJ] at hh
    exact congrArg Subtype.val hh
  have hl2G : (l : G) ^ 2 = 1 := congrArg Subtype.val hl2
  rw [hxl.inv_right.mul_pow, inv_pow, hl2G, inv_one, mul_one, hsq] at hj2
  exact hne hj2

end Theory.PSL2
