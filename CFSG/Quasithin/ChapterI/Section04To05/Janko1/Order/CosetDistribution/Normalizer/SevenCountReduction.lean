module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenSetup

/-!
# The counting contradiction for Bender (4.3)

Sum the actual involution fibers of `N_G(C_G(S))`. If their sizes and
multiplicities are the source counts, the index is at least
`1 + b₁ + 17a`, and the number of involutions is `b₁ + 43a`, with
`a = |C_G(S)|` and `b₁ ≥ 4a`. The class-size identity and the normalizer
order `6a` contradict `a ≥ 49`. The latter bound applies precisely when
the seven-centralizer is larger than the original subgroup.

This proves the consequence of the explicit counting contract. Constructing
that contract requires the separate local structure and incidence arguments.
Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), proof of (4.3), printed p.226.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData

private theorem seven_fiber_sums {G : Type*} [Group G] [Finite G]
    (H : Subgroup G)
    (hsizes : ∀ ω : G ⧸ H, ω ≠ benderBaseCoset H →
      Nat.card (BenderFiber H ω) = 0 ∨ Nat.card (BenderFiber H ω) = 1 ∨
      Nat.card (BenderFiber H ω) = 2 ∨ Nat.card (BenderFiber H ω) = 3 ∨
      Nat.card (BenderFiber H ω) = 6) :
    1 + benderCosetCount H 1 + benderCosetCount H 2 +
        benderCosetCount H 3 + benderCosetCount H 6 ≤ H.index ∧
      Nat.card {x : G // orderOf x = 2} = Nat.card (BenderFiber H (benderBaseCoset H)) +
        benderCosetCount H 1 + 2 * benderCosetCount H 2 +
        3 * benderCosetCount H 3 + 6 * benderCosetCount H 6 := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  have : ∀ ω : (G ⧸ H), Finite (BenderFiber H ω) := fun ω => by
    unfold BenderFiber
    infer_instance
  let f : (G ⧸ H) → ℕ := fun ω => Nat.card (BenderFiber H ω)
  let c : ℕ → (G ⧸ H) → ℕ := fun n ω => if ω ≠ benderBaseCoset H ∧ f ω = n then 1 else 0
  have hsumc (n : ℕ) : (∑ ω : (G ⧸ H), c n ω) = benderCosetCount H n := by
    simp only [c, Finset.sum_boole]
    rw [benderCosetCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  have hsumw (n : ℕ) : (∑ ω : (G ⧸ H), n * c n ω) = n * benderCosetCount H n := by
    rw [← Finset.mul_sum, hsumc]
  have hoccupied (ω : (G ⧸ H)) :
      (if ω = benderBaseCoset H then 1 else 0) + c 1 ω + c 2 ω + c 3 ω + c 6 ω ≤ 1 := by
    by_cases hb : ω = benderBaseCoset H
    · simp [c, hb]
    · rcases hsizes ω hb with h0 | h1 | h2 | h3 | h6 <;>
        simp [c, f, *]
  have hcosets : 1 + benderCosetCount H 1 + benderCosetCount H 2 +
      benderCosetCount H 3 + benderCosetCount H 6 ≤ H.index := by
    have hc := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hoccupied ω)
    simpa [Finset.sum_add_distrib, hsumc, H.index_eq_card, Nat.card_eq_fintype_card] using hc
  have hpartition : Nat.card {x : G // orderOf x = 2} = ∑ ω : (G ⧸ H), f ω := by
    let e : {x : G // orderOf x = 2} ≃ Σ ω : (G ⧸ H), BenderFiber H ω :=
      { toFun := fun x => ⟨benderRightCoset H x, ⟨x, x.property, rfl⟩⟩
        invFun := fun y => ⟨y.2.1, y.2.2.1⟩
        left_inv := by intro x; rfl
        right_inv := by rintro ⟨ω, x, hx, rfl⟩; rfl }
    rw [Nat.card_congr e, Nat.card_sigma]
  have hentry (ω : (G ⧸ H)) : f ω =
      (if ω = benderBaseCoset H then f (benderBaseCoset H) else 0) +
      c 1 ω + 2 * c 2 ω + 3 * c 3 ω + 6 * c 6 ω := by
    by_cases hb : ω = benderBaseCoset H
    · simp [c, hb]
    · rcases hsizes ω hb with h0 | h1 | h2 | h3 | h6 <;>
        simp [c, f, *]
  refine ⟨hcosets, ?_⟩
  rw [hpartition]
  calc
    (∑ ω : (G ⧸ H), f ω) = ∑ ω : (G ⧸ H),
        ((if ω = benderBaseCoset H then f (benderBaseCoset H) else 0) +
          c 1 ω + 2 * c 2 ω + 3 * c 3 ω + 6 * c 6 ω) :=
      Finset.sum_congr rfl (fun ω _ => hentry ω)
    _ = _ := by simp [Finset.sum_add_distrib, hsumc, hsumw, f]

/-- The actual local counts of (4.3) exclude a larger seven-centralizer.
The class-size identity supplies `|G| = 120|J|`; the count uses the
separate quotient by `N_G(C_G(S))`. -/
public theorem seven_centralizer_eq_of_counts {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (h : Janko1CentralizerData G) {d : ℕ}
    (localData : BenderPrimeData G d) (S : Subgroup G) (hS : Nat.card S = 7)
    (counts : BenderSevenCountData S) : centralizer (S : Set G) = S := by
  by_contra hne
  have h49 := h.seven_centralizer_card_ge localData S hS hne
  obtain ⟨hc, hj⟩ := seven_fiber_sums
    (normalizer (centralizer (S : Set G) : Set G)) counts.fiber_sizes
  rw [counts.double_cosets, counts.triple_cosets, counts.sextuple_cosets] at hc
  rw [counts.base_fiber, counts.double_cosets, counts.triple_cosets,
    counts.sextuple_cosets] at hj
  have horder := (normalizer (centralizer (S : Set G) : Set G)).index_mul_card
  rw [counts.normalizer_card, h.card_eq_involution_count_mul, hj] at horder
  have hlo := counts.single_lower
  let a := Nat.card (centralizer (S : Set G))
  let b := benderCosetCount (normalizer (centralizer (S : Set G) : Set G)) 1
  let i := (normalizer (centralizer (S : Set G) : Set G)).index
  change 49 ≤ a at h49
  change 4 * a ≤ b at hlo
  change 1 + b + 12 * a + 4 * a + a ≤ i at hc
  change i * (6 * a) = (a + b + 2 * (12 * a) + 3 * (4 * a) + 6 * a) * 120 at horder
  have hi : a * (1 + b + 17 * a) ≤ a * i := Nat.mul_le_mul_left a (by omega)
  have hb : 4 * a * (a - 20) ≤ b * (a - 20) := Nat.mul_le_mul_right (a - 20) hlo
  have ha : a - 20 + 20 = a := Nat.sub_add_cancel (by omega)
  nlinarith

end CFSG.Quasithin.Janko1CentralizerData
