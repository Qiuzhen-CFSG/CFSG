module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Placement.Transport
public import Theory.GroupTheory.SolvableSmallThreeCore
public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeGeometry

/-!
# Parabolic containment of the small ternary product in PSL₃

Let U be the full upper-unitriangular Sylow two-subgroup of PSL₃(F), where
|F| = 2^f and f ≥ 2. For a three-subgroup B of order at most 27 satisfying
BU = UB, the join has order |B||U| and only the prime divisors two and three.
Its three-core has order at most 27, and its order is divisible by 64.
Solvability therefore gives a nontrivial two-core by the small-three-core
theorem, whose proof uses Fitting self-centralization and the Frattini action.

The ambient image of this intrinsic two-core is a nontrivial two-subgroup
normalized by the whole join. Its full normalizer is an actual two-local,
so the projective fixed-space theorem conjugates the join into a point or
line parabolic. No invariant subspace or two-local witness is assumed.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), characteristic-two branch.
The subsequent Borel containment is a separate step.
-/

public section
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement

variable {F : Type*} [Field F] [Finite F] {f : ℕ} {B : Subgroup PSL(3,F)}

/-- Genuine permutability and coprime factor orders give the order of the join. -/
theorem projective_product_card (hF : Nat.card F = 2^f) (h : ProjectiveInput F B) :
    Nat.card (B ⊔ unipotent F : Subgroup PSL(3,F)) =
      Nat.card B * Nat.card F ^ 3 := by
  have hd : Disjoint B (unipotent F) :=
    h.three.disjoint_of_coprime (unipotent_isTwoGroup F hF) (by decide)
  have hc := card_set_mul_mul_card_inf B (unipotent F)
  rw [hd.eq_bot, card_bot, mul_one,
    ← coe_sup_of_set_mul_comm B (unipotent F) h.permutes, card_unipotent F] at hc
  exact hc

/-- The solvable product has a nontrivial intrinsic two-core when |F| ≥ 4. -/
theorem projective_product_twoCore_ne_bot (hf : 2 ≤ f) (hF : Nat.card F = 2^f)
    (h : ProjectiveInput F B) :
    pCore 2 (B ⊔ unipotent F : Subgroup PSL(3,F)) ≠ ⊥ := by
  let H := B ⊔ unipotent F
  have hcard : Nat.card H = Nat.card B * Nat.card (unipotent F) := by
    rw [card_unipotent F]
    exact projective_product_card hF h
  have hp : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3 := by
    intro p hp hd
    rw [hcard] at hd
    rcases hp.dvd_mul.mp hd with hb | hu
    · obtain ⟨n, hn⟩ := h.three.exists_card_eq
      rw [hn] at hb
      exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp (hp.dvd_of_dvd_pow hb)
        |>.resolve_left hp.ne_one)
    · obtain ⟨n, hn⟩ := (unipotent_isTwoGroup F hF).exists_card_eq
      rw [hn] at hu
      exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hu)
        |>.resolve_left hp.ne_one)
  have hsmall : Nat.card (pCore 3 H) ≤ 27 := by
    have hd := (pCore 3 H).card_subgroup_dvd_card
    rw [hcard] at hd
    have hcop := IsPGroup.coprime_card_of_ne 3 2 (by decide)
      (pCore 3 H) (unipotent F) pCore_isPGroup (unipotent_isTwoGroup F hF)
    exact (Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right hd)).trans h.card_le
  have h64 : 64 ∣ Nat.card H := by
    rw [hcard, card_unipotent F, hF, ← pow_mul]
    apply dvd_mul_of_dvd_right
    exact pow_dvd_pow 2 (by omega : 6 ≤ f * 3)
  exact twoCore_ne_bot_of_solvable_small_three_core h.solvable hp hsmall h64

/-- The whole product is conjugate into an actual point or line parabolic.
The normalizer of its embedded two-core supplies the two-local overgroup. -/
theorem projective_product_parabolic (hf : 2 ≤ f) (hF : Nat.card F = 2^f)
    (h : ProjectiveInput F B) :
    ∃ (g : PSL(3,F)) (point : Bool),
      (B ⊔ unipotent F).map (MulAut.conj g).toMonoidHom ≤ parabolic F point := by
  let H := B ⊔ unipotent F
  let N := (pCore 2 H).map H.subtype
  have hN : N ≠ ⊥ := by
    intro he
    exact projective_product_twoCore_ne_bot hf hF h
      (((pCore 2 H).map_eq_bot_iff_of_injective H.subtype_injective).mp he)
  have hlocal : IsTwoLocal (normalizer (N : Set PSL(3,F))) :=
    ⟨N, hN, pCore_isPGroup.map H.subtype, rfl⟩
  have hHN : H ≤ normalizer (N : Set PSL(3,F)) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore 2 H).le_normalizer_map H.subtype
  obtain ⟨g, point, hg⟩ :=
    CFSG.Quasithin.MainConverse.LinearThreeGeometry.twoLocal_conjugate_le F
      (by omega : 0 < f) hF (normalizer (N : Set PSL(3,F))) hlocal
  exact ⟨g, point, (map_mono hHN).trans hg⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement
