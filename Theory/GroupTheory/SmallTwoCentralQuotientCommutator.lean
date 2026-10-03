module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index

/-!
# Normalizer action on a small two-group modulo a normal involution

Let `K` be a two-subgroup of a finite group, and let `Z ≤ K` be a normal
subgroup of the ambient group of order two. If `K` has order less than eight,
every subgroup normalizing `K` acts trivially on its image modulo `Z`.
Equivalently, its commutator with `K` lies in `Z`.

The quotient image has order `card K / 2`. It is a two-group of order less
than four, hence has at most two elements. Every normalizer element fixes
the unique possible nonidentity element, so the quotient commutator is
trivial. Pulling back along the quotient map gives the asserted containment.

This is an elementary finite-group argument, isolated for the small-subgroup
step in Stellmacher's Theorem 2 development. It depends only on Mathlib's
subgroup index, p-group, and commutator APIs.
-/

namespace Subgroup

private theorem normalizer_le_centralizer_of_card_two
    {D : Type*} [Group D] (A : Subgroup D) (hA : Nat.card A = 2) :
    normalizer (A : Set D) ≤ centralizer (A : Set D) := by
  obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  intro g hg
  apply mem_centralizer_iff.mpr
  intro x hx
  by_cases hxone : x = 1
  · simp [hxone]
  let xA : A := ⟨x, hx⟩
  let yA : A := ⟨g * x * g⁻¹, (hg x).mp hx⟩
  have hyne : yA ≠ 1 := by
    intro hy
    have hy' : g * x * g⁻¹ = 1 := congrArg Subtype.val hy
    apply hxone
    have h := congrArg (fun a : D => g⁻¹ * a * g) hy'
    simpa [mul_assoc] using h
  have heq : yA = xA := (hzuniq yA hyne).trans (hzuniq xA (by
    intro hx'
    exact hxone (congrArg Subtype.val hx'))).symm
  have heq' : g * x * g⁻¹ = x := congrArg Subtype.val heq
  have h := congrArg (fun a : D => a * g) heq'
  simpa [mul_assoc] using h.symm

/-- A normalizer acts trivially on a two-subgroup of order less than eight
modulo a contained ambient-normal subgroup of order two. -/
public theorem commutator_le_of_card_lt_eight_of_normal_order_two
    {G : Type*} [Group G] [Finite G] (K Z A : Subgroup G) [Z.Normal]
    (hK : IsPGroup 2 K) (hZK : Z ≤ K) (hZcard : Nat.card Z = 2)
    (hAK : A ≤ normalizer (K : Set G)) (hsmall : Nat.card K < 8) :
    ⁅K, A⁆ ≤ Z := by
  let q := QuotientGroup.mk' Z
  let B := K.map q
  have hcard : 2 * Nat.card B = Nat.card K := by
    have hc := (Z.subgroupOf K).card_mul_index
    have hz : Nat.card (Z.subgroupOf K) = 2 :=
      (Nat.card_congr (subgroupOfEquivOfLe hZK).toEquiv).trans hZcard
    rw [hz] at hc
    have hi : (Z.subgroupOf K).index = Nat.card B := by
      change Z.relIndex K = Nat.card (K.map q)
      simpa only [q, QuotientGroup.ker_mk'] using K.relIndex_ker q
    rwa [hi] at hc
  have hBcard : Nat.card B ≤ 2 := by
    rcases (hK.map q).card_eq_or_dvd with hone | heven
    · change Nat.card B = 1 at hone
      omega
    · change 2 ∣ Nat.card B at heven
      omega
  have hcentral : A.map q ≤ centralizer (B : Set (G ⧸ Z)) := by
    by_cases hone : Nat.card B ≤ 1
    · rw [eq_bot_of_card_le B hone]
      intro a _
      apply mem_centralizer_iff.mpr
      intro b hb
      have : b = 1 := hb
      simp [this]
    · have htwo : Nat.card B = 2 := by omega
      exact ((map_mono hAK).trans (le_normalizer_map q)).trans
        (normalizer_le_centralizer_of_card_two B htwo)
  have hcomm : ⁅K, A⁆.map q = ⊥ := by
    rw [map_commutator, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hcentral
  have := (map_eq_bot_iff _).mp hcomm
  simpa only [q, QuotientGroup.ker_mk'] using this

end Subgroup
