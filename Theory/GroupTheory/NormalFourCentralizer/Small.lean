module

public import Theory.GroupTheory.NormalFourCentralizer

/-!
# Centralizers of small normal elementary subgroups

A normal elementary subgroup of order at most four in a finite two-group
has centralizer of index at most two. The order-four case is the usual
map into its automorphism group of order six. In the remaining cases the
subgroup has at most one nonidentity element, which is fixed by conjugation.

This extends the normal-four centralizer calculation used in GLS, volume 2,
Lemma 10.20(ii), to include the smaller subgroups occurring in local actions.
-/

namespace Subgroup

/-- A normal elementary subgroup of order at most four in a finite two-group
has centralizer of index at most two. -/
public theorem centralizer_index_le_two_of_normal_elementary_card_le_four {P : Type*} [Group P] [Finite P]
    (hp : IsPGroup 2 P) (D : Subgroup P) [D.Normal] [IsElementaryAbelian 2 D]
    (hcard : Nat.card D ≤ 4) : (centralizer (D : Set P)).index ≤ 2 := by
  obtain ⟨n, hn⟩ := (hp.to_subgroup D).exists_card_eq
  have hsmall : n ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hn] using hcard
  interval_cases n
  · have hbot : D = ⊥ := eq_bot_of_card_le D (by simpa using hn.le)
    have hcent : centralizer (D : Set P) = ⊤ := by
      apply top_unique
      intro g _ x hx
      have hxone : x = 1 := by
        rw [hbot] at hx
        exact hx
      simp [hxone]
    simp [hcent]
  · have htwo : Nat.card D = 2 := by simpa using hn
    obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : D)).mp htwo
    have hcent : centralizer (D : Set P) = ⊤ := by
      apply top_unique
      intro g _ x hx
      by_cases hxone : x = 1
      · simp [hxone]
      let a : D := ⟨x, hx⟩
      let b : D := ⟨g * x * g⁻¹, (inferInstance : D.Normal).conj_mem x hx g⟩
      have hb : b ≠ 1 := by
        intro he
        have he' : g * x * g⁻¹ = 1 := congrArg Subtype.val he
        apply hxone
        have hh := congrArg (fun v : P => g⁻¹ * v * g) he'
        simpa [mul_assoc] using hh
      have ha : a ≠ 1 := fun he => hxone (congrArg Subtype.val he)
      have he : g * x * g⁻¹ = x := congrArg Subtype.val ((hz b hb).trans (hz a ha).symm)
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    simp [hcent]
  · exact centralizer_index_le_two_of_normal_four hp D (by simpa using hn)

end Subgroup
