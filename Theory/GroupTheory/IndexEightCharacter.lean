module
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.IndexNormal

/-!
# Extending a character across an index-eight section

Let `R ≤ Q` be normal subgroups of a finite group `P`, with indices
`[P : R] = 8` and `[Q : R] = 2`. If `P / Q` is cyclic and there is an
involution outside `Q`, the nontrivial binary character of `Q / R` extends
to `P`.

In `P / R`, lift a generator of the cyclic quotient of order four. Its
order is four or eight. The latter would make `P / R` cyclic, whose unique
involution lies in the kernel, contrary to the supplied involution. Thus
the lift generates a subgroup of order four meeting the kernel trivially.
This subgroup has index two, and its quotient gives the character.

This is the elementary character-extension argument for the order-eight
section in Thompson's N-group local analysis; the proof uses only the
cyclic-group and quotient-group results imported below.
-/

private theorem character_of_eight_to_cyclic_four
    {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y] [IsCyclic Y]
    (f : X →* Y) (hf : Function.Surjective f)
    (hX : Nat.card X = 8) (hY : Nat.card Y = 4)
    (ht : ∃ t : X, t ^ 2 = 1 ∧ f t ≠ 1) :
    ∃ χ : X →* Multiplicative (ZMod 2), ∀ x : X, f x = 1 → (χ x = 1 ↔ x = 1) := by
  classical
  obtain ⟨y, hy⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Y)
  rw [hY] at hy
  obtain ⟨a, rfl⟩ := hf y
  have hfour : 4 ∣ orderOf a := hy ▸ orderOf_map_dvd f a
  have height : orderOf a ∣ 8 := hX ▸ orderOf_dvd_natCard a
  have ha : orderOf a = 4 := by
    have ha_cases : orderOf a = 4 ∨ orderOf a = 8 := by
      have := Nat.le_of_dvd (by decide : 0 < 8) height
      have hpos := orderOf_pos a
      obtain ⟨k, hk⟩ := hfour
      omega
    rcases ha_cases with ha | ha
    · exact ha
    · let : IsCyclic X := isCyclic_of_orderOf_eq_card a (ha.trans hX.symm)
      obtain ⟨t, ht, hft⟩ := ht
      have htne : t ≠ 1 := by intro h; exact hft (h ▸ f.map_one)
      have htord : orderOf t = 2 := orderOf_eq_prime_iff.mpr ⟨ht, htne⟩
      have ha4 : orderOf (a ^ 4) = 2 := by rw [orderOf_pow, ha]; decide
      have hta := IsCyclic.eq_of_orderOf_eq_two htord ha4
      apply False.elim
      apply hft
      rw [hta, map_pow, ← hy]
      exact pow_orderOf_eq_one _
  let K := Subgroup.zpowers a
  have hK : Nat.card K = 4 := by simpa [K] using ha
  have hi : K.index = 2 := by
    have h := K.card_mul_index
    rw [hK, hX] at h
    omega
  let : K.Normal := Subgroup.normal_of_index_eq_two hi
  have hquot : Nat.card (X ⧸ K) = 2 := by rw [← K.index_eq_card, hi]
  let e : (X ⧸ K) ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hquot (by simp)
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' K), ?_⟩
  intro x hx
  change e (QuotientGroup.mk' K x) = 1 ↔ x = 1
  rw [e.map_eq_one_iff]
  change (x : X ⧸ K) = 1 ↔ x = 1
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨n, rfl⟩
    rw [map_zpow] at hx
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rw [ha, ← hy]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hx
  · rintro rfl
    exact K.one_mem

/-- The nontrivial character of `Q / R` extends to `P` when the cyclic
order-four quotient has an involution lift outside its kernel. -/
public theorem exists_character_of_index_eight
    {P : Type*} [Group P] [Finite P]
    (R Q : Subgroup P) [R.Normal] [Q.Normal] (hRQ : R ≤ Q)
    (hP : Nat.card P = 8 * Nat.card R) (hQ : Nat.card Q = 2 * Nat.card R)
    [IsCyclic (P ⧸ Q)] (ht : ∃ t : P, t ^ 2 = 1 ∧ t ∉ Q) :
    ∃ χ : P →* Multiplicative (ZMod 2),
      ∀ x : P, x ∈ Q → (χ x = 1 ↔ x ∈ R) := by
  classical
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hX : Nat.card (P ⧸ R) = 8 := by
    apply Nat.eq_of_mul_eq_mul_right hRpos
    rw [← R.card_eq_card_quotient_mul_card_subgroup, hP]
  have hY : Nat.card (P ⧸ Q) = 4 := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card Q from Nat.card_pos)
    rw [← Q.card_eq_card_quotient_mul_card_subgroup, hP, hQ]
    omega
  let f : (P ⧸ R) →* (P ⧸ Q) := QuotientGroup.map R Q (MonoidHom.id P) hRQ
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective Q y
    exact ⟨QuotientGroup.mk' R p, rfl⟩
  have ht' : ∃ t : P ⧸ R, t ^ 2 = 1 ∧ f t ≠ 1 := by
    obtain ⟨t, ht, htQ⟩ := ht
    refine ⟨QuotientGroup.mk' R t, ?_, ?_⟩
    · rw [← map_pow, ht, map_one]
    · exact fun h => htQ ((QuotientGroup.eq_one_iff t).mp h)
  obtain ⟨χ, hχ⟩ := character_of_eight_to_cyclic_four f hf hX hY ht'
  refine ⟨χ.comp (QuotientGroup.mk' R), ?_⟩
  intro x hx
  exact (hχ (QuotientGroup.mk' R x) ((QuotientGroup.eq_one_iff x).mpr hx)).trans
    (QuotientGroup.eq_one_iff x)
