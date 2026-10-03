module

public import Theory.GroupAction.ElementaryEightInvolution
public import Theory.GroupAction.NormalizingFixedPoints
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Three-subgroup normalizers on an elementary eight

The centralizer of an order-three subgroup of Aut(E), for elementary E of
order eight, has odd order. Consequently its normalizer has order not divisible
by four. An involution commuting with the three-subgroup would have four fixed
elements, whereas the three-subgroup has two. Counting their common fixed
points modulo two and three gives a contradiction. Conjugation on the cyclic
three-subgroup then gives the normalizer assertion.

This intrinsic action argument supplies the three-core exclusion in the small
solvable automizer calculation of Stellmacher, Journal of Algebra 190 (1997),
Section 11, without a subgroup classification or a prescribed invariant plane.
-/

open Subgroup

private theorem fixed_card_two
    {E : Type*} [Group E] [Finite E]
    (hE : Nat.card E = 8) (B : Subgroup (MulAut E)) (hB : Nat.card B = 3) :
    Nat.card (FixedPoints.subgroup B E) = 2 := by
  let F := FixedPoints.subgroup B E
  have hp : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by simpa using hB)
  have hmod := hp.card_modEq_card_fixedPoints E
  change Nat.card E % 3 = Nat.card F % 3 at hmod
  rw [hE] at hmod
  have hdiv : Nat.card F ∣ 8 := hE ▸ F.card_subgroup_dvd_card
  have hproper : Nat.card F ≠ 8 := by
    intro hh
    have htop : F = ⊤ := F.eq_top_of_card_eq (hh.trans hE.symm)
    have hbot : B = ⊥ := by
      apply eq_bot_iff.mpr
      intro b hb
      apply mem_bot.mpr
      apply MulEquiv.ext
      intro x
      have hx : x ∈ F := htop ▸ mem_top x
      exact hx ⟨b, hb⟩
    rw [hbot, card_bot] at hB
    omega
  have hmem := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
  have hdivs : (8 : ℕ).divisors = {1, 2, 4, 8} := by decide
  rw [hdivs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  change Nat.card F = 2
  omega

/-- An order-three automorphism subgroup of an elementary eight has odd centralizer. -/
public theorem odd_card_centralizer_of_elementary_eight_three
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (B : Subgroup (MulAut E)) (hB : Nat.card B = 3) :
    Odd (Nat.card (centralizer (B : Set (MulAut E)))) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  let C := centralizer (B : Set (MulAut E))
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (even_iff_two_dvd.mp heven)
  let t : MulAut E := c
  have ht : orderOf t = 2 := (orderOf_injective C.subtype C.subtype_injective c).trans hc
  let Q := zpowers t
  have hQ : Nat.card Q = 2 := (Nat.card_zpowers t).trans ht
  have hQB : Q ≤ centralizer (B : Set (MulAut E)) := zpowers_le.mpr c.property
  have hBQ : B ≤ centralizer (Q : Set (MulAut E)) := le_centralizer_iff.mp hQB
  let F := FixedPoints.subgroup B E
  let D := FixedPoints.subgroup Q E
  let : IsInvariant Q E F := fixedPoints_isInvariant_of_normalizing_actor Q B
    (hQB.trans (centralizer_le_normalizer _))
  let : IsInvariant B E D := fixedPoints_isInvariant_of_normalizing_actor B Q
    (hBQ.trans (centralizer_le_normalizer _))
  have hF : Nat.card F = 2 := fixed_card_two hE B hB
  let x : Q := ⟨t, mem_zpowers t⟩
  have hx : x ≠ 1 := by
    intro hh
    have heq : t = 1 := congrArg Subtype.val hh
    rw [heq, orderOf_one] at ht
    omega
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    exact ht ▸ pow_orderOf_eq_one t
  have hmove : ∃ e : E, x • e ≠ e := by
    by_contra! hh
    apply hx
    apply Subtype.ext
    apply MulEquiv.ext
    exact hh
  have hD : Nat.card D = 4 :=
    fixed_subgroup_card_four_of_nontrivial_involution_on_eight x ⟨hx, hx2⟩ hQ hE hmove
  have hcommonQ : Nat.card (FixedPoints.subgroup Q F) = Nat.card (F ⊓ D : Subgroup E) := by
    rw [← card_map_of_injective F.subtype_injective,
      fixedPoints_subgroup_map_subtype_eq_inf]
  have hcommonB : Nat.card (FixedPoints.subgroup B D) = Nat.card (F ⊓ D : Subgroup E) := by
    rw [← card_map_of_injective D.subtype_injective,
      fixedPoints_subgroup_map_subtype_eq_inf, inf_comm]
  have hpQ : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by simpa using hQ)
  have hpB : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by simpa using hB)
  have hmQ := hpQ.card_modEq_card_fixedPoints F
  have hmB := hpB.card_modEq_card_fixedPoints D
  change Nat.card F % 2 = Nat.card (FixedPoints.subgroup Q F) % 2 at hmQ
  change Nat.card D % 3 = Nat.card (FixedPoints.subgroup B D) % 3 at hmB
  rw [hF, hcommonQ] at hmQ
  rw [hD, hcommonB] at hmB
  have hle : Nat.card (F ⊓ D : Subgroup E) ≤ 2 :=
    hF ▸ card_le_of_le (show F ⊓ D ≤ F from inf_le_left)
  have hpos := Nat.card_pos (α := (F ⊓ D : Subgroup E))
  omega

/-- Four does not divide the order of a three-subgroup normalizer on an elementary eight. -/
public theorem not_four_dvd_card_normalizer_of_elementary_eight_three
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (B : Subgroup (MulAut E)) (hB : Nat.card B = 3) :
    ¬ 4 ∣ Nat.card (normalizer (B : Set (MulAut E))) := by
  let : IsCyclic B := isCyclic_of_prime_card hB
  have hAut : Nat.card (MulAut B) = 2 := by
    rw [IsCyclic.card_mulAut, hB]
    decide
  let f := B.normalizerMonoidHom
  have hrange : Nat.card f.range ∣ 2 := hAut ▸ f.range.card_subgroup_dvd_card
  have hker : Odd (Nat.card f.ker) := by
    have hc := odd_card_centralizer_of_elementary_eight_three hE B hB
    have heq : Nat.card f.ker = Nat.card (centralizer (B : Set (MulAut E))) := by
      rw [normalizerMonoidHom_ker,
        Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (B : Set (MulAut E)))).toEquiv]
    rwa [heq]
  have hprod := f.ker.card_mul_index
  rw [index_ker] at hprod
  intro hfour
  have hdiv : 4 ∣ Nat.card f.range := by
    apply (hker.coprime_two_left.pow_left 2).dvd_of_dvd_mul_left
    simpa only [hprod] using hfour
  have := dvd_trans hdiv hrange
  norm_num at this
