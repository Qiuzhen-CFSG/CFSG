module
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.PGroup

/-!
# Maximal subgroups of finite p-groups

Every maximal proper subgroup of a finite p-group has index p, for prime p.
Nilpotence first makes the subgroup normal. Its quotient is a simple p-group,
therefore abelian with prime order; the p-group order condition forces that
prime to be p. This generalizes the two-group argument used privately in
`Theory/Alternating/proposition_5_2_4.lean` and supports maximal-subgroup
arguments without an upward dependency on that campaign.
-/

/-- A maximal subgroup of a finite p-group has index p. -/
public theorem IsPGroup.index_of_isCoatom
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (U : Subgroup G) (hU : IsCoatom U) :
    U.index = p := by
  let : Group.IsNilpotent G := hG.isNilpotent
  have hMall : ∀ M : Subgroup G, IsCoatom M → M.Normal :=
    (Group.isNilpotent_of_finite_tfae (G := G)).out 0 2 |>.mp
      (show Group.IsNilpotent G from inferInstance)
  let : U.Normal := hMall U hU
  let Q := G ⧸ U
  let q : G →* Q := QuotientGroup.mk' U
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective U
  let : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hU.ne_top
  let : IsSimpleGroup Q := {
    toNontrivial := inferInstance
    eq_bot_or_eq_top_of_normal := by
      intro N _
      by_cases hN : N = ⊥
      · exact Or.inl hN
      · right
        have hcomap : U < N.comap q := by
          have hker : q.ker = U := QuotientGroup.ker_mk' U
          exact lt_of_le_of_lt hker.ge
            ((Subgroup.comap_lt_comap_of_surjective hq).mpr
              (bot_lt_iff_ne_bot.mpr hN))
        have htop : N.comap q = ⊤ := hU.2 _ hcomap
        apply Subgroup.comap_injective hq
        rw [htop, Subgroup.comap_top]
  }
  have hQp : IsPGroup p Q := hG.to_quotient U
  let : Group.IsNilpotent Q := hQp.isNilpotent
  let : CommGroup Q := inferInstance
  have hprime : (Nat.card Q).Prime := IsSimpleGroup.prime_card
  have h2dvd : p ∣ Nat.card Q := by
    rcases hQp.card_eq_or_dvd with hcard | hdvd
    · have hgt : 1 < Nat.card Q :=
        Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    · exact hdvd
  have hcardQ : Nat.card Q = p := by
    exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hprime).mp h2dvd).symm
  rw [Subgroup.index_eq_card]
  exact hcardQ
