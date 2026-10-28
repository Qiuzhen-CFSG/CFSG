module

public import Theory.GroupTheory.PrimeRankCubeFree
public import Theory.GroupTheory.PrimeRankSylow

/-!
# Prime rank of a nonabelian group of prime-cube order

Every abelian subgroup of a nonabelian group of order `p³` is proper, so
its order is not divisible by `p³`. The prime-cube-free rank bound applies
to each such subgroup. Sylow conjugacy then gives the same rank bound in
any finite group with a nonabelian Sylow subgroup of order `p³`.

This supplies the elementary rank step for the sporadic groups in
Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem 0.1.2(5),
printed p.4. It does not assume or certify any sporadic order or Sylow model.
-/

open scoped IsMulCommutative

/-- A nonabelian group of prime-cube order has prime rank at most two. -/
public theorem primeRank_le_two_of_nonabelian_card_cube
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hc : Nat.card G = p ^ 3) (hna : ¬ IsMulCommutative G) :
    primeRank p G ≤ 2 := by
  apply csSup_le'
  rintro n ⟨A, hAp, hAc, hfg, hn⟩
  let : IsMulCommutative A := hAc
  have hnot : ¬ p ^ 3 ∣ Nat.card A := by
    intro hd
    have hcard : Nat.card A = Nat.card G :=
      Nat.dvd_antisymm A.card_subgroup_dvd_card (hc ▸ hd)
    have htop : A = ⊤ := Subgroup.eq_top_of_card_eq A hcard
    apply hna
    exact IsMulCommutative.of_comm fun x y => by
      have hx : x ∈ A := htop ▸ Subgroup.mem_top x
      have hy : y ∈ A := htop ▸ Subgroup.mem_top y
      exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hr : Group.rank A ≤ primeRank p A := by
    apply le_csSup (Theory.GroupTheory.primeRank_bdd p)
    refine ⟨⊤, hAp.of_injective (⊤ : Subgroup A).subtype Subtype.val_injective,
      inferInstance, inferInstance, ?_⟩
    exact le_of_eq (Group.rank_congr Subgroup.topEquiv).symm
  exact hn.trans (hr.trans (primeRank_le_two_of_cube_not_dvd hnot))

/-- It suffices to identify one nonabelian Sylow subgroup of order `p³`. -/
public theorem primeRank_le_two_of_nonabelian_sylow_cube
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hc : Nat.card P = p ^ 3) (hna : ¬ IsMulCommutative P) :
    primeRank p G ≤ 2 := by
  rw [P.primeRank_eq]
  exact primeRank_le_two_of_nonabelian_card_cube hc hna
