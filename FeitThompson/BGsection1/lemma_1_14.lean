/-
Authors: Tianjiao Nie
-/

module

public import FeitThompson.BGsection1.corollary_1_12

open scoped Pointwise

public section

/-
**Kind**: Theorem
**Note**: Lemma 1.14
**Stmt**:
Let `p` be a prime.
Let `T` be a `p`-subgroup of a finite group `G`.
Let `M` be a normal `p'`-subgroup of `G`.
Let `C = C_G(T)` and `N = N_G(T)`.
Then
`C_{G/M}(TM/M) = CM/M`
and
`N_{G/M}(TM/M) = NM/M`.
-/

public theorem lemma_1_14_a {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (T M : Subgroup G)
    [Fact (IsPGroup p (↥T))] (hM : M.Normal) (hcop : Nat.Coprime p (Nat.card M)) :
    let q : G →* G ⧸ M := QuotientGroup.mk' M
    Subgroup.centralizer ((T.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) =
      (Subgroup.centralizer (T : Set G)).map q := by
  simpa using centralizer_map_quotient_eq_map_centralizer (G := G) (p := p) T M hM hcop

public theorem lemma_1_14_b {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (T M : Subgroup G)
    [Fact (IsPGroup p (↥T))] (hM : M.Normal) (hcop : Nat.Coprime p (Nat.card M)) :
    let q : G →* G ⧸ M := QuotientGroup.mk' M
    Subgroup.normalizer (T.map q) = (Subgroup.normalizer T).map q := by
  simpa using normalizer_map_quotient_eq_map_normalizer (G := G) (p := p) T M hM hcop


end
