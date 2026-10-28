module

public import Theory.Quasithin.Rank
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Prime rank through a coprime kernel

A homomorphism with kernel coprime to p is injective on every abelian
p-subgroup. Thus the rank of its domain cannot exceed that of its codomain.
Together with Schur–Zassenhaus, this proves equality for surjections.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.10–11,
printed p.35. No monotonicity for arbitrary quotients is asserted.
-/

public section

variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- A coprime kernel loses none of the domain's prime rank. -/
theorem primeRank_le_of_coprime_ker (p : ℕ) [Fact p.Prime]
    (f : G →* H) (hc : Nat.Coprime p (Nat.card f.ker)) :
    primeRank p G ≤ primeRank p H := by
  apply (primeRank_le_iff p _).mpr
  intro A hp ha
  let := ha
  have hi := Subgroup.injective_comp_subtype_of_coprime_ker f hc A hp
  let e : A ≃* A.map f := MulEquiv.ofBijective (f.subgroupMap A)
    ⟨fun _ _ h => hi (congrArg Subtype.val h), f.subgroupMap_surjective A⟩
  rw [Group.rank_congr e]
  exact (primeRank_le_iff p _).mp le_rfl (A.map f) (hp.map f) inferInstance

/-- Surjections with coprime kernel preserve prime rank. -/
theorem primeRank_eq_of_surjective_of_coprime (p : ℕ) [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f)
    (hc : Nat.Coprime p (Nat.card f.ker)) : primeRank p G = primeRank p H :=
  le_antisymm (primeRank_le_of_coprime_ker p f hc)
    (primeRank_le_of_surjective_of_coprime p f hf hc)

/-- Quotienting by a normal two-subgroup preserves every odd prime rank. -/
theorem primeRank_quotient_eq_of_isTwoGroup (p : ℕ) [Fact p.Prime]
    (ho : Odd p) (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N) :
    primeRank p (G ⧸ N) = primeRank p G := by
  apply (primeRank_eq_of_surjective_of_coprime p (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) ?_).symm
  rw [QuotientGroup.ker_mk']
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hN
  rw [hn]
  exact (Nat.coprime_two_right.mpr ho).pow_right n
