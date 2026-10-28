module

public import Theory.Quasithin.LocalRank
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# Odd rank in quotient sections of involution centralizers

The centralizer of an involution is a two-local subgroup. If a subgroup
of that centralizer surjects onto S with kernel coprime to p, then the
p-rank of S is at most the two-local p-rank of the ambient group.
Schur--Zassenhaus supplies the quotient-rank inequality; in particular it
applies at every odd prime when the kernel is a 2-group. Normality is
only required inside the numerator and is automatic for the kernel.

Source: the local-rank obstruction in Aschbacher--Smith, A.2.15(2) and
A.2.19, printed pp. 37 and 40. This special coprime-kernel case does not
require smaller-section induction or simplicity of S.
-/

public section

namespace Theory.Quasithin

variable {G S : Type*} [Group G] [Finite G] [Group S] [Finite S]

/-- A quotient of a subgroup of an involution centralizer contributes to local
prime rank when its kernel has coprime order. -/
theorem primeRank_le_twoLocalPrimeRank_of_centralizer_quotient
    {t : G} (ht : orderOf t = 2) (L : Subgroup G)
    (hL : L ≤ Subgroup.centralizer ({t} : Set G))
    (f : L →* S) (hf : Function.Surjective f)
    (p : ℕ) [Fact p.Prime] (hk : Nat.Coprime p (Nat.card f.ker)) :
    primeRank p S ≤ twoLocalPrimeRank p G := by
  exact (primeRank_le_of_surjective_of_coprime p f hf hk).trans
    ((primeRank_mono p hL).trans
      ((Theory.GroupTheory.isTwoLocal_involution_centralizer ht).primeRank_le p))

/-- In the 2-kernel case all odd-prime ranks lift through the quotient. -/
theorem primeRank_le_twoLocalPrimeRank_of_centralizer_two_quotient
    {t : G} (ht : orderOf t = 2) (L : Subgroup G)
    (hL : L ≤ Subgroup.centralizer ({t} : Set G))
    (f : L →* S) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (p : ℕ) [Fact p.Prime] (ho : Odd p) :
    primeRank p S ≤ twoLocalPrimeRank p G := by
  apply primeRank_le_twoLocalPrimeRank_of_centralizer_quotient ht L hL f hf p
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hk
  rw [hn]
  exact (Nat.coprime_two_right.mpr ho).pow_right n

end Theory.Quasithin
