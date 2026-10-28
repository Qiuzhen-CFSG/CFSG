module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank

/-!
# The odd PSL₂ automorphism-rank inputs to G.7.3(1)

For an actual PSL₂(pᵉ) model, with p odd, e positive and pᵉ > 3, the
full automorphism group has two-rank at most three. For PSL₂(17) the
bound is two, as it is for every prime-field model with p > 3.

Transport the intrinsic semilinear bounds through the multiplicative
equivalence in `ClassicalGroup.IsPSL`, then through the induced equivalence
of automorphism groups. No rank or automorphism-coverage premise is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, proof of G.7.3(1), printed p.348
(PDF p.359). These are the rank inputs; the degree/rank comparison and
the remaining alternatives belong to the G.7.3 assembly.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section07.OddCharacteristic

open Theory.GroupTheory

/-- The general rank input, including field and diagonal automorphisms. -/
theorem psl2_automorphism_two_rank_le_three
    {L : Type*} [Group L] [Finite L] {p e : ℕ}
    (hp : p.Prime) (hodd : Odd p) (he : 0 < e) (hlarge : 3 < p ^ e)
    (hL : ClassicalGroup.IsPSL L 2 (p ^ e)) : primeRank 2 (MulAut L) ≤ 3 := by
  obtain ⟨K, _, _, hcard, ⟨f⟩⟩ := hL
  rw [primeRank_equiv 2 (MulAut.congr f)]
  exact Theory.PSL2.odd_automorphism_two_rank K
    ⟨p, e, hp, hodd, he, hcard⟩ (hcard ▸ hlarge)

/-- Prime-field models have the sharper bound because the field factor vanishes. -/
theorem psl2_prime_automorphism_two_rank_le_two
    {L : Type*} [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (hlarge : 3 < p)
    (hL : ClassicalGroup.IsPSL L 2 p) : primeRank 2 (MulAut L) ≤ 2 := by
  obtain ⟨K, _, _, hcard, ⟨f⟩⟩ := hL
  let : Fact p.Prime := ⟨hp⟩
  rw [primeRank_equiv 2 (MulAut.congr f)]
  exact Theory.PSL2.prime_card_automorphism_two_rank K hcard hlarge

/-- The exceptional parameter 17 in the G.7.3(1) degree comparison. -/
theorem psl2_seventeen_automorphism_two_rank_le_two
    {L : Type*} [Group L] [Finite L]
    (hL : ClassicalGroup.IsPSL L 2 17) : primeRank 2 (MulAut L) ≤ 2 :=
  psl2_prime_automorphism_two_rank_le_two (by decide) (by decide) hL

end CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
