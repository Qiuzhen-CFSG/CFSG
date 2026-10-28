module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalBasic
public import Theory.GroupTheory.PPrimeCorePGroupQuotient
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.ZStar.CoreFree

/-!
# The global Z-star obstruction in GLS Lemma 4.10

An even simple normal subgroup complemented by an external involution has
trivial odd core: the simple subgroup has trivial odd core and the quotient
has order two. Thus a Sylow-central weakly closed involution would be central
by the core-free Z-star theorem. The absence of nontrivial solvable normal
subgroups rules this out.

This proves the global obstruction needed for clause (c), independently of
the local Sylow isolation argument. It uses the actual normal subgroup and
its even order, without the odd-order theorem.

Source: GLS, Volume 4, Chapter 2, Lemma 4.10(c),
`refs/KGroup/GLS4/Chapter2.tex`, lines 704–708.
-/

namespace BenderSuzuki.ZD.Centralizers
open PFAppendixIII Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Trivial odd core ascends from the even simple normal subgroup across
its quotient of order two. -/
public theorem oddCore_eq_bot_of_simple_normal_extension
    (N : Subgroup G) [N.Normal] [IsSimpleGroup N]
    (hNeven : Even (Nat.card N)) {z : G} (hz : PFAppendixIII.IsInvolution z)
    (hgen : N ⊔ Subgroup.zpowers z = ⊤) (hzN : z ∉ N) :
    pPrimeCore 2 G = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNcore : pPrimeCore 2 N = ⊥ := by
    rcases (pPrimeCore_normal (p := 2) (G := N)).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hc := pPrimeCore_coprime_card (p := 2) (G := N)
      rw [ht, Subgroup.card_top] at hc
      exact (Nat.prime_two.coprime_iff_not_dvd.mp hc hNeven.two_dvd).elim
  have hzNorm : z ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    trivial
  have hcard : Nat.card G = 2 * Nat.card N := by
    simpa only [hgen, Subgroup.card_top] using
      Subgroup.card_sup_zpowers_of_normalizing_involution N z hz.sq_eq_one hzN hzNorm
  have hquot : Nat.card (G ⧸ N) = 2 := by
    have heq := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hpos : 0 < Nat.card N := Nat.card_pos
    nlinarith
  exact pPrimeCore_eq_bot_of_isPGroup_quotient 2 N hNcore
    (IsPGroup.of_card (n := 1) (by simpa using hquot))

/-- The Z-star obstruction used after constructing the Sylow subgroup in
Lemma 4.10(c). The Sylow isolation premise remains to be proved locally. -/
public theorem not_weaklyClosed_of_simple_normal_extension
    (hsol : ∀ A : Subgroup G, A.Normal → Group.IsSolvable A → A = ⊥)
    (N : Subgroup G) [N.Normal] [IsSimpleGroup N]
    (hNeven : Even (Nat.card N)) {z : G} (hz : PFAppendixIII.IsInvolution z)
    (hgen : N ⊔ Subgroup.zpowers z = ⊤) (hzN : z ∉ N)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzC : ∀ s : S, Commute z (s : G)) :
    ¬ Glauberman.ZStar.IsWeaklyClosedInSylow z (S : Subgroup G) := by
  intro hweak
  have hzZ := Glauberman.ZStar.glauberman_zstar_corefree
    (oddCore_eq_bot_of_simple_normal_extension N hNeven hz hgen hzN)
    S z hz hzS (fun s hs => (hzC ⟨s, hs⟩).eq.symm) hweak
  rw [hsol (Subgroup.center G) inferInstance
    (Group.isSolvable_of_comm (fun x y => mul_comm' x y))] at hzZ
  exact hz.ne_one hzZ

end BenderSuzuki.ZD.Centralizers
