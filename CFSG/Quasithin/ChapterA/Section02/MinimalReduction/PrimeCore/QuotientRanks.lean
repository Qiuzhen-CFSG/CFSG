module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.CenterPreimage
public import Theory.Quasithin.CoprimeLocalRank

/-!
# Ranks in the actual non-offending Sylow quotient

Each Sylow subgroup of the center preimage is normal by the minimal
covering argument. At an odd prime distinct from the offending prime,
quotienting by that literal subgroup preserves both the ordinary and
two-local offending-prime ranks. Both quotient maps retain the original
surjection and its center preimage.

Source: Aschbacher–Smith A.2.11, printed p.35.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p q : ℕ}

theorem CounterexampleToTheoremA.other_sylow_quotient_ranks
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f) [Fact q.Prime]
    (hq : Odd q) (hne : p ≠ q) (Q : Sylow q ((center S).comap f)) :
    let N := (Q : Subgroup ((center S).comap f)).map ((center S).comap f).subtype
    let : N.Normal := h.center_preimage_sylow_normal ih f hf q Q
    primeRank p (G ⧸ N) = primeRank p G ∧
      twoLocalPrimeRank p (G ⧸ N) = twoLocalPrimeRank p G := by
  dsimp only
  let N := (Q : Subgroup ((center S).comap f)).map ((center S).comap f).subtype
  let : N.Normal := h.center_preimage_sylow_normal ih f hf q Q
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  have hN : IsPGroup q N := Q.isPGroup'.map ((center S).comap f).subtype
  obtain ⟨n, hn⟩ := hN.exists_card_eq
  have hc : Nat.Coprime p (Nat.card N) := by
    rw [hn]
    exact (Nat.coprime_primes h.2.2.2.2.1 Fact.out |>.mpr hne).pow_right n
  have hc2 : Nat.Coprime 2 (Nat.card N) := by
    rw [hn]
    exact (Nat.coprime_two_left.mpr hq).pow_right n
  let π := QuotientGroup.mk' N
  have hpker : Nat.Coprime p (Nat.card π.ker) := by simpa [π] using hc
  have h2ker : Nat.Coprime 2 (Nat.card π.ker) := by simpa [π] using hc2
  exact ⟨(primeRank_eq_of_surjective_of_coprime p π (QuotientGroup.mk'_surjective N)
      hpker).symm,
    (twoLocalPrimeRank_eq_of_surjective_of_coprime p π (QuotientGroup.mk'_surjective N)
      hpker h2ker).symm⟩

end CFSG.Quasithin.ChapterA.Section02
