module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.QuotientRanks
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.QuasisimpleCase

/-!
# The offending prime divides the original covering kernel

The source kernel has odd order. If its order were also prime to the
offending prime, coprime lifting would preserve both ordinary and two-local
ranks, giving the nonexceptional conclusion of Theorem A. Hence the
offending prime divides that kernel and, in the quasisimple case, the center.
In particular any independently proved single-prime center restriction
identifies its prime with the offending prime; A.2.11 is unnecessary for
this implication.

Source: Aschbacher–Smith A.2.11–14, printed pp.35–37.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.prime_dvd_cover_kernel
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f) : p ∣ Nat.card f.ker := by
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  have hk : f.ker ≤ (center S).comap f := by
    intro x hx
    change f x ∈ center S
    rw [show f x = 1 from hx]
    exact one_mem _
  have h2 : Nat.Coprime 2 (Nat.card f.ker) :=
    (Nat.coprime_two_left.mpr (h.center_preimage_odd_card ih f hf)).of_dvd_right
      (card_dvd_of_le hk)
  by_contra hn
  have hp : Nat.Coprime p (Nat.card f.ker) :=
    (h.2.2.2.2.1.coprime_iff_not_dvd).mpr hn
  have hr := primeRank_eq_of_surjective_of_coprime p f hf hp
  have hl := twoLocalPrimeRank_eq_of_surjective_of_coprime p f hf hp h2
  apply h.2.2.2.2.2.2
  exact ⟨.inl ⟨hl.symm.le,
    isQuasithin_iff_twoLocalPrimeRank.mp h.1 p Fact.out h.2.2.2.2.2.1⟩,
    fun _ => hr.symm.le⟩

theorem CounterexampleToTheoremA.prime_dvd_center [IsQuasisimple G]
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G) :
    p ∣ Nat.card (center G) := by
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  apply (h.prime_dvd_cover_kernel ih f hf).trans
  apply card_dvd_of_le
  rw [← h.center_preimage_eq_center ih f hf]
  intro x hx
  change f x ∈ center S
  rw [show f x = 1 from hx]
  exact one_mem _

theorem CounterexampleToTheoremA.prime_eq_of_center_isPGroup [IsQuasisimple G]
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {q : ℕ} [Fact q.Prime] (hq : IsPGroup q (center G)) : p = q := by
  obtain ⟨n, hn⟩ := hq.exists_card_eq
  have hd := h.prime_dvd_center ih
  rw [hn] at hd
  exact (Nat.dvd_prime Fact.out).mp (h.2.2.2.2.1.dvd_of_dvd_pow hd) |>.resolve_left
    h.2.2.2.2.1.ne_one

end CFSG.Quasithin.ChapterA.Section02
