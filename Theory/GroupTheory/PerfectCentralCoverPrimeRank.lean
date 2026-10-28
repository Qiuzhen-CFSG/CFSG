module

public import Theory.GroupTheory.PerfectCentralCover
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero

/-!
# Odd prime rank in perfect central covers

If the target of a finite perfect central cover has odd prime rank at most
one, its Sylow subgroups at that prime are cyclic. Transfer excludes that
prime from the central kernel, and the kernel--image rank inequality gives
the same bound for the source. Thus odd prime rank at least two survives a
perfect central cover. No assertion about arbitrary central quotients is used.

Source: Aschbacher--Smith I.1.2 and A.2.7, and the projection step in I.3.1(3).
-/

public section

namespace PerfectCentralCovering
open Subgroup Theory.GroupTheory

variable {L S : Type*} [Group L] [Finite L] [Group S] [Finite S]
variable {p : ℕ} [Fact p.Prime]

theorem Cover.primeRank_le_one_of_target_le_one (f : Cover L S)
    (hp : Odd p) (hr : primeRank p S ≤ 1) : primeRank p L ≤ 1 := by
  have hn : ¬ p ∣ Nat.card f.toMonoidHom.ker :=
    f.not_dvd_card_multiplier_of_isCyclic_sylow
      (fun Q => Q.isCyclic_of_odd_of_primeRank_le_one hp hr)
  have hz : primeRank p f.toMonoidHom.ker = 0 :=
    PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
  have h := primeRank_le_ker_add (p := p) f.toMonoidHom
  rw [hz, zero_add] at h
  exact h.trans hr

theorem Cover.two_le_primeRank_target (f : Cover L S)
    (hp : Odd p) (hr : 2 ≤ primeRank p L) : 2 ≤ primeRank p S := by
  by_contra h
  have h' := f.primeRank_le_one_of_target_le_one hp (by omega)
  omega

/-- Apply the transfer argument to the literal central quotient. -/
theorem two_le_primeRank_central_quotient [Group.IsPerfect L]
    (hp : Odd p) (hr : 2 ≤ primeRank p L) :
    2 ≤ primeRank p (L ⧸ center L) := by
  let f : Cover L (L ⧸ center L) := {
    toMonoidHom := QuotientGroup.mk' (center L)
    surjective := QuotientGroup.mk'_surjective _
    isPerfect := inferInstance
    ker_le_center := (QuotientGroup.ker_mk' _).le }
  exact f.two_le_primeRank_target hp hr

end PerfectCentralCovering
