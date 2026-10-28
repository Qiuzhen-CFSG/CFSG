module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.SimpleQuotient
public import Theory.GroupTheory.NilpotentPrimeCover
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.OffendingPrime
/-!
# The offending core rank from actual prime-kernel exclusion

If the original offending p-core has rank at most two, the source action
argument makes it central. Removing the characteristic p′-part of the
nilpotent marked kernel then constructs a genuine perfect central p-cover
of S/Z(S) with nontrivial p-kernel. Any actual model theorem excluding that
kernel forces the original p-core to have rank greater than two. The
ordinary-rank clause of Theorem A is then vacuous, so the literal failure
witness forces local p-rank greater than two in S.

The model-specific kernel exclusion remains explicit and is consumed by
the defining signed-three source family. No quotient-quasithinness is used.
Source: Aschbacher–Smith A.2.11–12, printed pp.35–36.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.exists_nontrivial_central_prime_cover_of_core_rank_le_two
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hr : primeRank p (pCore p G) ≤ 2) :
    ∃ (N : Subgroup G) (_ : N.Normal), Nat.Coprime p (Nat.card N) ∧
      ∃ c : PerfectCentralCovering.Cover (G ⧸ N) (S ⧸ center S),
        IsPGroup p c.toMonoidHom.ker ∧ p ∣ Nat.card c.toMonoidHom.ker := by
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  let := h.isPerfect ih
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  let g := (QuotientGroup.mk' (center S)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hk : g.ker = (center S).comap f := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hnil : Group.IsNilpotent g.ker := hk ▸ h.center_preimage_isNilpotent ih f hf
  have hpd : p ∣ Nat.card g.ker := by
    apply (h.prime_dvd_cover_kernel ih f hf).trans (card_dvd_of_le ?_)
    rw [hk]
    intro x hx
    change f x ∈ center S
    rw [show f x = 1 from hx]
    exact one_mem _
  obtain ⟨N, hN, hNc, c, hcp, hcd⟩ :=
    exists_central_prime_cover_of_nilpotent_kernel p g hg hnil
      (h.primeCore_le_center_of_rank_le_two ih h.2.2.2.2.2.1 hr)
  exact ⟨N, hN, hNc, c, hcp, hcd hpd⟩

theorem CounterexampleToTheoremA.core_rank_gt_two_of_no_defining_central_cover
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hcover : ∀ (L : Type u) [Group L] [Finite L]
      (c : PerfectCentralCovering.Cover L (S ⧸ center S)),
      ¬ p ∣ Nat.card c.toMonoidHom.ker) :
    2 < primeRank p (pCore p G) := by
  by_contra hr
  obtain ⟨N, hN, _, c, _, hd⟩ :=
    h.exists_nontrivial_central_prime_cover_of_core_rank_le_two ih (by omega)
  let := hN
  exact hcover (G ⧸ N) c hd

theorem CounterexampleToTheoremA.local_rank_gt_two_of_no_defining_central_cover
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hcover : ∀ (L : Type u) [Group L] [Finite L]
      (c : PerfectCentralCovering.Cover L (S ⧸ center S)),
      ¬ p ∣ Nat.card c.toMonoidHom.ker) :
    2 < twoLocalPrimeRank p S := by
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  have hcore := h.core_rank_gt_two_of_no_defining_central_cover ih hcover
  have hbig : 2 < primeRank p G := hcore.trans_le
    (Theory.GroupTheory.primeRank_le_of_injective p (pCore p G).subtype (pCore p G).subtype_injective)
  by_contra hl
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  have hp : p ≠ 2 := by
    intro he
    have ho := h.2.2.2.2.2.1
    rw [he] at ho
    norm_num at ho
  have hi := TwoLocalPrimeRank.le_of_surjective_of_target_le_two hp f hf (by omega)
  exact h.2.2.2.2.2.2 ⟨Or.inl ⟨hi,
    isQuasithin_iff_twoLocalPrimeRank.mp h.1 p h.2.2.2.2.1 h.2.2.2.2.2.1⟩,
    fun hh => (not_le_of_gt hbig hh).elim⟩

theorem CounterexampleToTheoremA.centralQuotient_local_rank_gt_two_of_no_prime_cover
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hcover : ∀ (L : Type u) [Group L] [Finite L]
      (c : PerfectCentralCovering.Cover L (S ⧸ center S)),
      ¬ p ∣ Nat.card c.toMonoidHom.ker) :
    2 < twoLocalPrimeRank p (S ⧸ center S) := by
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  let c : PerfectCentralCovering.Cover S (S ⧸ center S) :=
    { toMonoidHom := QuotientGroup.mk' (center S)
      surjective := QuotientGroup.mk'_surjective _
      isPerfect := h.2.2.2.1.isPerfect
      ker_le_center := by rw [QuotientGroup.ker_mk'] }
  have hp : Nat.Coprime p (Nat.card c.toMonoidHom.ker) :=
    h.2.2.2.2.1.coprime_iff_not_dvd.mpr (hcover S c)
  have ht : Nat.Coprime 2 (Nat.card c.toMonoidHom.ker) := by
    change Nat.Coprime 2 (Nat.card (QuotientGroup.mk' (center S)).ker)
    rw [QuotientGroup.ker_mk']
    exact Nat.coprime_two_left.mpr (h.section_center_odd_card ih)
  rw [← twoLocalPrimeRank_eq_of_surjective_of_coprime p c.toMonoidHom c.surjective hp ht]
  exact h.local_rank_gt_two_of_no_defining_central_cover ih hcover

end CFSG.Quasithin.ChapterA.Section02
