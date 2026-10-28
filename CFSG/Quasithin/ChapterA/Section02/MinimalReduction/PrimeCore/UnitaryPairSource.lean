module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.CenterPreimage
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.UnitaryPairCovers

/-!
# Excluding a non-offending central Sylow kernel

A.2.10 and the Frattini reduction make the original center odd. If induction
produces the complete rank-three unitary-pair quotient and the source action
argument centralizes its q-kernel, the actual quotient cover has three-group
center. Its q-group kernel is therefore trivial for q different from three.
The perfect-cover and odd-center hypotheses are discharged from the original
counterexample; centralization and the earlier inductive quotient are the
remaining source inputs at this boundary.

Source: Aschbacher–Smith A.2.11, printed p.35.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- The original center has odd order by its inclusion in the already
identified center preimage, not by assuming a cover classification. -/
theorem CounterexampleToTheoremA.center_odd_card
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G) :
    Odd (Nat.card (center G)) := by
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  have ho := h.center_preimage_odd_card ih f hf
  rw [h.center_preimage_eq_fitting ih f hf] at ho
  have hcf : center G ≤ fittingSubgroup G := le_sSup ⟨inferInstance, inferInstance⟩
  exact Nat.coprime_two_left.mp
    ((Nat.coprime_two_left.mpr ho).of_dvd_right (card_dvd_of_le hcf))

/-- The non-offending central kernel vanishes once the source unitary
exception has been obtained on the actual quotient. -/
theorem CounterexampleToTheoremA.central_kernel_eq_bot_of_unitary_pair
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (N : Subgroup G) [N.Normal] (hN : N ≤ center G)
    {q : ℕ} [Fact q.Prime] (hq : q ≠ 3) (hNp : IsPGroup q N)
    (d : TheoremAUnitaryPair (G ⧸ N)) (hr : primeRank 3 (G ⧸ N) = 3) :
    N = ⊥ := by
  let f : PerfectCentralCovering.Cover G (G ⧸ N) :=
    { toMonoidHom := QuotientGroup.mk' N
      surjective := QuotientGroup.mk'_surjective N
      isPerfect := h.isPerfect ih
      ker_le_center := by simpa only [QuotientGroup.ker_mk'] using hN }
  have hk : f.toMonoidHom.ker = N := QuotientGroup.ker_mk' N
  exact hk ▸ d.cover_kernel_eq_bot_of_ne_three hr f (h.center_odd_card ih) hq (hk.symm ▸ hNp)

end CFSG.Quasithin.ChapterA.Section02
