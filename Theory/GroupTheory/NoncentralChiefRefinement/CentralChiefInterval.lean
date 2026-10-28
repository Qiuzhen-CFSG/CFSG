module
public import Theory.GroupAction.NormalPChiefSeries
public import Theory.GroupTheory.NoncentralChiefRefinement.Transport

/-!
# A single chief interval between central strata

If a normal two-subgroup has a central initial stratum, a single noncentral
chief interval, and a central terminal stratum, every ambient chief series
on that subgroup has exactly one noncentral factor. Refine the outer strata,
concatenate through the given interval, and use equivariant Jordan–Hölder.

The original class-two branch of Niles, *Pushing-up in finite groups*
(1979), Proposition 5.5(a), uses this with Z(H) < Z(O₂(H)).
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {H : Type*} [Group H] [Finite H]

/-- Central outer strata contribute no factors to the count around the
given noncentral chief interval. -/
theorem SeriesOn.noncentralCount_eq_one_of_central_chief_strata
    {U : Subgroup H} [U.Normal] (hp : IsPGroup 2 U)
    (A B : NormalNode H) (hA : IsCentral ⊥ A)
    (hAB : A ⋖ B) (hn : ¬ IsCentral A B) (hBU : B.val ≤ U)
    (hU : IsCentral B ⟨U, inferInstanceAs U.Normal⟩)
    (s : SeriesOn U) : s.noncentralCount = 1 := by
  obtain ⟨a, ha0, ha1⟩ := exists_chiefSeries (⊥ : NormalNode H) A bot_le
  let b : ChiefSeries H := (RelSeries.singleton _ A).snoc B hAB
  obtain ⟨c, hc0, hc1⟩ := exists_chiefSeries B ⟨U, inferInstanceAs U.Normal⟩ hBU
  have hab : a.last = b.head := ha1
  have hbc : (a.smash b hab).last = c.head :=
    (RelSeries.last_smash hab).trans ((RelSeries.last_snoc _ _ _).trans hc0.symm)
  have ha : a.noncentralTwoCount = 0 := by
    apply a.noncentralTwoCount_eq_zero_of_central
    rwa [ha0, ha1]
  have hb : b.noncentralTwoCount = 1 := by
    change Nat.card {i : Fin 1 // IsNoncentralTwo (b i.castSucc) (b i.succ)} = 1
    apply Nat.card_eq_one_iff_exists.mpr
    have hi : IsNoncentralTwo (b (0 : Fin 1).castSucc) (b (0 : Fin 1).succ) :=
      by
        change IsNoncentralTwo A B
        exact ⟨(hp.to_le hBU).to_quotient _, hn⟩
    refine ⟨⟨0, hi⟩, ?_⟩
    intro i
    apply Subtype.ext
    exact Subsingleton.elim _ _
  have hc : c.noncentralTwoCount = 0 := by
    apply c.noncentralTwoCount_eq_zero_of_central
    rwa [hc0, hc1]
  rw [s.noncentralCount_eq_twoCount hp,
    s.series.noncentralTwoCount_eq ((a.smash b hab).smash c hbc)
      (by simpa using s.head_eq.trans ha0.symm)
      (by simpa using s.last_eq.trans hc1.symm),
    ChiefSeries.noncentralTwoCount_smash, ChiefSeries.noncentralTwoCount_smash,
    ha, hb, hc]
end NoncentralChiefRefinement
