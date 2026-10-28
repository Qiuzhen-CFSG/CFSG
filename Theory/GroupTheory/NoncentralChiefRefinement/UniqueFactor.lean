module
public import Theory.GroupAction.NormalPChiefSeries
public import Theory.GroupTheory.NoncentralChiefRefinement.Transport
/-!
# Identifying the unique noncentral chief factor

A specified noncentral chief interval inside a normal subgroup can be inserted
into a chief series of that subgroup. Equivariant Jordan–Hölder matches it to
an interval of any other series with the same endpoints. If that series has
exactly one noncentral factor, the match identifies every noncentral interval
with the specified section, preserving the ambient conjugation action.

Source application: Niles, “Pushing-up in finite groups” (1979), Theorem B,
printed p.28: the unique noncentral chief factor is the actual natural module.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {H : Type*} [Group H] [Finite H]

theorem SeriesOn.sectionEquiv_of_count_one
    {U : Subgroup H} [U.Normal] (s : SeriesOn U) (hs : s.noncentralCount = 1)
    (A B : NormalNode H) (hAB : A ⋖ B) (hBU : B.val ≤ U) (hn : ¬ IsCentral A B)
    (i : Fin s.series.length) (hi : ¬ s.Central i) :
    Nonempty (SectionEquiv (s.lower i) (s.upper i) A B) := by
  obtain ⟨a, ha0, haA⟩ := exists_chiefSeries (⊥ : NormalNode H) A bot_le
  have hstep : a.last ⋖ B := haA ▸ hAB
  let a' : ChiefSeries H := a.snoc B hstep
  obtain ⟨b, hbB, hbU⟩ := exists_chiefSeries B ⟨U, inferInstanceAs U.Normal⟩ hBU
  have hab : a'.last = b.head := (RelSeries.last_snoc a B hstep).trans hbB.symm
  let t : ChiefSeries H := a'.smash b hab
  let j : Fin t.length := (Fin.last a.length).castAdd b.length
  have hj0 : t j.castSucc = A :=
    (RelSeries.smash_castAdd (p := a') (q := b) hab (Fin.last a.length)).trans
      ((RelSeries.snoc_castSucc a B hstep (Fin.last a.length)).trans haA)
  have hj1 : t j.succ = B :=
    (RelSeries.smash_succ_castAdd (p := a') (q := b) hab (Fin.last a.length)).trans
      (RelSeries.last_snoc' a B hstep)
  have ht0 : t.head = s.series.head := by
    simpa only [t, a', RelSeries.head_smash, RelSeries.head_snoc] using ha0.trans s.head_eq.symm
  have ht1 : t.last = s.series.last := (RelSeries.last_smash hab).trans (hbU.trans s.last_eq.symm)
  obtain ⟨f, hf⟩ := ChiefSeries.exists_sectionEquiv_matching t s.series ht0 ht1
  obtain ⟨e⟩ := hf j
  have hjn : ¬ s.Central (f j) := by
    change ¬ IsCentral (s.series (f j).castSucc) (s.series (f j).succ)
    rw [← e.isCentral_iff, hj0, hj1]
    exact hn
  obtain ⟨k, _, hu⟩ := s.noncentralCount_eq_one_iff.mp hs
  have hji : f j = i := (hu _ hjn).trans (hu _ hi).symm
  have ee := e.symm
  rw [hj0, hj1, hji] at ee
  exact ⟨ee⟩
end NoncentralChiefRefinement
