module

public import Theory.GroupTheory.Amalgam.RankTwoCompletion

/-!
# Transporting the normal core of a marked overlap

For two faithful completions of the same rank-two amalgam, a normal subgroup
contained in one marked middle image transports to a normal subgroup of the
other completion. Its preimages in each endpoint are normal; compatibility of
both middle maps identifies their transported images, and generation gives
ambient normality. Consequently a trivial middle core transfers between the
completions without a coprime-index or whole-intersection assumption.

This is the kernel argument for coset actions of marked amalgams, used in
Aschbacher–Smith F.3–F.4. The whole-intersection condition, when needed to
identify the coset-action kernel, must still be established separately.
-/

@[expose] public section

open Subgroup
open Theory.GroupTheory

namespace Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion

variable {L B R G H : Type*} [Group L] [Group B] [Group R] [Group G] [Group H]
variable {α : RankTwoAmalgam L B R}

private theorem preimage_eq_map_middle {A C X : Type*} [Group A] [Group C] [Group X]
    (i : A →* C) (f : C →* X) (hf : Function.Injective f)
    (N : Subgroup X) (hN : N ≤ (f.comp i).range) :
    N.comap f = (N.comap (f.comp i)).map i := by
  ext x
  constructor
  · intro hx
    obtain ⟨b, hb⟩ := hN hx
    have he : i b = x := hf hb
    refine ⟨b, ?_, he⟩
    change f (i b) ∈ N
    rw [he]
    exact hx
  · rintro ⟨b, hb, rfl⟩
    exact hb

/-- Transport an ambient normal subgroup contained in the marked middle. -/
theorem map_middle_preimage_normal (c : FaithfulCompletion α (G := G))
    (d : FaithfulCompletion α (G := H)) (N : Subgroup G) [N.Normal]
    (hN : N ≤ c.middle.range) : ((N.comap c.middle).map d.middle).Normal := by
  let M := (N.comap c.middle).map d.middle
  have hl : M = (N.comap c.left).map d.left := by
    rw [preimage_eq_map_middle α.left c.left c.left_injective N hN, map_map]
  have hr : M = (N.comap c.right).map d.right := by
    have hNr : N ≤ (c.right.comp α.right).range := by
      rw [← c.compatible]
      exact hN
    rw [preimage_eq_map_middle α.right c.right c.right_injective N hNr, map_map]
    change (N.comap (c.left.comp α.left)).map (d.left.comp α.left) = _
    rw [c.compatible, d.compatible]
  change M.Normal
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← d.generated]
  apply sup_le
  · rw [hl]
    have hh := (N.comap c.left).le_normalizer_map d.left
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map] using hh
  · rw [hr]
    have hh := (N.comap c.right).le_normalizer_map d.right
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map] using hh

/-- Triviality of the marked middle core is independent of the faithful completion. -/
theorem middle_normalCore_eq_bot_of_model (c : FaithfulCompletion α (G := G))
    (d : FaithfulCompletion α (G := H)) (hd : d.middle.range.normalCore = ⊥) :
    c.middle.range.normalCore = ⊥ := by
  let N := c.middle.range.normalCore
  let M := (N.comap c.middle).map d.middle
  have hN : N ≤ c.middle.range := c.middle.range.normalCore_le
  have hM : M ≤ d.middle.range := map_le_range _ _
  let : M.Normal := map_middle_preimage_normal c d N hN
  have hMb : M = ⊥ := le_bot_iff.mp (hd ▸ normal_le_normalCore.mpr hM)
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨b, hb⟩ := hN hx
  have hbm : d.middle b ∈ M := ⟨b, by change c.middle b ∈ N; rw [hb]; exact hx, rfl⟩
  rw [hMb] at hbm
  have hb1 : b = 1 := d.middle_injective
    ((show d.middle b = 1 from hbm).trans (map_one d.middle).symm)
  change x = 1
  simpa only [hb1, map_one] using hb.symm

end Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
