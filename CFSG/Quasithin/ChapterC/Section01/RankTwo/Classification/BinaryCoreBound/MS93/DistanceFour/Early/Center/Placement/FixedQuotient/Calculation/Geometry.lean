module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry.Planes

/-!
# Full-normalizer generation of the natural fixed space

An order-four subgroup of SL₃(2) has fixed space of order at most four.
If the fixed space is a plane, the subgroup is its pointwise fixer, so its
normalizer is the full plane stabilizer and is transitive on nonzero vectors.
If its order is at most two, every nonzero subgroup already equals it.
This treats cyclic actors as well as elementary abelian actors.

Source: the natural-module calculation in MS93 (1993), (4.6.7), p.904.
-/

public section

open Subgroup Matrix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Escape.Propagation.Backward.Products.Selection.Choices
open Escape.Propagation.Backward.Products.Selection.Choices.FiniteGeometry
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement.Calculation

private def cyclePlane : SL := ⟨!![0,1,0; 1,1,0; 0,0,1], by decide⟩

private theorem cycle_mem : cyclePlane ∈ planeStabilizer standardPlane := by
  rw [mem_planeStabilizer_iff]
  decide +kernel

private theorem cycle_transitive : ∀ u v : Space,
    u ∈ standardPlane → v ∈ standardPlane → u ≠ 1 → v ≠ 1 →
    ∃ i : Fin 3, modelAction (cyclePlane ^ i.val) u = v := by
  decide +kernel

private theorem plane_transitive_nonzero (F : Subgroup Space) (hF : Nat.card F = 4)
    (u v : Space) (hu : u ∈ F) (hv : v ∈ F) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    ∃ g ∈ planeStabilizer F, modelAction g u = v := by
  obtain ⟨a, rfl⟩ := plane_transitive F hF
  obtain ⟨u, hu, rfl⟩ := hu
  obtain ⟨v, hv, rfl⟩ := hv
  have hun : u ≠ 1 := by intro h; subst u; exact hu1 (map_one _)
  have hvn : v ≠ 1 := by intro h; subst v; exact hv1 (map_one _)
  obtain ⟨i, hi⟩ := cycle_transitive u v hu hv hun hvn
  refine ⟨MulAut.conj a (cyclePlane ^ i.val), ?_, ?_⟩
  · rw [planeStabilizer_move]
    exact mem_map_of_mem _ (pow_mem cycle_mem _)
  · change modelAction (MulAut.conj a (cyclePlane ^ i.val)) (modelAction a u) =
      modelAction a v
    rw [action_conj, hi]

private theorem action_faithful (g : SL) (h : ∀ v : Space, modelAction g v = v) :
    g = 1 := by
  apply Subtype.ext
  ext i j
  have hh := congrFun (h (Multiplicative.ofAdd (Pi.single j 1))) i
  change g.val.mulVec (Pi.single j 1) i = (Pi.single j 1 : Fin 3 → ZMod 2) i at hh
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using hh

private theorem fixedSpace_card_cases (B : Subgroup SL) (hB : Nat.card B = 4) :
    Nat.card (fixedSpace B) = 1 ∨ Nat.card (fixedSpace B) = 2 ∨
      Nat.card (fixedSpace B) = 4 := by
  have hc : Nat.card Space = 8 := by
    change Nat.card (Fin 3 → ZMod 2) = 8
    simp
  have hd := (fixedSpace B).card_subgroup_dvd_card
  rw [hc] at hd
  have hcases : Nat.card (fixedSpace B) = 1 ∨ Nat.card (fixedSpace B) = 2 ∨
      Nat.card (fixedSpace B) = 4 ∨ Nat.card (fixedSpace B) = 8 := by
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp
      (show Nat.card (fixedSpace B) ∣ 2 ^ 3 from hd)
    interval_cases k <;> simp_all
  rcases hcases with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · have ht : fixedSpace B = ⊤ := (fixedSpace B).eq_top_of_card_eq (h.trans hc.symm)
    have hb : B = ⊥ := by
      apply eq_bot_iff.mpr
      intro g hg
      apply action_faithful g
      intro v
      exact (show v ∈ fixedSpace B from ht.symm ▸ mem_top v) g hg
    simp [hb] at hB

/-- Any nonzero subgroup of the natural fixed space invariant under the
actor’s full normalizer is the entire fixed space. Only actor order four is used. -/
theorem invariant_fixed_eq (B : Subgroup SL) (hB : Nat.card B = 4)
    (W : Subgroup Space) (hW : W ≤ fixedSpace B) (hne : W ≠ ⊥)
    (hn : ∀ g ∈ normalizer (B : Set SL), ∀ v ∈ W, modelAction g v ∈ W) :
    W = fixedSpace B := by
  obtain ⟨u, hu, hun⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hne)
  rcases fixedSpace_card_cases B hB with hF | hF | hF
  · exact False.elim (hun (by have := hW hu; rwa [card_eq_one.mp hF] at this))
  · apply eq_of_le_of_card_ge hW
    have hc : 1 < Nat.card W := W.one_lt_card_iff_ne_bot.mpr hne
    omega
  · have he : B = planeFixer (fixedSpace B) :=
      eq_of_le_of_card_ge (fun g hg v hv => hv g hg)
        (by rw [planeFixer_card _ hF, hB])
    apply le_antisymm hW
    intro v hv
    by_cases hv1 : v = 1
    · simp [hv1]
    obtain ⟨g, hg, hgu⟩ := plane_transitive_nonzero _ hF u v (hW hu) hv hun hv1
    rw [← hgu]
    apply hn g _ u hu
    rwa [he, planeFixer_normalizer _ hF]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement.Calculation
