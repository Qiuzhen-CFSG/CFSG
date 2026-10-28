module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.Data
public import Theory.GroupTheory.PrimeSubgroupInvolution
public import Theory.GroupAction.InvertedOddSupportDisplacement
public import Theory.GroupAction.FixedCoatomDisplacement

/-!
# Locating the source line in the first five-support

An involution normalizing and moving a five-factor inverts it. Its displacement
on that factor's support has order four, which is already the order of its
whole displacement. The whole displacement therefore lies in the first
canonical support. The image of D_H has index dividing two. If its displacement
were trivial, the whole displacement would have order at most two. Thus its
nontrivial displacement fills the image of A₁, placing that actual source line
in the first support.

Normalization of the first factor remains an explicit algebraic input here.
This module proves its support consequences, not the existence of the second
actor or the source solvable-overgroup exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951, the final paragraph and the equality Ã₁ = [D̃_H,Uγ] ≤ Ũ₁.
-/

@[expose] public section


open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.SecondActor

private theorem involution_moved_le_five_support
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (A R : Subgroup (MulAut W)) (hA : Nat.card A = 2) (hR : Nat.card R = 5)
    (hS : Nat.card (commutatorAction R W) = 16)
    (hD : Nat.card (commutatorAction A W) = 4)
    (hn : A ≤ normalizer (R : Set (MulAut W)))
    (hm : ⁅A, R⁆ ≠ ⊥) : commutatorAction A W ≤ commutatorAction R W := by
  classical
  have hnc : ¬ A ≤ centralizer (R : Set (MulAut W)) :=
    fun h => hm (commutator_eq_bot_iff_le_centralizer.mpr h)
  obtain ⟨t, ht, htc⟩ := SetLike.not_le_iff_exists.mp hnc
  have htne : t ≠ 1 := fun he => htc (he ▸ one_mem _)
  have ht2 : t ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨t, ht⟩ : A))
    rw [hA] at hh
    exact congrArg Subtype.val hh
  have htA : zpowers t = A := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr ht)
    rw [Nat.card_zpowers, orderOf_eq_prime ht2 htne, hA]
  have hinv : ∀ r ∈ R, t * r * t⁻¹ = r⁻¹ := by
    rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one R
      (by rw [hR]; decide) t ht2 (hn ht) with hc | hi
    · exact (htc (mem_centralizer_iff.mpr fun r hr => (hc r hr).eq.symm)).elim
    · exact hi
  obtain ⟨_, S, _, hSR, hSA, hcard, _⟩ :=
    inverted_odd_support_displacement_packet R (by rw [hR]; decide)
      (fun he => by rw [he, card_bot] at hR; omega) t ⟨htne, ht2⟩ hinv
  rw [htA] at hSA
  have he : S = commutatorAction A W := by
    apply eq_of_le_of_card_ge hSA
    rw [hD]
    rw [hS] at hcard
    nlinarith
  exact he ▸ hSR


private theorem line_le_moved_of_coatom
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (A : Subgroup (MulAut W)) (D Z : Subgroup W)
    (hA : Nat.card A = 2) (hD : D.index ∣ 2) (hZ : Nat.card Z ≤ 2)
    (hm : Nat.card (commutatorAction A W) = 4)
    (hc : commutatorSubgroup A W D ≤ Z) : Z ≤ commutatorAction A W := by
  classical
  obtain ⟨t, ht, _⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  have ht2 : (t : MulAut W) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := t)
    rw [hA] at hh
    exact congrArg Subtype.val hh
  have htne : (t : MulAut W) ≠ 1 := fun he => ht (Subtype.ext he)
  have htA : zpowers (t : MulAut W) = A := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr t.property)
    rw [Nat.card_zpowers, orderOf_eq_prime ht2 htne, hA]
  have hne : commutatorSubgroup A W D ≠ ⊥ := by
    intro he
    have hfixed : D ≤ FixedPoints.subgroup (zpowers (t : MulAut W)) W := by
      rw [htA]
      intro w hw b
      have hh : w⁻¹ * (b • w) ∈ commutatorSubgroup A W D :=
        subset_closure ⟨b, w, hw, rfl⟩
      rw [he, mem_bot] at hh
      exact (inv_mul_eq_one.mp hh).symm
    have hb := MulAut.commutatorAction_card_le_two_of_fixed_index_dvd_two
      (t : MulAut W) ((index_dvd_of_le hfixed).trans hD)
    rw [htA, hm] at hb
    omega
  have hpos := Nat.card_pos (α := commutatorSubgroup A W D)
  have hn : Nat.card (commutatorSubgroup A W D) ≠ 1 :=
    fun he => hne (card_eq_one.mp he)
  have he : commutatorSubgroup A W D = Z :=
    eq_of_le_of_card_ge hc (by omega)
  rw [← he]
  exact closure_mono (by rintro _ ⟨b, w, _, rfl⟩; exact ⟨b, w, mem_top w, rfl⟩)


variable {G : Type*} [Group G] [Finite G]
variable {H UH V₁ P Uγ A₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]
variable [IsElementaryAbelian 2 (UH ⧸ V₁.subgroupOf UH)]

/-- The full rank-one displacement lies in its first canonical five-support. -/
theorem moved_le_first
    (a : StarAction H UH V₁) (hf : Function.Injective a.action)
    (f : RankOneFactors a P Uγ)
    (hn : Source.starImage H Uγ ≤
      normalizer (Source.starImage H (f.factors.factor ⟨0, f.factors.count_pos⟩) : Set _)) :
    commutatorAction (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH) ≤
      f.factors.support ⟨0, f.factors.count_pos⟩ := by
  apply involution_moved_le_five_support (a.actors Uγ)
    (a.actors (f.factors.factor ⟨0, f.factors.count_pos⟩))
  · exact (card_map_of_injective hf).trans f.actor_card
  · exact (card_map_of_injective hf).trans (f.factors.star_card _)
  · exact f.factors.support_card _
  · exact f.moved_card
  · exact (map_mono hn).trans (le_normalizer_map a.action)
  · intro he
    apply f.first_moved
    apply map_injective hf
    simpa only [map_commutator, Subgroup.map_bot, StarAction.actors] using he


/-- The actual source line is forced into the full displacement by the D_H index. -/
theorem line_le_moved [IsMulCommutative UH]
    (a : StarAction H UH V₁) (hf : Function.Injective a.action)
    (f : RankOneFactors a P Uγ)
    (hUγ : Uγ ≤ H) (hA : A₁ ≤ UH) (hAcard : Nat.card A₁ = 2)
    (hindex : (Source.DH UH Uγ A₁).relIndex UH = 2) :
    tildeImage UH V₁ A₁ ≤ commutatorAction (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH) := by
  apply line_le_moved_of_coatom (a.actors Uγ) (tildeImage UH V₁ (Source.DH UH Uγ A₁))
  · exact (card_map_of_injective hf).trans f.actor_card
  · exact ((Source.DH UH Uγ A₁).subgroupOf UH).index_map_dvd
      (QuotientGroup.mk'_surjective _) |>.trans (show ((Source.DH UH Uγ A₁).subgroupOf UH).index ∣ 2 by change (Source.DH UH Uγ A₁).relIndex UH ∣ 2; rw [hindex])
  · have hh := Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' (V₁.subgroupOf UH)) (A₁.subgroupOf UH))
    rw [Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv, hAcard] at hh
    exact hh
  · exact f.moved_card
  · rw [a.commutatorSubgroup_eq_tildeImage (Source.DH UH Uγ A₁) Uγ
      (show Source.DH UH Uγ A₁ ≤ UH from commutatorPreimage_le _ _ _) hUγ]
    apply map_mono
    intro x hx
    exact commutator_commutatorPreimage_le UH Uγ A₁
      ((UH.le_centralizer.trans (centralizer_le hA)).trans (centralizer_le_normalizer _)) hx


/-- First-support containment of the actual quotient image of A₁. -/
theorem line_le_first [IsMulCommutative UH]
    (a : StarAction H UH V₁) (hf : Function.Injective a.action)
    (f : RankOneFactors a P Uγ)
    (hUγ : Uγ ≤ H) (hA : A₁ ≤ UH) (hAcard : Nat.card A₁ = 2)
    (hindex : (Source.DH UH Uγ A₁).relIndex UH = 2)
    (hn : Source.starImage H Uγ ≤
      normalizer (Source.starImage H (f.factors.factor ⟨0, f.factors.count_pos⟩) : Set _)) :
    tildeImage UH V₁ A₁ ≤ f.factors.support ⟨0, f.factors.count_pos⟩ :=
  (line_le_moved a hf f hUγ hA hAcard hindex).trans (moved_le_first a hf f hn)

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.SecondActor
