module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalNoncyclic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalPlanes
public import Theory.GroupTheory.ConjugateIntersectionCore

/-!
# Centralizer kernels in the non-two conjugate-pair branch

For two actual natural layers whose join is not a two-group, the intersection
of either layer with the other layer's centralizer has order at most two.
Otherwise the natural field-plane core puts the conjugate layer in a two-core,
forcing the join to be a two-group. The index-two normalizer intersection
still has a nontrivial natural action, so the action-rank bound gives the
reverse inequality and identifies the kernel as order two.

This constructs the initial kernel facts in source 6.2.6 for the actual pair;
it does not assert the extraspecial quotient classification. The Chapter 12
companion applies the result to the original whole reduced layer.
Source: Aschbacher--Smith, 6.2.4(1), 6.2.6, printed pp.681--682.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}

/-- A non-two generated pair cannot have a centralizer kernel of order four. -/
theorem local_pair_intersection_centralizer_card_le_two
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (g : G)
    (hnon : ¬ IsPGroup 2 (layer L R ⊔
      (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    Nat.card (layer L R ⊓ centralizer
      ((layer L R).map (MulAut.conj g).toMonoidHom : Set G) : Subgroup G) ≤ 2 := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  have hpB : IsPGroup 2 B := T.isPGroup'.to_le h.layer_le_T
  have hpA : IsPGroup 2 A := hpB.map _
  have hAN : ¬ A ≤ normalizer (B : Set G) := fun hh =>
    hnon (hpB.to_sup_of_normal_left' hpA hh)
  have hAC : A ≤ centralizer (U : Set G) := le_centralizer_iff.mpr inf_le_right
  have hsmall : Nat.card U < 8 := by
    by_contra hh
    have he := local_large_subgroup_centralizer h hnatural hE
      (show U ≤ B from inf_le_left) (Nat.le_of_not_gt hh)
    exact hAN ((hAC.trans_eq he).trans (Subgroup.centralizer_le_normalizer _))
  by_contra hh
  change ¬ Nat.card U ≤ 2 at hh
  have hcard : Nat.card U = 4 := by
    have hd : Nat.card U ∣ 2 ^ 4 := by
      have hd := card_dvd_of_le (show U ≤ B from inf_le_left)
      rw [hnatural.2.1.card] at hd
      exact hd
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    interval_cases k <;> norm_num only [Nat.reducePow] at he <;> omega
  have hUne : U ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hcard
    omega
  have hf := local_escaping_plane_field h hnatural hE
    (show U ≤ B from inf_le_left) hcard (fun he => hAN (hAC.trans he))
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  exact hnon (Subgroup.isPGroup_sup_of_le_pCoreIn
    (local_field_plane_core h hnat hE hf hUne).1 hAC hpA)

omit [Finite G] in
private theorem pair_half_card {A B : Subgroup G}
    (hle : A ≤ B) (hc : Nat.card B = 16) (hi : A.relIndex B = 2) :
    Nat.card A = 8 := by
  have hh := (A.subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at hh
  change Nat.card A * A.relIndex B = Nat.card B at hh
  rw [hi, hc] at hh
  omega

private theorem pair_kernel_card_ge_two
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAN : A ≤ normalizer (layer L R : Set G)) (hc : Nat.card A = 8) :
    2 ≤ Nat.card (A ⊓ centralizer (layer L R : Set G) : Subgroup G) := by
  let C := A ⊓ centralizer (layer L R : Set G)
  have hnat : IsNaturalModule L (layer L R) n := hnatural.1 ▸ hnatural.2.1
  have hr := elementaryActionRankBound_of_natural h hnat hE A inferInstance hAN
  rw [hnatural.1] at hr
  let := h.layer_elementary
  have hi : C.relIndex A = 2 ^ ChapterE.subgroupCorank A C := by
    rw [ChapterE.subgroupCorank_eq_quotient_finrank]
    exact A.relIndex_eq_two_pow_quotient_finrank C
  have hib : C.relIndex A ≤ 4 := by
    rw [hi]
    exact Nat.pow_le_pow_right (by decide) hr
  have hh := (C.subgroupOf A).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show C ≤ A from inf_le_left)).toEquiv] at hh
  change Nat.card C * C.relIndex A = Nat.card A at hh
  rw [hc] at hh
  nlinarith

/-- Source 6.2.6: the two index-two normalizer intersections act with an
order-two kernel when the generated pair is not a two-group. -/
theorem local_pair_normalizer_kernel_card_two
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (g : G)
    (hright : ((layer L R).map (MulAut.conj g).toMonoidHom ⊓ normalizer (layer L R : Set G)).relIndex
      ((layer L R).map (MulAut.conj g).toMonoidHom) = 2)
    (hnon : ¬ IsPGroup 2 (layer L R ⊔
      (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    Nat.card ((layer L R).map (MulAut.conj g).toMonoidHom ⊓
      centralizer (layer L R : Set G) : Subgroup G) = 2 := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := A ⊓ normalizer (B : Set G)
  let := h.layer_elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ A from inf_le_left)
  have hu : Nat.card U = 8 := pair_half_card inf_le_left
    ((card_map_of_injective (MulAut.conj g).injective).trans hnatural.2.1.card) hright
  have hlo := pair_kernel_card_ge_two h hnatural hE U inf_le_right hu
  have he : U ⊓ centralizer (B : Set G) = A ⊓ centralizer (B : Set G) := by
    exact inf_assoc _ _ _ |>.trans (congrArg (fun X => A ⊓ X)
      (inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _)))
  rw [he] at hlo
  have hback : ¬ IsPGroup 2 (B ⊔ B.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) := by
    intro hp
    have hh := hp.map (MulAut.conj g).toMonoidHom
    rw [Subgroup.map_sup, show (B.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = B from by
        simpa using fusion_map_conj_inverse B g⁻¹, sup_comm] at hh
    exact hnon hh
  have hup := local_pair_intersection_centralizer_card_le_two h hnatural hE g⁻¹ hback
  have hm : Nat.card ((A ⊓ centralizer (B : Set G)).map
      (MulAut.conj g⁻¹).toMonoidHom) = Nat.card (A ⊓ centralizer (B : Set G) : Subgroup G) :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  rw [fusion_pullback_centralizer] at hm
  exact le_antisymm (hm ▸ hup) hlo

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
