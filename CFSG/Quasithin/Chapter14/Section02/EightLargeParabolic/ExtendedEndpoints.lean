module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.CubicExtension
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.Completion

/-!
# Exact intersections in the original cubic endpoint extension

The cross-normalizer clause of F.1.3 identifies P₂ intersect Mc with the whole
original Borel. Hence the actual cubic supplement is disjoint from both original
endpoints, and the three enlarged groups are split products with the same A.

A subgroup of Mc intersect M normal in both enlarged endpoints meets each base
endpoint in the same common normal subgroup. Source F.1.1 kills this intersection;
then the characteristic-two condition in Mc kills the remaining subgroup. This
establishes faithfulness of the enlarged overlap without assuming generation of G.

Source: Aschbacher--Smith 14.2.18, printed p.987; F.1.3(2), printed p.260.
The marked triality realization is retained as an independent earlier input.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH

theorem source_second_inf_partner (r : MarkedTriality T M Mc H) :
    secondParabolic T M Mc H ⊓ Mc = H ⊓ M := by
  let L := locals T M Mc H
  let B := ChapterF.Source.commonBorel L (T : Subgroup G)
  have hf := (source_hypothesis hG T hempty hM hu hmany hcard e H hH
    (firstResidualQuotientEquiv r)).1
  obtain ⟨h0,h1,hB,hinter,hPM⟩ := source_parabolics
    hG T hempty hM hu hmany hcard e H hH (firstResidualQuotientEquiv r)
  have hBH : B ≤ normalizer (H : Set G) := by
    have h := hf.commonBorel_normalizes_local 0
    change B ≤ normalizer (residual H : Set G) at h
    rwa [first_residual_eq r] at h
  have hB1 : ChapterF.Source.borel (L 1) (T : Subgroup G) =
      L 1 ⊓ normalizer (H : Set G) := by
    have h := ChapterF.Source.lemma_F_1_3_2 hf 0
    change ChapterF.Source.borel (L 1) (T : Subgroup G) =
      L 1 ⊓ normalizer (residual H : Set G) at h
    rwa [first_residual_eq r] at h
  have hprod : secondParabolic T M Mc H = L 1 ⊔ B := by
    rw [←h1]
    exact ChapterF.Source.parabolic_eq_sup_commonBorel _ _ 1
  apply le_antisymm
  · intro x hx
    have hxN : x ∈ normalizer (H : Set G) :=
      source_partner_le_first_normalizer hG hempty hM hu hmany hcard e hH r hx.2
    have hxprod : x ∈ (L 1 : Set G) * (B : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ (hf.commonBorel_normalizes_local 1), ←hprod]
      exact hx.1
    obtain ⟨a,ha,b,hb,rfl⟩ := hxprod
    have haN := (normalizer _).mul_mem_cancel_right (hBH hb) |>.mp hxN
    have haB : a ∈ B := ChapterF.Source.borel_le_commonBorel 1
      (hB1.symm ▸ (show a ∈ L 1 ⊓ normalizer (H : Set G) from ⟨ha,haN⟩))
    exact hB ▸ B.mul_mem haB hb
  · rw [←hinter]
    exact le_inf inf_le_right (inf_le_left.trans
      (source_first_le_partner hG hempty hM hu hmany hcard e hH))

theorem source_second_eq_of_partner_eq (r : MarkedTriality T M Mc H)
    (he : Mc = H) : secondParabolic T M Mc H = M := by
  have h := source_second_partner_factorization hG hempty hM hu hmany hcard e hH
  simpa only [he,secondParabolic,first_residual_eq r] using h.symm

omit [Finite G] hG hempty hM hu hmany hcard e hH in
private theorem disjoint_of_prime_supplement {X A E : Subgroup G}
    (hcardA : Nat.card A = 3) (hgen : E = X ⊔ A) (hne : E ≠ X) : Disjoint X A := by
  let : Fact (Nat.card A).Prime := ⟨by rw [hcardA]; decide⟩
  rcases (X.subgroupOf A).eq_bot_or_eq_top_of_prime_card with hb | ht
  · have hm := congrArg (Subgroup.map A.subtype) hb
    rw [subgroupOf_map_subtype,Subgroup.map_bot] at hm
    exact disjoint_iff.mpr hm
  · have hAX : A ≤ X := by
      intro a ha
      exact show (⟨a,ha⟩ : A) ∈ X.subgroupOf A from ht ▸ mem_top _
    exact (hne (hgen.trans (sup_eq_left.mpr hAX))).elim

theorem source_split_endpoint_data (r : MarkedTriality T M Mc H) (hne : Mc ≠ H) :
    ∃ A : Subgroup G,
      A ≤ M ⊓ Mc ∧ Nat.card A = 3 ∧
      A ≤ normalizer (H : Set G) ∧
      A ≤ normalizer (secondParabolic T M Mc H : Set G) ∧
      Disjoint H A ∧ Disjoint (secondParabolic T M Mc H) A ∧
      Mc = H ⊔ A ∧ M = secondParabolic T M Mc H ⊔ A ∧
      Mc ⊓ M = (H ⊓ secondParabolic T M Mc H) ⊔ A := by
  rcases source_cubic_endpoint_factorizations hG hempty hM hu hmany hcard e hH r with
    he | ⟨A,hA,hcardA,hMc,hI,hMP,hAP,hprod,hprodM⟩
  · exact (hne he).elim
  have hAH := (hA.trans inf_le_right).trans
    (source_partner_le_first_normalizer hG hempty hM hu hmany hcard e hH r)
  have hdH := disjoint_of_prime_supplement hcardA hMc hne
  have hdP : Disjoint (secondParabolic T M Mc H) A := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    have hxH : x ∈ H := ((source_second_inf_partner
      hG hempty hM hu hmany hcard e hH r).le ⟨hx.1,(hA hx.2).2⟩).1
    exact (disjoint_iff.mp hdH).le ⟨hxH,hx.2⟩
  refine ⟨A,hA,hcardA,hAH,hAP,hdH,hdP,hMc,hMP,?_⟩
  rw [inf_comm Mc M,hI, (source_parabolics hG T hempty hM hu hmany hcard e
    H hH (firstResidualQuotientEquiv r)).2.2.2.1, inf_comm H M]

theorem source_extended_common_normal_eq_bot (r : MarkedTriality T M Mc H)
    (N : Subgroup G) (hN : N ≤ Mc ⊓ M)
    (hNc : Mc ≤ normalizer (N : Set G)) (hNM : M ≤ normalizer (N : Set G)) : N = ⊥ := by
  have hHM := source_first_le_partner hG hempty hM hu hmany hcard e hH
  obtain ⟨_,_,_,hinter,hPM⟩ := source_parabolics
    hG T hempty hM hu hmany hcard e H hH (firstResidualQuotientEquiv r)
  have hinf : N ⊓ H = N ⊓ secondParabolic T M Mc H := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1,(hinter.symm ▸ (show x ∈ H ⊓ M from ⟨hx.2,(hN hx.1).2⟩)).2⟩
    · intro x hx
      exact ⟨hx.1,((source_second_inf_partner hG hempty hM hu hmany hcard e hH r).le
        ⟨hx.2,(hN hx.1).1⟩).1⟩
  have hbot : N ⊓ H = ⊥ := by
    apply (source_completion hG T hempty hM hu hmany hcard e H hH
      (firstResidualQuotientEquiv r)).2
    · exact le_inf inf_le_right (hinf ▸ (show N ⊓ secondParabolic T M Mc H ≤
        secondParabolic T M Mc H from inf_le_right))
    · exact (le_inf (hHM.trans hNc) H.le_normalizer).trans inf_normalizer_le_normalizer_inf
    · rw [hinf]
      exact (le_inf (hPM.trans hNM) (secondParabolic T M Mc H).le_normalizer).trans
        inf_normalizer_le_normalizer_inf
  have hcomm : ⁅N,H⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [←hbot]
    exact le_inf
      (le_normalizer_iff_commutator_le_left.mp (hHM.trans hNc))
      (le_normalizer_iff_commutator_le_right.mp ((hN.trans inf_le_left).trans
        (source_partner_le_first_normalizer hG hempty hM hu hmany hcard e hH r)))
  have hC := commutator_eq_bot_iff_le_centralizer.mp hcomm
  apply bot_unique
  intro n hn
  have hnq : (⟨n,(hN hn).1⟩ : Mc) ∈ pCore 2 Mc := by
    apply source_partner_characteristic_two hG hempty hM hu hmany hcard e hH
    intro q hq
    apply Subtype.ext
    apply (hC hn)
    apply pCoreIn_le 2 H
    rw [←source_partner_core_eq hG hempty hM hu hmany hcard e hH r]
    exact ⟨q,hq,rfl⟩
  have hnH : n ∈ H := by
    apply pCoreIn_le 2 H
    rw [←source_partner_core_eq hG hempty hM hu hmany hcard e hH r]
    exact ⟨⟨n,(hN hn).1⟩,hnq,rfl⟩
  exact hbot.le ⟨hn,hnH⟩

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
