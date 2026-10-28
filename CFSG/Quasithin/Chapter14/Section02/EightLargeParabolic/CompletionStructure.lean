module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.ExtendedAmalgam

/-!
# The perfect base and full normalizer of the original triality completion

Write B = H join P₂ and J = Mc join M. The original characteristic-two
centralizer has C_G(H) = Z(T), so source F.1.1 gives C_G(B) = 1. Frattini's
argument, with the actual ambient Sylow and N_G(T) placement, proves N_G(B) = J.

The first endpoint is perfect and contains T. The source identity Y = [Y,S₂]
therefore makes B perfect. The common cubic supplement then gives [J,J] = B
and |J:B| dividing three. Characteristicity of the derived subgroup yields
N_G(J) = J. Simplicity proves B = G if and only if J = G; neither equality is
assumed. All normality before that last implication is relative to J.

These are completion-structure consequences used in the specialized
14.2.18--19 recognition. They do not recognize the arbitrary completion as the
standard finite triality group or prove generation of G. Those obligations
remain with qt-e-14315-eight-borel-exclusion, and the earlier marked realization
remains explicit, owned by qt-e-1427-eight-amalgam-recognition.

Source: Aschbacher--Smith 14.2.18--19, p.987; F.4.3 and F.4.31, pp.274,290--291.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
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

theorem source_first_centralizer (r : MarkedTriality T M Mc H) :
    centralizer (H : Set G) = centralInvolutions T := by
  have hCH : centralizer (H : Set G) ≤ Mc := by
    rw [←source_first_normalizer_eq hG hempty hM hu hmany hcard e hH r]
    exact Subgroup.centralizer_le_normalizer _
  apply le_antisymm
  · intro x hx
    have hxQ : (⟨x,hCH hx⟩ : Mc) ∈ pCore 2 Mc := by
      apply source_partner_characteristic_two hG hempty hM hu hmany hcard e hH
      intro q hq
      apply Subtype.ext
      apply hx
      apply pCoreIn_le 2 H
      rw [←source_partner_core_eq hG hempty hM hu hmany hcard e hH r]
      exact ⟨q,hq,rfl⟩
    have hxQH : x ∈ H.pCoreIn 2 := by
      rw [←source_partner_core_eq hG hempty hM hu hmany hcard e hH r]
      exact ⟨⟨x,hCH hx⟩,hxQ,rfl⟩
    rw [←source_firstCore_center hG hempty hM hu hmany hcard e hH r]
    exact ⟨⟨x,hxQH⟩,mem_center_iff.mpr (fun q =>
      Subtype.ext (hx q (pCoreIn_le 2 H q.property))),rfl⟩
  · exact le_centralizer_iff.mp ((source_lemma_14_2_3
      hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2)

theorem source_generated_centralizer_eq_bot (r : MarkedTriality T M Mc H) :
    centralizer ((H ⊔ secondParabolic T M Mc H : Subgroup G) : Set G) = ⊥ := by
  let B := H ⊔ secondParabolic T M Mc H
  let C := centralizer (B : Set G)
  have hCZ : C ≤ centralInvolutions T :=
    (centralizer_le (show (H : Set G) ⊆ B from fun _ hx => mem_sup_left hx)).trans_eq
      (source_first_centralizer hG hempty hM hu hmany hcard e hH r)
  have hCP : C ≤ H ⊓ secondParabolic T M Mc H :=
    hCZ.trans ((centralInvolutions_le_sylow T).trans (le_inf hH.1.1.2
      (show (T : Subgroup G) ≤ secondParabolic T M Mc H from
        le_sup_right.trans le_sup_left)))
  have hNC : B ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp (show C ≤ centralizer (B : Set G) from le_rfl)).trans
      (Subgroup.centralizer_le_normalizer _)
  exact (source_completion hG T hempty hM hu hmany hcard e H hH
    (firstResidualQuotientEquiv r)).2 C hCP
      (le_sup_left.trans hNC) (le_sup_right.trans hNC)

theorem source_generated_normalizer_eq (r : MarkedTriality T M Mc H) :
    normalizer ((H ⊔ secondParabolic T M Mc H : Subgroup G) : Set G) = Mc ⊔ M := by
  let B := H ⊔ secondParabolic T M Mc H
  let J := Mc ⊔ M
  let N := normalizer (B : Set G)
  have hBJ : B ≤ J := sup_le_sup
    (source_first_le_partner hG hempty hM hu hmany hcard e hH)
    (source_parabolics hG T hempty hM hu hmany hcard e H hH
      (firstResidualQuotientEquiv r)).2.2.2.2
  have hTB : (T : Subgroup G) ≤ B := fun _ hx => mem_sup_left (hH.1.1.2 hx)
  have hTN : (T : Subgroup G) ≤ N := hTB.trans B.le_normalizer
  let S := T.subtype hTN
  have hSN : (S : Subgroup N) ≤ B.subgroupOf N := comap_mono hTB
  have hfr := S.normalizer_sup_eq_top' hSN
  apply le_antisymm
  · have hNS : normalizer (S : Set N) ≤ J.subgroupOf N := by
      intro x hx
      have hxT : (x : G) ∈ normalizer (T : Set G) := by
        change x ∈ normalizer ((T : Subgroup G).subgroupOf N : Set N) at hx
        rw [←subgroupOf_normalizer_eq hTN] at hx
        exact hx
      have hxI := source_lemma_14_2_2_7 hG T hempty hM hu hmany hcard e hxT
      exact mem_sup_left hxI.2
    have ht : (⊤ : Subgroup N) ≤ J.subgroupOf N := by
      rw [←hfr]
      exact sup_le hNS (comap_mono hBJ)
    intro x hx
    exact ht (show (⟨x,hx⟩ : N) ∈ (⊤ : Subgroup N) from mem_top _)
  · exact (normal_subgroupOf_iff_le_normalizer hBJ).mp
      (source_generated_base_normal hG hempty hM hu hmany hcard e hH r)


theorem source_generated_perfect (r : MarkedTriality T M Mc H) :
    Group.IsPerfect (H ⊔ secondParabolic T M Mc H : Subgroup G) := by
  let B := H ⊔ secondParabolic T M Mc H
  let Y := sourceResidual M Mc
  have hTB : (T : Subgroup G) ≤ B := fun _ ht => mem_sup_left (hH.1.1.2 ht)
  have hYB : Y ≤ B :=
    (show Y ≤ secondParabolic T M Mc H from le_sup_left.trans le_sup_left).trans le_sup_right
  have hgen : B = H ⊔ Y := by
    apply le_antisymm
    · apply sup_le le_sup_left
      exact sup_le (sup_le le_sup_right (fun _ ht => mem_sup_left (hH.1.1.2 ht)))
        (inf_le_right.trans ((map_subtype_le _).trans le_sup_left))
    · exact sup_le le_sup_left hYB
  let := first_perfect r
  have hHB : H ≤ ⁅B,B⁆ := by
    rw [←commutator_eq_self (H := H)]
    exact commutator_mono le_sup_left le_sup_left
  obtain ⟨_,hS,hmotion,_,_⟩ := source_hypothesis
    hG T hempty hM hu hmany hcard e H hH (firstResidualQuotientEquiv r)
  have hY : Y ≤ ⁅B,B⁆ := by
    change sourceResidual M Mc ≤ _
    rw [hmotion]
    exact commutator_mono hYB (hS.trans hTB)
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm
  · exact (Subgroup.commutator_le_sup B B).trans (sup_idem B).le
  · exact hgen.le.trans (sup_le hHB hY)

theorem source_generated_derived_and_index (r : MarkedTriality T M Mc H) :
    ⁅Mc ⊔ M, Mc ⊔ M⁆ = H ⊔ secondParabolic T M Mc H ∧
      (H ⊔ secondParabolic T M Mc H).relIndex (Mc ⊔ M) ∣ 3 := by
  let B := H ⊔ secondParabolic T M Mc H
  let J := Mc ⊔ M
  let : Group.IsPerfect B := source_generated_perfect hG hempty hM hu hmany hcard e hH r
  by_cases he : Mc = H
  · have hP := source_second_eq_of_partner_eq hG hempty hM hu hmany hcard e hH r he
    have hJB : Mc ⊔ M = B := by rw [he,←hP]
    rw [hJB,commutator_eq_self (H := B),relIndex_self]
    exact ⟨rfl,one_dvd _⟩
  · obtain ⟨A,hA,hcardA,hAH,hAP,hdH,hdP,hMc,hMP,hI⟩ :=
      source_split_endpoint_data hG hempty hM hu hmany hcard e hH r he
    have hBJ : B ≤ J := sup_le_sup
      (source_first_le_partner hG hempty hM hu hmany hcard e hH)
      (source_parabolics hG T hempty hM hu hmany hcard e H hH
        (firstResidualQuotientEquiv r)).2.2.2.2
    have hAJ : A ≤ J := (hA.trans inf_le_right).trans le_sup_left
    have hgen : B ⊔ A = J := by
      change (H ⊔ secondParabolic T M Mc H) ⊔ A = Mc ⊔ M
      calc
        (H ⊔ secondParabolic T M Mc H) ⊔ A =
            (H ⊔ A) ⊔ (secondParabolic T M Mc H ⊔ A) := by ac_rfl
        _ = Mc ⊔ M := (congrArg₂ (· ⊔ ·) hMc hMP).symm
    let N := B.subgroupOf J
    let A' := A.subgroupOf J
    let : N.Normal := source_generated_base_normal hG hempty hM hu hmany hcard e hH r
    have hgen' : N ⊔ A' = ⊤ := by
      rw [←subgroupOf_sup hBJ hAJ,hgen,subgroupOf_self]
    have hcardA' : Nat.card A' = 3 :=
      (Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv).trans hcardA
    let : IsCyclic A' := isCyclic_of_prime_card hcardA'
    have hupper := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      hgen' (inferInstance : IsMulCommutative A')
    have hupper' := map_mono (f := J.subtype) hupper
    rw [map_subtype_commutator,map_subgroupOf_eq_of_le hBJ] at hupper'
    refine ⟨le_antisymm hupper' ?_, ?_⟩
    · exact (commutator_eq_self (H := B)).symm.le.trans (commutator_mono hBJ hBJ)
    · change N.index ∣ 3
      have hi := relIndex_sup_left A' N
      rw [hgen',relIndex_top_right] at hi
      rw [hi,←hcardA']
      exact N.relIndex_dvd_card A'

theorem source_extended_self_normalizing (r : MarkedTriality T M Mc H) :
    normalizer ((Mc ⊔ M : Subgroup G) : Set G) = Mc ⊔ M := by
  let J := Mc ⊔ M
  have hderived : (commutator J).map J.subtype = H ⊔ secondParabolic T M Mc H :=
    (map_subtype_commutator J).trans
      (source_generated_derived_and_index hG hempty hM hu hmany hcard e hH r).1
  have hbound := normalizer_le_normalizer_characteristic_image J (commutator J)
  rw [hderived,source_generated_normalizer_eq hG hempty hM hu hmany hcard e hH r] at hbound
  exact le_antisymm hbound J.le_normalizer

theorem source_generated_eq_top_iff (r : MarkedTriality T M Mc H) :
    H ⊔ secondParabolic T M Mc H = ⊤ ↔ Mc ⊔ M = ⊤ := by
  let B := H ⊔ secondParabolic T M Mc H
  let J := Mc ⊔ M
  have hBJ : B ≤ J := sup_le_sup
    (source_first_le_partner hG hempty hM hu hmany hcard e hH)
    (source_parabolics hG T hempty hM hu hmany hcard e H hH
      (firstResidualQuotientEquiv r)).2.2.2.2
  constructor
  · intro ht
    exact top_unique (ht ▸ hBJ)
  · intro ht
    let : IsSimpleGroup G := hG.simple
    have hn : B.Normal := normalizer_eq_top_iff.mp
      ((source_generated_normalizer_eq hG hempty hM hu hmany hcard e hH r).trans ht)
    rcases hn.eq_bot_or_eq_top with hb | hb
    · have hc := source_generated_centralizer_eq_bot hG hempty hM hu hmany hcard e hH r
      change centralizer (B : Set G) = ⊥ at hc
      rw [hb] at hc
      have ht : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
        centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup G) ≤ center G from bot_le)
      exact (top_ne_bot (ht.symm.trans hc)).elim
    · exact hb


end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
