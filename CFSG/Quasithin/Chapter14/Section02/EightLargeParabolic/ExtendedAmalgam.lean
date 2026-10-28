module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.ExtendedEndpoints
public import Theory.GroupTheory.Amalgam.SplitExtension

/-!
# The actual enlarged triality amalgam and its faithful completion

Construct the inclusion amalgam (Mc, Mc intersect M, M), completed in Mc join M.
Its overlap has trivial normal core. If Mc = H it is the original marked triality
amalgam. Otherwise the exact source intersections identify all three groups,
compatibly, with semidirect products of the marked triality amalgam by the same
order-three subgroup A. Conjugation on both endpoints is retained pointwise.
The restriction of the genuine coefficient-field action to A is bijective, and
the transported amalgam action is faithful. The original generated subgroup
H join P₂ is normal in the enlarged generated subgroup Mc join M.

This supplies a split presentation of the actual extension in 14.2.18, not yet
its identification with the prescribed Aut(³D₄(2)) amalgam of Definition F.4.3.
Extending this compatible cubic action to the standard finite completion,
recognizing the arbitrary ambient group in 14.2.19, and final Borel exclusion
remain with qt-e-14315-eight-borel-exclusion. The independent marked realization
from qt-e-1427-eight-amalgam-recognition is still explicit.

Source: Aschbacher--Smith 14.2.18--19, printed p.987; F.4.3 and F.4.31,
printed pp.274 and 290--291. No assertion Mc join M = G is made here.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
variable {G : Type*} [Group G]

def extendedAmalgam (Mc M : Subgroup G) :=
  RankTwoAmalgam.ofSubgroups Mc (Mc ⊓ M) M inf_le_left inf_le_right

private theorem inclusion_range {A B : Subgroup G} (h : A ≤ B) :
    (inclusion h).range = A.subgroupOf B := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩; exact a.property
  · intro hx; exact ⟨⟨x,hx⟩,rfl⟩

def extendedCompletion (Mc M : Subgroup G) :
    RankTwoAmalgam.FaithfulCompletion (extendedAmalgam Mc M)
      (G := (Mc ⊔ M : Subgroup G)) where
  left := inclusion le_sup_left
  right := inclusion le_sup_right
  compatible := by ext x; rfl
  left_injective := inclusion_injective _
  right_injective := inclusion_injective _
  middle_injective := by
    intro x y he
    exact Subtype.ext (congrArg (Mc ⊔ M).subtype he)
  generated := by
    rw [inclusion_range,inclusion_range,←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]

theorem extendedCompletion_images (Mc M : Subgroup G) :
    (extendedCompletion Mc M).left.range.map (Mc ⊔ M).subtype = Mc ∧
      (extendedCompletion Mc M).right.range.map (Mc ⊔ M).subtype = M ∧
      (extendedCompletion Mc M).middle.range.map (Mc ⊔ M).subtype = Mc ⊓ M := by
  refine ⟨?_,?_,?_⟩
  · change (inclusion (show Mc ≤ Mc ⊔ M from le_sup_left)).range.map _ = Mc
    rw [inclusion_range,map_subgroupOf_eq_of_le le_sup_left]
  · change (inclusion (show M ≤ Mc ⊔ M from le_sup_right)).range.map _ = M
    rw [inclusion_range,map_subgroupOf_eq_of_le le_sup_right]
  · change (inclusion (show Mc ⊓ M ≤ Mc ⊔ M from inf_le_left.trans le_sup_left)).range.map _ = _
    rw [inclusion_range,map_subgroupOf_eq_of_le (inf_le_left.trans le_sup_left)]

theorem extendedCompletion_overlap (Mc M : Subgroup G) :
    (extendedCompletion Mc M).left.range ⊓ (extendedCompletion Mc M).right.range =
      (extendedCompletion Mc M).middle.range := by
  apply map_injective (Mc ⊔ M).subtype_injective
  rw [map_inf _ _ _ (Mc ⊔ M).subtype_injective,
    (extendedCompletion_images Mc M).1,(extendedCompletion_images Mc M).2.1,
    (extendedCompletion_images Mc M).2.2]

variable {T : Sylow 2 G} {M Mc H : Subgroup G}

def markedCubicAction (r : MarkedTriality T M Mc H) (A : Subgroup G)
    (hAH : A ≤ normalizer (H : Set G))
    (hAP : A ≤ normalizer (secondParabolic T M Mc H : Set G)) :=
  (RankTwoAmalgam.automorphismConjEquiv r).toMonoidHom.comp
    (RankTwoAmalgam.conjugationAction H (secondParabolic T M Mc H) A hAH hAP)

theorem markedCubicAction_left (r : MarkedTriality T M Mc H) (A : Subgroup G)
    (hAH : A ≤ normalizer (H : Set G))
    (hAP : A ≤ normalizer (secondParabolic T M Mc H : Set G)) (a : A) (x : H) :
    (markedCubicAction r A hAH hAP a).left (r.left x) =
      r.left (H.normalizerMonoidHom (inclusion hAH a) x) := by
  change r.left (H.normalizerMonoidHom (inclusion hAH a) (r.left.symm (r.left x))) = _
  rw [r.left.symm_apply_apply]

theorem markedCubicAction_right (r : MarkedTriality T M Mc H) (A : Subgroup G)
    (hAH : A ≤ normalizer (H : Set G))
    (hAP : A ≤ normalizer (secondParabolic T M Mc H : Set G))
    (a : A) (x : secondParabolic T M Mc H) :
    (markedCubicAction r A hAH hAP a).right (r.right x) =
      r.right ((secondParabolic T M Mc H).normalizerMonoidHom (inclusion hAP a) x) := by
  change r.right ((secondParabolic T M Mc H).normalizerMonoidHom (inclusion hAP a)
    (r.right.symm (r.right x))) = _
  rw [r.right.symm_apply_apply]

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable [Finite G]
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

theorem source_extendedCompletion_corefree (r : MarkedTriality T M Mc H) :
    (extendedCompletion Mc M).middle.range.normalCore = ⊥ := by
  let J := Mc ⊔ M
  let N := (extendedCompletion Mc M).middle.range.normalCore
  have hnJ : J ≤ normalizer (N.map J.subtype : Set G) := by
    have hn := N.le_normalizer_map J.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hn
  have hNm : N.map J.subtype ≤ Mc ⊓ M :=
    (map_mono (f := J.subtype) (extendedCompletion Mc M).middle.range.normalCore_le).trans_eq
      (extendedCompletion_images Mc M).2.2
  have hb := source_extended_common_normal_eq_bot hG hempty hM hu hmany hcard e hH r
    (N.map J.subtype) hNm (le_sup_left.trans hnJ) (le_sup_right.trans hnJ)
  exact (map_eq_bot_iff_of_injective N J.subtype_injective).mp hb

theorem source_cubic_field_restriction (r : MarkedTriality T M Mc H)
    (A : Subgroup G) (hAc : A ≤ Mc) (hcardA : Nat.card A = 3) (hd : Disjoint H A) :
    Function.Bijective ((sourceFieldAction hG hempty hM hu hmany hcard e hH r).comp
      (inclusion hAc)) := by
  let : Finite (Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) :=
    Nat.finite_of_card_ne_zero (by rw [GaloisField.card_ringAut 2 3 (by decide)]; decide)
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    have haH : (a : G) ∈ H := by
      have hk : inclusion hAc a ∈
          (sourceFieldAction hG hempty hM hu hmany hcard e hH r).ker := ha
      rw [source_fieldAction_kernel_eq_first] at hk
      exact hk
    exact mem_bot.mpr (Subtype.ext (disjoint_iff.mp hd |>.le ⟨haH,a.property⟩))
  · rw [hcardA,GaloisField.card_ringAut 2 3 (by decide)]

theorem source_markedCubicAction_injective (r : MarkedTriality T M Mc H)
    (A : Subgroup G) (hAc : A ≤ Mc) (hcardA : Nat.card A = 3) (hd : Disjoint H A)
    (hAH : A ≤ normalizer (H : Set G))
    (hAP : A ≤ normalizer (secondParabolic T M Mc H : Set G)) :
    Function.Injective (markedCubicAction r A hAH hAP) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hfix (x : H) : H.normalizerMonoidHom (inclusion hAH a) x = x := by
    apply r.left.injective
    rw [←markedCubicAction_left r A hAH hAP a x]
    rw [show markedCubicAction r A hAH hAP a = 1 from ha,RankTwoAmalgam.Iso.one_left]
    rfl
  have hrank : sourceRankOneAction hG hempty hM hu hmany hcard e hH r (inclusion hAc a) = 1 := by
    ext u
    obtain ⟨v,rfl⟩ := (firstQuotientEquiv r).surjective u
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) v
    rw [source_rankOneAction_mk]
    change (firstQuotientEquiv r) (QuotientGroup.mk' (pCore 2 H)
      (H.normalizerMonoidHom (inclusion hAH a) x)) = _
    rw [hfix]
    rfl
  have hf : sourceFieldAction hG hempty hM hu hmany hcard e hH r (inclusion hAc a) = 1 := by
    change Theory.PSL2.fieldProjection _
      (sourceRankOneAction hG hempty hM hu hmany hcard e hH r (inclusion hAc a)) = 1
    rw [hrank,map_one]
  apply mem_bot.mpr
  apply (source_cubic_field_restriction hG hempty hM hu hmany hcard e hH r A hAc hcardA hd).1
  exact hf.trans (map_one _).symm

theorem source_extendedAmalgam_split (r : MarkedTriality T M Mc H) (hne : Mc ≠ H) :
    ∃ (A : Subgroup G) (hAH : A ≤ normalizer (H : Set G))
      (hAP : A ≤ normalizer (secondParabolic T M Mc H : Set G)),
      A ≤ M ⊓ Mc ∧ Nat.card A = 3 ∧
      Disjoint H A ∧ Disjoint (secondParabolic T M Mc H) A ∧
      Mc = H ⊔ A ∧ M = secondParabolic T M Mc H ⊔ A ∧
      Nonempty (RankTwoAmalgam.Iso (extendedAmalgam Mc M)
        (RankTwoAmalgam.semidirect (markedCubicAction r A hAH hAP))) := by
  obtain ⟨A,hA,hcardA,hAH,hAP,hdH,hdP,hMc,hMP,hI⟩ :=
    source_split_endpoint_data hG hempty hM hu hmany hcard e hH r hne
  let j : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (H ⊔ A) ((H ⊓ secondParabolic T M Mc H) ⊔ A)
        (secondParabolic T M Mc H ⊔ A)
          (sup_le_sup_right inf_le_left A) (sup_le_sup_right inf_le_right A))
      (extendedAmalgam Mc M) :=
    { left := MulEquiv.subgroupCongr hMc.symm
      middle := MulEquiv.subgroupCongr hI.symm
      right := MulEquiv.subgroupCongr hMP.symm
      left_commutes _ := rfl
      right_commutes _ := rfl }
  exact ⟨A,hAH,hAP,hA,hcardA,hdH,hdP,hMc,hMP,
    ⟨j.symm.trans ((RankTwoAmalgam.splitIso H (secondParabolic T M Mc H) A
      hAH hAP hdH hdP).symm.trans (RankTwoAmalgam.semidirectIso r _))⟩⟩

theorem source_extendedAmalgam_plain (r : MarkedTriality T M Mc H) (he : Mc = H) :
    Nonempty (RankTwoAmalgam.Iso (extendedAmalgam Mc M)
      (ChapterF.GreenBook.LieModels.Triality.amalgam
        (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one))) := by
  have hP := source_second_eq_of_partner_eq hG hempty hM hu hmany hcard e hH r he
  let j : RankTwoAmalgam.Iso (extendedAmalgam Mc M) (amalgam T M Mc H) :=
    { left := MulEquiv.subgroupCongr he
      middle := MulEquiv.subgroupCongr (by rw [hP,he])
      right := MulEquiv.subgroupCongr hP.symm
      left_commutes _ := rfl
      right_commutes _ := rfl }
  exact ⟨j.trans r⟩

theorem source_generated_base_normal (r : MarkedTriality T M Mc H) :
    ((H ⊔ secondParabolic T M Mc H).subgroupOf (Mc ⊔ M)).Normal := by
  by_cases he : Mc = H
  · have hP := source_second_eq_of_partner_eq hG hempty hM hu hmany hcard e hH r he
    rw [hP,he,subgroupOf_self]
    infer_instance
  · obtain ⟨A,hA,hcardA,hAH,hAP,hdH,hdP,hMc,hMP,hI⟩ :=
      source_split_endpoint_data hG hempty hM hu hmany hcard e hH r he
    have hnA := (le_inf hAH hAP).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    apply normal_subgroupOf_of_le_normalizer
    calc
      Mc ⊔ M = (H ⊔ A) ⊔ (secondParabolic T M Mc H ⊔ A) := congrArg₂ (· ⊔ ·) hMc hMP
      _ ≤ normalizer ((H ⊔ secondParabolic T M Mc H : Subgroup G) : Set G) :=
        sup_le (sup_le (le_sup_left.trans (H ⊔ secondParabolic T M Mc H).le_normalizer) hnA)
          (sup_le (le_sup_right.trans (H ⊔ secondParabolic T M Mc H).le_normalizer) hnA)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
