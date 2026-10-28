module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.LocalCore
public import Theory.GroupTheory.Amalgam.RankTwoCompletion

/-!
# The original marked triality completion

The inclusion maps construct a faithful completion in H join P₂. Changing the
marking with both commuting squares gives a completion of the genuine triality
amalgam, whose endpoint images are H and P₂ and whose whole middle is their
intersection. The original F.1.1 common-normal argument proves that the normal
core of this middle is trivial inside the generated subgroup.

This is the source completion needed for Aschbacher--Smith 14.2.18--19 and F.4.31
(printed pp.987,290--291). It asserts neither H join P₂ = G nor recognition of
this completion. The cubic-extension case must use the enlarged endpoints.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
variable {G : Type*} [Group G] {T : Sylow 2 G} {M Mc H : Subgroup G}

private theorem inclusion_range {A B : Subgroup G} (h : A ≤ B) :
    (inclusion h).range = A.subgroupOf B := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hx
    exact ⟨⟨x,hx⟩,rfl⟩

/-- The inclusion amalgam completes in the subgroup it actually generates.
No generation of the whole ambient G is presumed. -/
def inclusionCompletion (T : Sylow 2 G) (M Mc H : Subgroup G) :
    RankTwoAmalgam.FaithfulCompletion (amalgam T M Mc H)
      (G := (H ⊔ secondParabolic T M Mc H : Subgroup G)) where
  left := inclusion le_sup_left
  right := inclusion le_sup_right
  compatible := by ext x; rfl
  left_injective := inclusion_injective _
  right_injective := inclusion_injective _
  middle_injective := by
    intro x y hxy
    have hv := congrArg (H ⊔ secondParabolic T M Mc H).subtype hxy
    exact Subtype.ext hv
  generated := by
    rw [inclusion_range, inclusion_range, ← subgroupOf_sup le_sup_left le_sup_right,
      subgroupOf_self]

/-- The genuine triality amalgam has this specific faithful completion under
the explicit earlier marking. This is a completion, not its recognition. -/
def markedCompletion (r : MarkedTriality T M Mc H) :
    RankTwoAmalgam.FaithfulCompletion
      (ChapterF.GreenBook.LieModels.Triality.amalgam
        (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one))
      (G := (H ⊔ secondParabolic T M Mc H : Subgroup G)) :=
  (inclusionCompletion T M Mc H).comapIso r.symm

/-- Both endpoint images in the original G are the specified source parabolics. -/
theorem markedCompletion_endpoint_images (r : MarkedTriality T M Mc H) :
    (markedCompletion r).left.range.map (H ⊔ secondParabolic T M Mc H).subtype = H ∧
      (markedCompletion r).right.range.map (H ⊔ secondParabolic T M Mc H).subtype =
        secondParabolic T M Mc H := by
  constructor
  · rw [markedCompletion, RankTwoAmalgam.FaithfulCompletion.comapIso_left_range]
    change (inclusion (show H ≤ H ⊔ secondParabolic T M Mc H from le_sup_left)).range.map _ = H
    rw [inclusion_range, map_subgroupOf_eq_of_le le_sup_left]
  · rw [markedCompletion, RankTwoAmalgam.FaithfulCompletion.comapIso_right_range]
    change (inclusion (show secondParabolic T M Mc H ≤ H ⊔ secondParabolic T M Mc H
      from le_sup_right)).range.map _ = _
    rw [inclusion_range, map_subgroupOf_eq_of_le le_sup_right]

/-- The middle image is the full original intersection; the odd Borel factor
has not been replaced by a two-subgroup. -/
theorem markedCompletion_middle_image (r : MarkedTriality T M Mc H) :
    (markedCompletion r).middle.range.map (H ⊔ secondParabolic T M Mc H).subtype =
      H ⊓ secondParabolic T M Mc H := by
  rw [markedCompletion, RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range]
  change (inclusion (show H ⊓ secondParabolic T M Mc H ≤
    H ⊔ secondParabolic T M Mc H from inf_le_left.trans le_sup_left)).range.map _ = _
  rw [inclusion_range, map_subgroupOf_eq_of_le (inf_le_left.trans le_sup_left)]

/-- The completion has the whole marked overlap, as required by coset geometry. -/
theorem markedCompletion_overlap (r : MarkedTriality T M Mc H) :
    (markedCompletion r).left.range ⊓ (markedCompletion r).right.range =
      (markedCompletion r).middle.range := by
  apply map_injective (H ⊔ secondParabolic T M Mc H).subtype_injective
  rw [map_inf _ _ _ (H ⊔ secondParabolic T M Mc H).subtype_injective,
    (markedCompletion_endpoint_images r).1, (markedCompletion_endpoint_images r).2,
    markedCompletion_middle_image]

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- The action on cosets of the whole marked middle is faithful in the generated
completion. Normality is used inside that completion, not inside G. -/
theorem source_markedCompletion_corefree [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
    (r : MarkedTriality T M Mc H) : (markedCompletion r).middle.range.normalCore = ⊥ := by
  let J := H ⊔ secondParabolic T M Mc H
  let N := (markedCompletion r).middle.range.normalCore
  have hNm : N.map J.subtype ≤ H ⊓ secondParabolic T M Mc H :=
    (map_mono (f := J.subtype) (markedCompletion r).middle.range.normalCore_le).trans_eq
      (markedCompletion_middle_image r)
  have hnJ : J ≤ normalizer (N.map J.subtype : Set G) := by
    have hn := N.le_normalizer_map J.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn
  have he := (source_completion hG T hempty hM hu hmany hcard e H hH eR).2
    (N.map J.subtype) hNm (le_sup_left.trans hnJ) (le_sup_right.trans hnJ)
  exact (map_eq_bot_iff_of_injective N J.subtype_injective).mp he

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
