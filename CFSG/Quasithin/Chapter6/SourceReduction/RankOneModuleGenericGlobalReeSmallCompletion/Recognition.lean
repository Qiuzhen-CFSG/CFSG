module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeSmallCompletion.NativeCore
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeExtension.Recognition

/-!
# Original full normalizer recognition from the marked Ree relation

Choose an actual compatible isomorphism of the original normalizer diagram,
in either orientation. Its transported inclusion completion retains the two
whole normalizers and their entire intersection. The existing full order
argument makes their join all of G. If the two specified native orbit words
satisfy the eighth-power relation there, comparison with the native extension
and original simplicity identify G with the native Ree group.

The displayed Weyl relation is still an additional premise, owned by this
small-completion development. The source extension, compatible comparison
and ambient full order bound remain the earlier-source owner's inputs.
This conditional adapter does not by itself close the prepared Ree row.
Source: Aschbacher–Smith 5.3.1–4 and F.4.10,16–17,24, pp.658–659,279,282–283,287.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion
open ChapterF.SourceCompletion.GeneralReeExtension
variable {G : Type*} [Group G]
namespace ReeSmallCompletion
variable (L K : Subgroup G) {m : ℕ} (E : SourceExtension m)

/-- An actual compatible comparison of the original whole-normalizer diagram. -/
abbrev NormalizerComparison :=
  RankTwoAmalgam.Iso
    (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (K : Set G))) E.amalgam ⊕
  RankTwoAmalgam.Iso
    (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (K : Set G))) E.amalgam.reverse

/-- Transport the two original inclusions, allowing either orientation. -/
def normalizerCompletion (e : NormalizerComparison L K E) :
    Completion E (normalizer (L : Set G) ⊔ normalizer (K : Set G) : Subgroup G) :=
  match e with
  | .inl f => (UnitaryNonbinary.Generated.completion
      (normalizer (L : Set G)) (normalizer (K : Set G))).comapIso f.symm
  | .inr f => UnitaryNonbinary.Generated.reverseCompletion
      ((UnitaryNonbinary.Generated.completion
        (normalizer (L : Set G)) (normalizer (K : Set G))).comapIso f.symm)

/-- The transported completion has exactly the original whole overlap. -/
theorem normalizerCompletion_overlap (e : NormalizerComparison L K E) :
    (normalizerCompletion L K E e).left.range ⊓ (normalizerCompletion L K E e).right.range =
      (normalizerCompletion L K E e).middle.range := by
  cases e with
  | inl f =>
    simpa only [normalizerCompletion,RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using
      UnitaryNonbinary.Generated.whole_overlap (normalizer (L : Set G)) (normalizer (K : Set G))
  | inr f =>
    apply UnitaryNonbinary.Generated.reverseCompletion_overlap
    simpa only [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using
      UnitaryNonbinary.Generated.whole_overlap (normalizer (L : Set G)) (normalizer (K : Set G))

/-- The marked endpoint images are the actual full normalizers in their join. -/
theorem normalizerCompletion_ranges (e : NormalizerComparison L K E) :
    let X := normalizer (L : Set G) ⊔ normalizer (K : Set G)
    let c := normalizerCompletion L K E e
    (c.left.range = (normalizer (L : Set G)).subgroupOf X ∧
      c.right.range = (normalizer (K : Set G)).subgroupOf X) ∨
    (c.left.range = (normalizer (K : Set G)).subgroupOf X ∧
      c.right.range = (normalizer (L : Set G)).subgroupOf X) := by
  cases e with
  | inl f =>
    left
    simp only [normalizerCompletion,RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,UnitaryNonbinary.Generated.completion,
      RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_left_range,
      RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_right_range,and_self]
  | inr f =>
    right
    change (UnitaryNonbinary.Generated.completion _ _ |>.comapIso f.symm).right.range = _ ∧
      (UnitaryNonbinary.Generated.completion _ _ |>.comapIso f.symm).left.range = _
    simp only [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,UnitaryNonbinary.Generated.completion,
      RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_left_range,
      RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_right_range,and_self]

/-- The common image is the full intersection, not a Sylow or residual substitute. -/
theorem normalizerCompletion_middle (e : NormalizerComparison L K E) :
    (normalizerCompletion L K E e).middle.range =
      (normalizer (L : Set G) ⊓ normalizer (K : Set G)).subgroupOf
        (normalizer (L : Set G) ⊔ normalizer (K : Set G)) := by
  rw [←normalizerCompletion_overlap L K E e]
  rcases normalizerCompletion_ranges L K E e with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · rw [hl,hr]
    rfl
  · rw [hl,hr,inf_comm]
    rfl

end ReeSmallCompletion
variable [Finite G]

/-- Literal original-normalizer recognition with just the marked Weyl relation
remaining in addition to the retained earlier-source extension inputs. -/
theorem Preparation.ree_full_normalizers_recognition_of_weyl_relation
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
    (E : SourceExtension m) (e : ReeSmallCompletion.NormalizerComparison L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier)
    (hweyl : weylProduct E (ReeSmallCompletion.normalizerCompletion L (residual H) E e)^8 = 1) :
    2*m+1 = n ∧ 0 < m ∧
      normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
      Nat.card G = Nat.card E.carrier ∧ Nonempty (G ≃* ReeF4.Model m) := by
  let : IsSimpleGroup G := h.qtke.simple
  have hext : Nonempty (RankTwoAmalgam.Iso
      (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (residual H : Set G))) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (residual H : Set G))) E.amalgam.reverse) := by
    cases e with
    | inl f => exact .inl ⟨f⟩
    | inr f => exact .inr ⟨f⟩
  obtain ⟨hn,hm,htop,hcard,_⟩ := d.ree_full_normalizers_small_completion h hH hp m he E hext horder
  let X := normalizer (L : Set G) ⊔ normalizer (residual H : Set G)
  let a : X ≃* G := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  let c := ReeSmallCompletion.normalizerCompletion L (residual H) E e
  have hc := ReeSmallCompletion.normalizerCompletion_overlap L (residual H) E e
  have hw : weylProduct E (c.mapEquiv a)^8 = 1 := by
    change (a (c.left (leftReflection E)) * a (c.right (rightReflection E)))^8 = 1
    rw [←map_mul,←map_pow]
    exact (congrArg a hweyl).trans (map_one a)
  exact ⟨hn,hm,htop,hcard,nonempty_native_mulEquiv_of_simple_of_weyl_relation E
    (c.mapEquiv a) hm (c.mapEquiv_overlap a hc) hw⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
