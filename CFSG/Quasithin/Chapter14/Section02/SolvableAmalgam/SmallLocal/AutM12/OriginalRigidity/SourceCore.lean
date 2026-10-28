module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.Orientation
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity.Marking

/-!
# The actual core reduction inside the containing centralizer

The recognized pair is reindexed only at its first vertex, through the
inclusion of H into Mc. Every wreath preimage has the same ambient image
under this reindexing. The original Sylow marking then identifies its central
kernel in Mc, so the corrected core trichotomy applies to the actual groups:
either H equals Mc or the marked quaternion base is normal in Mc.

This supplies the literal normality and central marking used by the
independent-cubic overgroup calculation in the original Aut(M12) row.
Source: Aschbacher--Smith, Lemma 14.2.21, printed pp.988--989.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity
open SourceModel.Transport SourcePreliminaries Chapter15.Section03
variable {G B R : Type*} [Group G] [Finite G] [Group B] [Group R]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}

/-- Reindex only the left vertex through its actual embedding into Mc. -/
def insidePair (c : CubicSourceContext T M Mc H) (α : RankTwoAmalgam H B R) :
    RankTwoAmalgam (H.subgroupOf Mc) B R where
  left := (subgroupOfEquivOfLe c.H_le_Mc).symm.toMonoidHom.comp α.left
  right := α.right

def insideIso (c : CubicSourceContext T M Mc H) (α : RankTwoAmalgam H B R) :
    RankTwoAmalgam.Iso (insidePair c α) α where
  left := subgroupOfEquivOfLe c.H_le_Mc
  middle := MulEquiv.refl _
  right := MulEquiv.refl _
  left_commutes x := by simp only [insidePair,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply,MulEquiv.refl_apply]
  right_commutes _ := rfl

variable (c : CubicSourceContext T M Mc H) {α : RankTwoAmalgam H B R}
  (r : RankTwoAmalgam.Iso α ChapterF.GreenBook.AutMathieuTwelve.autAmalgam)

def insideRecognition : RankTwoAmalgam.Iso (insidePair c α)
    ChapterF.GreenBook.AutMathieuTwelve.autAmalgam := (insideIso c α).trans r

omit [Finite G] in
private theorem wreath_inside (x : pCore 2 (H.subgroupOf Mc)) :
    wreathMap (insideRecognition c r) x =
      wreathMap r (LocalCoreTransport.coreEquiv 2 (subgroupOfEquivOfLe c.H_le_Mc) x) := by
  apply congrArg SourceModel.coreWreathMap
  apply Subtype.ext
  change (coreEquiv (insideRecognition c r) x).val =
    (coreEquiv r (LocalCoreTransport.coreEquiv 2 (subgroupOfEquivOfLe c.H_le_Mc) x)).val
  rw [coreEquiv_val,coreEquiv_val,LocalCoreTransport.coreEquiv_apply]
  rfl

omit [Finite G] in
/-- The same wreath preimage is retained when the first vertex is viewed in Mc. -/
theorem wreath_preimage_inside (W : Subgroup FourWreathTwo.Wreath) :
    (W.comap (wreathMap (insideRecognition c r))).map
      ((H.subgroupOf Mc).subtype.comp (pCore 2 (H.subgroupOf Mc)).subtype) =
    ((W.comap (wreathMap r)).map (H.subtype.comp (pCore 2 H).subtype)).subgroupOf Mc := by
  let e := subgroupOfEquivOfLe c.H_le_Mc
  let ce := LocalCoreTransport.coreEquiv 2 e
  have hc (x : pCore 2 (H.subgroupOf Mc)) : ((ce x : H) : G) = x.val.val.val := rfl
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨ce a,?_,hc a⟩
    change wreathMap r (ce a) ∈ W
    rw [←wreath_inside c r]
    exact ha
  · rintro ⟨a,ha,he⟩
    obtain ⟨b,rfl⟩ := ce.surjective a
    refine ⟨b,?_,Subtype.ext ((hc b).symm.trans he)⟩
    change wreathMap (insideRecognition c r) b ∈ W
    rw [wreath_inside c r]
    exact ha

/-- The original source involution remains central under the same recognition inside Mc. -/
theorem marked_center_inside :
    (markedCore (insideRecognition c r)).map
      ((H.subgroupOf Mc).subtype.comp (pCore 2 (H.subgroupOf Mc)).subtype) ≤ center Mc := by
  have hm : (markedCore (insideRecognition c r)).map
      ((H.subgroupOf Mc).subtype.comp (pCore 2 (H.subgroupOf Mc)).subtype) =
      ((markedCore r).map (H.subtype.comp (pCore 2 H).subtype)).subgroupOf Mc := by
    simpa only [MonoidHom.comap_bot,wreathMap_ker] using wreath_preimage_inside c r ⊥
  have hmark : (markedCore r).map (H.subtype.comp (pCore 2 H).subtype) =
      centralInvolutions T := markedCore_image T H c.sylow_le_H c.mark_card r
  have hcent : (markedCore (insideRecognition c r)).map
      ((H.subgroupOf Mc).subtype.comp (pCore 2 (H.subgroupOf Mc)).subtype) ≤ center Mc := by
    rw [hm,hmark]
    intro z hz
    apply mem_center_iff.mpr
    intro m
    apply Subtype.ext
    have hm : (m : G) ∈ centralizer (centralInvolutions T : Set G) := by
      rw [←c.Mc_centralizer]
      exact m.property
    exact (hm z hz).symm
  exact hcent

include c in
/-- The source core reduction inside the literal containing group Mc. -/
theorem normal_quaternion_or_eq_source :
    H = Mc ∨ (((FourWreathTwo.base.comap (wreathMap r)).map
      (H.subtype.comp (pCore 2 H).subtype)).subgroupOf Mc).Normal := by
  let hTMc := c.sylow_le_H.trans c.H_le_Mc
  let S := T.subtype hTMc
  have hSH : (S : Subgroup Mc) ≤ H.subgroupOf Mc := fun _ hx => c.sylow_le_H hx
  rcases normal_quaternion_or_eq (H.subgroupOf Mc) (insideRecognition c r) S hSH
      (marked_center_inside c r) c.Mc_characteristic_two with he | hn
  · left
    apply le_antisymm c.H_le_Mc
    intro x hx
    exact show (⟨x,hx⟩ : Mc) ∈ H.subgroupOf Mc from he.ge (mem_top _)
  · right
    rwa [wreath_preimage_inside c r] at hn

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.OriginalRigidity
end
