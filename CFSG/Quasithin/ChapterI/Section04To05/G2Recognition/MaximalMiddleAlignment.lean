module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalWeylCoordinates
public import Theory.SpecificGroups.G2.TernaryBorelTwists
public import Theory.GroupTheory.Amalgam.SylowNormalizerAlignment
public import Theory.GroupTheory.Amalgam.TwistTransport

/-!
# Aligning the whole original middle with the Atlas Borel

Start with the constructed full short and long endpoint isomorphisms on the
original aligned pair. Sylow conjugacy corrects each map inside its target
parabolic to identify the whole Sylow normalizer. Conjugacy inside that Borel
also identifies the original Klein four torus. All corrections are explicit,
and the original core coordinates, full actor equations and right Sylow
aligner survive as the displayed conjugated formulas.

The two middle restrictions define one actual automorphism of the entire
Borel. Both commuting squares hold for the corresponding twist of the exact
Atlas amalgam. The original ambient group faithfully completes this twist,
with the same endpoint ranges, whole middle, and involutions of orders two,
two and product six. Source simplicity makes the amalgam intrinsically
faithful, excluding the radical-exchanging discrepancy. The discrepancy also
preserves the split torus and the whole six-root subgroup.

Removing this remaining automorphism by endpoint extensions is still required
before the already proved completion-recognition theorem applies. The
independent strongly-three-embedded source branch is not excluded here.
The literal Chapter14 application is Chapter14MiddleAlignment.
Source: Aschbacher–Smith I.4.5, p.417, via F.4.26, p.288.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace AlignedCubicPair
variable {t : CubicTorus c} (p : AlignedCubicPair t)

/-- The original Klein four inside the literal whole middle. -/
abbrev middleTorus (_p : AlignedCubicPair t) : Subgroup t.leftCubicBorel :=
  (t.torus.map c.H.subtype).subgroupOf t.leftCubicBorel

/-- Both original endpoint maps, corrected by explicit inner conjugations,
identify the entire common middle and its original Klein four torus. -/
structure MiddleAlignment where
  leftComparison : t.ShortQuotientComparison p.core_order
  rightComparison : t.swap.LongQuotientComparison p.right_core_order
  leftCorrection : Atlas.G2.TernaryBorel.P false
  rightCorrection : Atlas.G2.TernaryBorel.P true
  leftMiddle : t.leftCubicBorel ≃* Atlas.G2.TernaryBorel.B
  rightMiddle : t.leftCubicBorel ≃* Atlas.G2.TernaryBorel.B
  left_commutes : ∀ b,
    ((p.leftAtlasEndpointEquiv leftComparison).trans (MulAut.conj leftCorrection))
      (p.amalgam.left b)=inclusion (Atlas.G2.TernaryBorel.borel_le_endpoint false) (leftMiddle b)
  right_commutes : ∀ b,
    ((p.rightAtlasEndpointEquiv rightComparison).trans (MulAut.conj rightCorrection))
      (p.amalgam.right b)=inclusion (Atlas.G2.TernaryBorel.borel_le_endpoint true) (rightMiddle b)
  left_torus : p.middleTorus.map leftMiddle.toMonoidHom=
    Atlas.G2.TernaryBorel.A.subgroupOf Atlas.G2.TernaryBorel.B
  right_torus : p.middleTorus.map rightMiddle.toMonoidHom=
    Atlas.G2.TernaryBorel.A.subgroupOf Atlas.G2.TernaryBorel.B

/-- No middle identification or torus-image premise is required. -/
theorem nonempty_middleAlignment : Nonempty p.MiddleAlignment := by
  obtain ⟨⟨l⟩,⟨r⟩⟩ := p.nonempty_endpoint_comparisons
  obtain ⟨S,hS⟩ := t.maximal_extension_sylow p.core_order
  have hSB : (S:Subgroup G)≤t.leftCubicBorel := hS ▸ le_sup_left
  have hBL := t.leftCubicBorel_le
  have hBR : t.leftCubicBorel≤p.rightEndpoint := p.overlap ▸ inf_le_right
  have hN (K : Subgroup G) (hBK : t.leftCubicBorel≤K) :
      normalizer (S.subtype (hSB.trans hBK):Set K)=(inclusion hBK).range := by
    rw [inclusion_range]
    change normalizer (((S:Subgroup G).subgroupOf K):Set K)=_
    rw [←subgroupOf_normalizer_eq (hSB.trans hBK),hS,t.maximal_sylow_normalizer_eq p.core_order]
  have hA : Nat.card p.middleTorus=4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show t.torus.map c.H.subtype≤t.leftCubicBorel from le_sup_right)).toEquiv]
    let : IsKleinFour (t.torus.map c.H.subtype) := t.ambient_torus_kleinFour
    exact IsKleinFour.card_four
  have hi : ¬2∣p.middleTorus.index := by
    have hh := p.middleTorus.card_mul_index
    rw [hA,(t.maximal_leftCubicBorel_split p.core_order).2.2.2] at hh
    have he : p.middleTorus.index=729 := by omega
    rw [he]
    decide
  let A : Sylow 2 t.leftCubicBorel := (IsPGroup.of_card (p:=2) (n:=2) hA).toSylow hi
  have hM (side : Bool) :
      normalizer (Atlas.G2.TernaryBorel.endpointSylow side:Set (Atlas.G2.TernaryBorel.P side))=
      (inclusion (Atlas.G2.TernaryBorel.borel_le_endpoint side)).range := by
    rw [inclusion_range,Atlas.G2.TernaryBorel.endpointSylow_normalizer]
  obtain ⟨g,u,hu,_,hAu⟩ := RankTwoAmalgam.exists_normalized_normalizer_endpoint_with_sylow
    (inclusion hBL) (inclusion (Atlas.G2.TernaryBorel.borel_le_endpoint false))
    (inclusion_injective _) (inclusion_injective _)
    (S.subtype (hSB.trans hBL)) (hN _ hBL)
    (Atlas.G2.TernaryBorel.endpointSylow false) (hM false)
    A Atlas.G2.TernaryBorel.torusSylow (p.leftAtlasEndpointEquiv l)
  obtain ⟨h,v,hv,_,hAv⟩ := RankTwoAmalgam.exists_normalized_normalizer_endpoint_with_sylow
    (inclusion hBR) (inclusion (Atlas.G2.TernaryBorel.borel_le_endpoint true))
    (inclusion_injective _) (inclusion_injective _)
    (S.subtype (hSB.trans hBR)) (hN _ hBR)
    (Atlas.G2.TernaryBorel.endpointSylow true) (hM true)
    A Atlas.G2.TernaryBorel.torusSylow (p.rightAtlasEndpointEquiv r)
  exact ⟨⟨l,r,g,h,u,v,hu,hv,hAu,hAv⟩⟩

namespace MiddleAlignment
variable {p} (d : p.MiddleAlignment)

noncomputable def leftEndpointEquiv : p.leftEndpoint ≃* Atlas.G2.TernaryBorel.P false :=
  (p.leftAtlasEndpointEquiv d.leftComparison).trans (MulAut.conj d.leftCorrection)
noncomputable def rightEndpointEquiv : p.rightEndpoint ≃* Atlas.G2.TernaryBorel.P true :=
  (p.rightAtlasEndpointEquiv d.rightComparison).trans (MulAut.conj d.rightCorrection)

/-- The corrected short map retains the same constructed core coordinates. -/
theorem leftEndpointEquiv_core (x : p.leftCore) :
    (d.leftEndpointEquiv (inclusion t.cubicCore_le_normalizer x):Atlas.G2.Model (ZMod 3))=
      MulAut.conj (d.leftCorrection:Atlas.G2.Model (ZMod 3))
        (t.cubicAtlasShortEquiv p.core_order d.leftComparison.coordinates d.leftComparison.form x) := by
  change (d.leftCorrection:Atlas.G2.Model (ZMod 3))*
    (p.leftAtlasEndpointEquiv d.leftComparison (inclusion t.cubicCore_le_normalizer x):
      Atlas.G2.Model (ZMod 3))*(d.leftCorrection:Atlas.G2.Model (ZMod 3))⁻¹=_
  rw [p.leftAtlasEndpointEquiv_core]
  rfl

/-- The corrected long map retains the original Sylow-aligner inclusion. -/
theorem rightEndpointEquiv_core (x : cubicOddCore (swapFactors c) t.swap.x) :
    (d.rightEndpointEquiv (p.rightEndpointEquiv (inclusion t.swap.cubicCore_le_normalizer x)):
      Atlas.G2.Model (ZMod 3))=
      MulAut.conj (d.rightCorrection:Atlas.G2.Model (ZMod 3))
        (t.swap.cubicAtlasLongEquiv p.right_core_order d.rightComparison.coordinates d.rightComparison.form x) := by
  change (d.rightCorrection:Atlas.G2.Model (ZMod 3))*
    (p.rightAtlasEndpointEquiv d.rightComparison
      (p.rightEndpointEquiv (inclusion t.swap.cubicCore_le_normalizer x)):
      Atlas.G2.Model (ZMod 3))*(d.rightCorrection:Atlas.G2.Model (ZMod 3))⁻¹=_
  rw [p.rightAtlasEndpointEquiv_core]
  rfl

/-- The full original short actor is transported by the same inner correction. -/
theorem leftEndpointEquiv_actor (a : Atlas.G2.TernaryLevi.GL23) :
    (d.leftEndpointEquiv (inclusion t.cubicLevi_le_normalizer
      ((t.cubicLeviLinearEquiv p.core_order).symm a)):Atlas.G2.Model (ZMod 3))=
      MulAut.conj (d.leftCorrection:Atlas.G2.Model (ZMod 3))
        (Atlas.G2.TernaryLevi.embedding false (d.leftComparison.actor a)) := by
  change (d.leftCorrection:Atlas.G2.Model (ZMod 3))*
    (p.leftAtlasEndpointEquiv d.leftComparison (inclusion t.cubicLevi_le_normalizer
      ((t.cubicLeviLinearEquiv p.core_order).symm a)):Atlas.G2.Model (ZMod 3))*
        (d.leftCorrection:Atlas.G2.Model (ZMod 3))⁻¹=_
  rw [p.leftAtlasEndpointEquiv_actor]
  rfl

/-- The full original long actor keeps the same aligner and inner correction. -/
theorem rightEndpointEquiv_actor (a : Atlas.G2.TernaryLevi.GL23) :
    (d.rightEndpointEquiv (p.rightEndpointEquiv (inclusion t.swap.cubicLevi_le_normalizer
      ((t.swap.cubicLeviLinearEquiv p.right_core_order).symm a))):Atlas.G2.Model (ZMod 3))=
      MulAut.conj (d.rightCorrection:Atlas.G2.Model (ZMod 3))
        (Atlas.G2.TernaryLevi.embedding true (d.rightComparison.actor a)) := by
  change (d.rightCorrection:Atlas.G2.Model (ZMod 3))*
    (p.rightAtlasEndpointEquiv d.rightComparison (p.rightEndpointEquiv
      (inclusion t.swap.cubicLevi_le_normalizer
        ((t.swap.cubicLeviLinearEquiv p.right_core_order).symm a))):Atlas.G2.Model (ZMod 3))*
        (d.rightCorrection:Atlas.G2.Model (ZMod 3))⁻¹=_
  rw [p.rightAtlasEndpointEquiv_actor]
  rfl

/-- The precise remaining disagreement, on the entire order-2916 middle. -/
def difference : MulAut Atlas.G2.TernaryBorel.B := d.leftMiddle.symm.trans d.rightMiddle

/-- The discrepancy already preserves the actual split torus. -/
theorem difference_torus :
    (Atlas.G2.TernaryBorel.A.subgroupOf Atlas.G2.TernaryBorel.B).map d.difference.toMonoidHom=
      Atlas.G2.TernaryBorel.A.subgroupOf Atlas.G2.TernaryBorel.B := by
  have hu : (Atlas.G2.TernaryBorel.A.subgroupOf Atlas.G2.TernaryBorel.B).map
      d.leftMiddle.symm.toMonoidHom=p.middleTorus :=
    (map_symm_eq_iff_map_eq p.middleTorus (e:=d.leftMiddle)).mpr d.left_torus
  change (Atlas.G2.TernaryBorel.A.subgroupOf Atlas.G2.TernaryBorel.B).map
    (d.rightMiddle.toMonoidHom.comp d.leftMiddle.symm.toMonoidHom)=_
  rw [←map_map,hu,d.right_torus]

/-- Both whole-middle squares now commute with the explicit twisted model. -/
noncomputable def borelTwistIso : RankTwoAmalgam.Iso p.amalgam
    (RankTwoAmalgam.twistRight
      (ChapterF.GreenBook.LieModels.G2.borelAmalgam (F:=ZMod 3)) d.difference) :=
  RankTwoAmalgam.isoTwistOfEndpointSquares d.leftEndpointEquiv d.rightEndpointEquiv
    d.leftMiddle d.rightMiddle d.left_commutes d.right_commutes

/-- Transfer the discrepancy to the exact Atlas intersection carrier. -/
def atlasDifference : MulAut (ChapterF.GreenBook.LieModels.G2.overlap (F:=ZMod 3)) :=
  MulAut.congr (ChapterF.GreenBook.LieModels.G2.borelIso (F:=ZMod 3)).symm.middle d.difference

/-- The target uses the literal Atlas amalgam, including its actual overlap maps. -/
noncomputable def atlasTwistIso : RankTwoAmalgam.Iso p.amalgam
    (RankTwoAmalgam.twistRight
      (ChapterF.GreenBook.LieModels.G2.amalgam (F:=ZMod 3)) d.atlasDifference) :=
  d.borelTwistIso.trans
    ((ChapterF.GreenBook.LieModels.G2.borelIso (F:=ZMod 3)).symm.twistRightIso d.difference)

/-- The actual original group is a faithful generating completion of this twist. -/
noncomputable def atlasTwistCompletion : RankTwoAmalgam.FaithfulCompletion
    (RankTwoAmalgam.twistRight
      (ChapterF.GreenBook.LieModels.G2.amalgam (F:=ZMod 3)) d.atlasDifference) (G:=G) :=
  p.completion.comapIso d.atlasTwistIso.symm

@[simp] theorem atlasTwistCompletion_left_range :
    d.atlasTwistCompletion.left.range=p.leftEndpoint := by
  rw [atlasTwistCompletion,RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
    p.completion_left_range]
@[simp] theorem atlasTwistCompletion_right_range :
    d.atlasTwistCompletion.right.range=p.rightEndpoint := by
  rw [atlasTwistCompletion,RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
    p.completion_right_range]
@[simp] theorem atlasTwistCompletion_middle_range :
    d.atlasTwistCompletion.middle.range=t.leftCubicBorel := by
  rw [atlasTwistCompletion,RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range,
    p.completion_middle_range]

/-- The same original involutions retain every completion-recognition order premise. -/
theorem atlasTwistCompletion_involutions :
    p.leftReflection∈d.atlasTwistCompletion.left.range ∧
    p.rightReflection∈d.atlasTwistCompletion.right.range ∧
    p.leftReflection∉d.atlasTwistCompletion.middle.range ∧
    p.rightReflection∉d.atlasTwistCompletion.middle.range ∧
    orderOf p.leftReflection=2 ∧ orderOf p.rightReflection=2 ∧
    orderOf (p.leftReflection*p.rightReflection)=6 := by
  rw [d.atlasTwistCompletion_left_range,d.atlasTwistCompletion_right_range,
    d.atlasTwistCompletion_middle_range]
  exact ⟨p.left_mem,p.right_mem,p.left_out,p.right_out,p.left_order,p.right_order,p.product_order⟩

end MiddleAlignment

/-- Intrinsic amalgam faithfulness comes from the proved source simplicity. -/
theorem amalgam_faithful : RankTwoAmalgam.Faithful p.amalgam := by
  let : IsSimpleGroup G := ambient_simple c
  apply RankTwoAmalgam.faithful_ofSubgroups_of_completion _ _ _ _ _ p.generated
  intro N hN hNB
  rcases hN.eq_bot_or_eq_top with h | h
  · exact h
  · exact (p.left_out (hNB (h ▸ mem_top p.leftReflection))).elim

namespace MiddleAlignment
variable {p} (d : p.MiddleAlignment)

/-- The remaining model twist inherits intrinsic faithfulness as well. -/
theorem atlasTwist_faithful : RankTwoAmalgam.Faithful
    (RankTwoAmalgam.twistRight
      (ChapterF.GreenBook.LieModels.G2.amalgam (F:=ZMod 3)) d.atlasDifference) :=
  d.atlasTwistIso.faithful p.amalgam_faithful

/-- Intrinsic faithfulness rules out exchanging the two marked radicals. -/
theorem difference_not_exchange :
    (Atlas.G2.TernaryBorel.middleRadical false).map d.difference.toMonoidHom≠
      Atlas.G2.TernaryBorel.middleRadical true :=
  Atlas.G2.TernaryBorel.faithful_twist_not_exchange d.difference
    (d.borelTwistIso.faithful p.amalgam_faithful)

/-- The same discrepancy preserves the whole order-729 subgroup. -/
theorem difference_unipotent :
    (Atlas.G2.TernaryBorel.U.subgroupOf Atlas.G2.TernaryBorel.B).map d.difference.toMonoidHom=
      Atlas.G2.TernaryBorel.U.subgroupOf Atlas.G2.TernaryBorel.B :=
  Atlas.G2.TernaryBorel.automorphism_unipotent d.difference

end MiddleAlignment
end AlignedCubicPair
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
