module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesDegrees
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockLinearThree
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction

/-!
# The actual natural SL₃ row in the rank-one block classification

The B.5 classifier acts on the offender-generated subgroup. Restriction
transport identifies its literal moved/fixed quotient with the canonical star
section, retaining both the component map and the conjugation action. A natural
SL₃ row therefore supplies an intrinsic block model. The original L quotient
excludes degree one and recovers the original field degree n. The established
involutory-action argument then excludes this row.

This proves the natural-action branch. Deriving that action from an arbitrary
SL₃ star-group isomorphism, and completing the other C.4.1 rows, remain with
qt-d-1222-rankone-uniqueness-block. No row selection is asserted here.
Source: Aschbacher–Smith B.5.1, C.4.7 and original 4.3.7,
printed pp.99–103,153,615–616.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
open ChapterC ChapterB.QuasisimpleSource Representation Representation.BinaryOffender
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open scoped IsMulCommutative

/-- The moved section returned by the source classifier yields the intrinsic
block model, even though its ambient actor is the offender-generated subgroup. -/
theorem SourceConfiguration.block_model_of_restricted_star_moving
    (c : SourceConfiguration T L) (hb : IsBlock c.K)
    (J : Subgroup (StarQuotient (c.K.map c.H.subtype) (c.I.pCoreIn 2)))
    (hCJ : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
      (c.K.map c.H.subtype) ≤ J)
    (s : MovedSection ((starRepresentation (c.K.map c.H.subtype)
      (c.I.pCoreIn 2)).comp J.subtype)
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype)).subgroupOf J))
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) A W)
    (E : ActionEquiv (s.action.comp
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype)).subgroupOf J).subtype) σ) :
    IsLinearBlockModel c.K σ := by
  let a := s.componentEmbeddingEquiv c.block_star_section
    (subgroupOfEquivOfLe hCJ).symm (LinearMap.id : _ →ₗ[ZMod 2] _)
    (fun _ _ h => h) (fun _ _ => rfl) (by
      rw [Submodule.map_id,moved_comp_map,map_subgroupOf_eq_of_le hCJ])
  apply c.block_model_of_star_moving hb σ
  exact ⟨a.groupEquiv.trans E.groupEquiv,a.linearEquiv.trans E.linearEquiv,
    fun k v => (congrArg E.linearEquiv (a.intertwines k v)).trans
      (E.intertwines (a.groupEquiv k) (a.linearEquiv v))⟩

/-- The actual SL₃ natural row gives the required block with the original
field degree; neither a degree equality nor a parabolic premise is supplied. -/
theorem SourceConfiguration.linearThree_block_of_source_moved_action
    (c : SourceConfiguration T L) {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (J : Subgroup (StarQuotient (c.K.map c.H.subtype) (c.I.pCoreIn 2)))
    (hCJ : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
      (c.K.map c.H.subtype) ≤ J)
    (s : MovedSection ((starRepresentation (c.K.map c.H.subtype)
      (c.I.pCoreIn 2)).comp J.subtype)
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype)).subgroupOf J))
    (F : BinaryField)
    (E : ActionEquiv (s.action.comp
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype)).subgroupOf J).subtype) (linearNatural F 3)) :
    IsSL3EvenBlock c.K n := by
  have hm : IsLinearBlockModel c.K
      (specialLinearNatural (k := F.Carrier) 3) :=
    c.block_model_of_restricted_star_moving hb J hCJ s (linearNatural F 3) E
  obtain ⟨e⟩ := hm.quotient_iso
  have hgt := c.linearThree_degree_gt_one hn F.degree_pos hpsl F.card_eq e
  have heq := c.original_degree_of_linearThree hgt hpsl hf hb F.card_eq e
  refine ⟨by omega,hb.short,F.Carrier,inferInstance,inferInstance,?_,hm⟩
  rw [F.card_eq,heq]

/-- Apply the existing involutory-action obstruction to the literal B.5
natural row. The C.4.1 assembly still owns the other classification rows. -/
theorem SourceConfiguration.false_of_linearThree_source_moved_action
    {V : Subgroup G} (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (J : Subgroup (StarQuotient (c.K.map c.H.subtype) (c.I.pCoreIn 2)))
    (hCJ : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
      (c.K.map c.H.subtype) ≤ J)
    (s : MovedSection ((starRepresentation (c.K.map c.H.subtype)
      (c.I.pCoreIn 2)).comp J.subtype)
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype)).subgroupOf J))
    (F : BinaryField)
    (E : ActionEquiv (s.action.comp
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype)).subgroupOf J).subtype) (linearNatural F 3)) : False :=
  c.false_of_linearThree_block D hn hf hb
    (c.linearThree_block_of_source_moved_action hn hpsl hf hb J hCJ s F E)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
