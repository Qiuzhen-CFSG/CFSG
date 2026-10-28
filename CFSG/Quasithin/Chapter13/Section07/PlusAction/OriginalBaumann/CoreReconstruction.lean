module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CorePullback
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.Coordinates

/-!
# The original Baumann consumer of the symplectic core equality

The original natural L--T setup supplies the literal symplectic source and
its intrinsic MS pair. A core equality at its actual characteristic
replacement pulls back to the entire intrinsic component core, proving its
elementary, central and irreducible module clauses and both block conclusions.

The displayed core equality is the conclusion still supplied by the MS93
critical-distance branches, not a substitute for those source arguments.
Source: Aschbacher--Smith (13.7.4), via C.1.37; MS93 Sections 3 and 5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.ChapterC.NaturalSixControl
open Section08.SourceCompletion
open Section05.PlaneGeometry
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)

local notation "X" => (L ⊔ (T : Subgroup G) : Subgroup G)
local notation "LX" => L.subgroupOf X
local notation "VX" => V.subgroupOf X

theorem literal_original_coreReconstruction
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v ≠ 1)
    (hne : let := component_normal d
           let := local_module_normal d
           ¬ (elementaryAbelianMaxJ (sourceData d h hU hV v hv).R).map
             (sourceData d h hU hV v hv).q0 ≤ ChapterB.Offenders.Six.last)
    (hno : let := component_normal d
           let := local_module_normal d
           ¬ ∃ C : Subgroup (sourceData d h hU hV v hv).B,
             C.Characteristic ∧ C ≠ ⊥ ∧
             (C.map (sourceData d h hU hV v hv).B.subtype).Normal)
 :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ c : BinaryMS.MS93.CharacteristicReduction ((LX).subgroupOf (LX ⊔ d0.B))
        (d0.B.subgroupOf (LX ⊔ d0.B)),
      BinaryMS.MS93.core c.radical (BinaryMS.MS93.alpha c.radical) =
        BinaryMS.MS93.U c.radical (BinaryMS.MS93.alpha c.radical) →
      CoreReconstruction LX ∧ IsBlock LX ∧ IsAlternatingBlock LX 6 := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro c he
  let hm : IntrinsicMSPair d0 := d0.intrinsicMSPair_of_full_image hne hno
  have hc := SymplecticSetup.SourceData.coreReconstruction_of_reduced_core_eq_U d0 hm c he
  have hb := SymplecticSetup.SourceData.ms_block_of_reduced_core_eq_U d0 hm c he
  exact ⟨hc,hb⟩

end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
