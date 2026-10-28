module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.Complete
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.Coordinates
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.BlockChiefCount
/-!
# Excluding distance two in the original Chapter 13 Baumann source

The actual natural L--T setup supplies the intrinsic marked symplectic source.
The completed distance-two argument makes its component an alternating block.
The original abelian U_H and nonabelian V_H give the previously proved
chief-factor obstruction to that block. Hence every genuine characteristic
replacement of the intrinsic MS pair has critical distance different from two.

The intrinsic MS pair is the one produced from the original full-image and
characteristic-normalizer branch in `NaturalSixControl.MSReduction`; no core,
natural-section, finite-model or recognition premise remains here.
Source: Aschbacher--Smith 13.7.4 and C.1.37, using MS93 (3.6), pp.870--871.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.ChapterC.NaturalSixControl
open Section08.SourceCompletion Section05.PlaneGeometry
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
local notation "X" => (L ⊔ (T : Subgroup G) : Subgroup G)
local notation "LX" => L.subgroupOf X

theorem sourceData_reduced_distance_ne_two
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v ≠ 1) :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ (hm : IntrinsicMSPair d0)
      (r : BinaryMS.MS93.CharacteristicReduction ((LX).subgroupOf (LX ⊔ d0.B))
        (d0.B.subgroupOf (LX ⊔ d0.B))),
      ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical ≠ 2 := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r hb
  exact source_not_alternatingBlock d h hU hV
    (SymplecticSetup.SourceData.reducedSource_alternatingBlock_of_distance_two d0 hm r hb)
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
