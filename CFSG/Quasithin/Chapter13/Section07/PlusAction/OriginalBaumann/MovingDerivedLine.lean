module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.MovingDerivedLine
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.Coordinates
/-!
# Moving-radius derived bound in the original Baumann source

For each actual characteristic replacement, a marked natural binary central
quotient and containment of the radius derived subgroup in the fixed core
imply derived order at most two. All maps retain the original local action.
The explicit quotient coordinates remain the input of source (5.12)(2).

Source: Meierfrankenfeld--Stellmacher (1993), (3.10)(i), as used in (5.12)(2).
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
open CFSG.Quasithin.ChapterC CFSG.Quasithin.ChapterC.NaturalSixControl
open Section08.SourceCompletion Section05.PlaneGeometry
open Section08.TransvectionRecognition.Component.ModelExtension
open BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph BinaryPermutation
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
local notation "X" => (L⊔(T:Subgroup G):Subgroup G)
local notation "LX" => L.subgroupOf X

/-- The source (3.10)(i) derived bound on every actual characteristic
replacement with its natural central quotient marked. -/
theorem sourceData_movingRadius_derived_card_le_two
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v≠1) :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ (hm : IntrinsicMSPair d0)
      (r : CharacteristicReduction ((LX).subgroupOf (LX⊔d0.B))
        (d0.B.subgroupOf (LX⊔d0.B))),
    let s := (SymplecticSetup.SourceData.originalSource d0 hm).reduce r
    ∀ (e : ((Vcirc r.radical (alpha r.radical)) ⧸
        center (Vcirc r.radical (alpha r.radical))) ≃*
        Multiplicative (natural (Fin 6))) (σ : Model.S≃*Model.S),
      (∀ (m : r.overgroup) (p : Vcirc r.radical (alpha r.radical)),
        (e (QuotientGroup.mk' (center (Vcirc r.radical (alpha r.radical)))
          (SymplecticSetup.movingRadiusAction r.radical m p))).toAdd=
        naturalRepresentation (Fin 6) (σ (s.projection m))
          (e (QuotientGroup.mk' (center (Vcirc r.radical (alpha r.radical))) p)).toAdd) →
      ⁅Vcirc r.radical (alpha r.radical),Vcirc r.radical (alpha r.radical)⁆≤
        fixedCore r.radical (alpha r.radical) →
      Nat.card (⁅Vcirc r.radical (alpha r.radical),Vcirc r.radical (alpha r.radical)⁆:
        Subgroup (FreeAmalgam r.radical))≤2 := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r
  exact SymplecticSetup.SourceData.reducedSource_movingRadius_derived_card_le_two d0 hm r
end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
