module
public import CFSG.Quasithin.Chapter14.Section02.ExceptionalDiagram.Source
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramResidual


/-!
# The selected marked-parabolic consumer for source14.2.13

The selector's literal marked point-parabolic residual supplies the actual
K₁. The source13 core calculation is applied to that residual; no abstract
parabolic replacement is made. The resulting O₂(Y) containment is exactly
the normalizer containment needed by the proper-index assembly.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.ExceptionalDiagram
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- Original source13 for the actual residual of the marked point-parabolic
preimage. The source12 action is retained on Mc, with its literal inner
preimage placed in the normalizer of this same residual. -/
theorem source_exceptional_markedParabolic_twoCore_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K : Subgroup H) (hK : K.IsCComponent) (hn : K.Normal)
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (mark : sourceImage ((H ⊓ M).subgroupOf H) K ≃* Matrix.PSL3Four.PSL)
    (ρ : Mc →* MulAut Matrix.PSL3Four.PSL)
    (hinner : MulAut.innerSubgroup Matrix.PSL3Four.PSL ≤ ρ.range)
    (hswap : ∃ t : Mc, (t : G) ∈ (T : Subgroup G) ∧
      Matrix.PSL3.LinearThree.OuterExtensions.diagramAction Matrix.PSL3Four.F
        (n := 2) (by decide) (by simpa using Matrix.PSL3Four.card_F) (ρ t) ≠ 1)
    (hplace : (T : Subgroup G) ⊓
        ((MulAut.innerSubgroup Matrix.PSL3Four.PSL).comap ρ).map Mc.subtype ≤
      (T : Subgroup G) ⊓ normalizer
        ((markedParabolicResidual ((H ⊓ M).subgroupOf H) K mark
          (Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F)).map H.subtype : Set G)) :
    (sourceResidual M Mc).pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer
      ((markedParabolicResidual ((H ⊓ M).subgroupOf H) K mark
        (Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F)).map H.subtype : Set G) :=
  source_exceptional_twoCore_le_of_marked_action hG T hempty hM hu hmany hcard e
    H hH K hK hn hgen hm ρ hinner hswap _ hplace

end CFSG.Quasithin.Chapter14.Section02.ExceptionalDiagram
