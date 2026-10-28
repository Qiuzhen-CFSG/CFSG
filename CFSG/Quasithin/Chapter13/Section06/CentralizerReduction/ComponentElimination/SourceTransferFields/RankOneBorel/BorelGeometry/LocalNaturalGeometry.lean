module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.LocalNaturalPlacement
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.ResidualProduct
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.MarkedAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.CheckedRigidity
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.Transport
/-!
# Direct natural rank-one Borel geometry

The natural section of the marked component supplies the Baumann image
containment directly.  This wrapper feeds that containment into the existing
Borel geometry and checked-rigidity consumers, removing the former explicit
E.2.3 factor and Baumann source callbacks while retaining the literal source
maps and residual product conclusion.

Source: Aschbacher--Smith 13.6.18, printed p.931, together with E.2.3,
pp.216--217.
-/
public section
open Subgroup Stellmacher Matrix.SpecialLinearGroup
open scoped MatrixGroups IsMulCommutative
open Matrix.SpecialLinearGroup.RankOneResidual
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry
open ComponentSelection A5Module Placement
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The marked natural section constructs all Borel geometry and fixation data.
The natural placement theorem is the only image-containment input. -/
theorem source_geometry_natural
    {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) (K M : Subgroup G)
    (hL : Tv (T : Subgroup G) (markedV d.module) ≤
      normalizer (Lv L (markedV d.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.module) ≤
      centralizer ({markedZ d.module} : Set G))
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module))
    (hnorm : Tv (T : Subgroup G) (markedV d.module) ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L (T : Subgroup G) (markedZ d.module) (markedV d.module))]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : NaturalSection (F := F)
      (componentRepresentation K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz)
      (movingSpace K L (T : Subgroup G) (markedZ d.module) (markedV d.module)))
    (hq : IsSQTK KnownSimple.IsKnownSimple (Gv (markedV d.module)))
    (hzOmega : markedZ d.module ∈ omegaOneCenterAmbient
      (Tv (T : Subgroup G) (markedV d.module)))
    (hpush : HigherFieldParabolics.CharacteristicNormalizerObstruction
      (Tv (T : Subgroup G) (markedV d.module)) K)
    (hSylow : Chapter1.IsSylowIn 2
      (Tv (T : Subgroup G) (markedV d.module)) (Gv (markedV d.module)))
    (hf : Theory.GroupTheory.generalizedFitting (Gv (markedV d.module)) =
      pCore 2 (Gv (markedV d.module)))
    (P : Sylow 2 (K ⊔ Tv (T : Subgroup G) (markedV d.module) : Subgroup G))
    (hP : (P : Subgroup (K ⊔ Tv (T : Subgroup G) (markedV d.module) : Subgroup G)) =
      (Tv (T : Subgroup G) (markedV d.module)).subgroupOf
        (K ⊔ Tv (T : Subgroup G) (markedV d.module)))
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
    (h1324 : ChapterB.baumann (T : Subgroup G) ≤
      Tv (T : Subgroup G) (markedV d.module))
    (h1325 : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M)
    (hMV : normalizer (V : Set G) ≤ M)
    (hBV : Mv M (markedV d.module) ≤ normalizer (V : Set G))
    (hlocal : (pResidual 2 (Mv M (markedV d.module))).map
      (Mv M (markedV d.module)).subtype ≤
      Lv L (markedV d.module) ⊔ (M ⊓ centralizer (V : Set G))) :
    ∃ s' : NaturalSection (F := F)
        (componentRepresentation K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz)
        (movingSpace K L (T : Subgroup G) (markedZ d.module) (markedV d.module)),
      let B := borel K (Tv (T : Subgroup G) (markedV d.module))
      let R := (pResidual 2 B).map B.subtype
      Tv (T : Subgroup G) (markedV d.module) ≤ B ∧
      B ≤ K ⊔ Tv (T : Subgroup G) (markedV d.module) ∧
      B ≤ normalizer (elementaryAbelianMaxJ
        (Tv (T : Subgroup G) (markedV d.module)) : Set G) ∧
      B ≤ normalizer (ChapterB.baumann
        (Tv (T : Subgroup G) (markedV d.module)) : Set G) ∧
      B ≤ Mv M (markedV d.module) ∧
      ((B.subgroupOf K).map
        (componentMap K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz)).map
        s'.actor.toMonoidHom = rankOneBorel F ∧ n = 2 ∧
      R ⊔ (M ⊓ centralizer (V : Set G)) =
        Lv L (markedV d.module) ⊔ (M ⊓ centralizer (V : Set G)) ∧
      R ≤ centralizer ({markedA d.module} : Set G) ∧
      ((R.subgroupOf K).map
        (componentMap K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz)).map
        s'.actor.toMonoidHom = rankOneBorel F ∧
      checkedQuotientMap (markedV d.module)
          (inclusion inf_le_right d.checkedPoint) ∈
        centralizer (checkedImage (markedV d.module) B : Set (Gcheck (markedV d.module))) := by
  have hLV : Lv L (markedV d.module) ≤ normalizer (V : Set G) :=
    (residual_le_L d.module).trans d.module.normalizes
  have hc := marked_residual_conjugation_card d.module hLV
  have hplace := local_natural_normalizations_and_placement d.module K
    (T : Subgroup G) M d.action_kernel hL hz hK hnorm hF hb s hq hzOmega hpush
    hSylow hf P hP hmin h1324 h1325 hBV hMV
  have hzV : markedZ d.module ∈ V := map_mem d.module _
  let a : Gv (markedV d.module) := inclusion inf_le_right d.checkedPoint
  have ha := markedA_mem_centralizer d.module
  obtain ⟨s', hTB, hBK, hBim, hn2, hRa, hRim, hcheck⟩ :=
    local_natural_conclusions_of_marking d.module K (T : Subgroup G) M
      d.action_kernel hL hz hK hnorm hF hb s hq hzOmega hpush hSylow hf P hP hmin
      h1324 h1325 hMV hBV hLV hc a ha.1 ha.2
      (marked_checked_central d) hlocal
  refine ⟨s', hTB, hBK, hplace.1, hplace.2.1, hplace.2.2, hBim, hn2, ?_, hRa, hRim,
    hcheck⟩
  exact residual_product_eq_of_local_source K L (T : Subgroup G) M V _
    (markedZ d.module) (markedV d.module) hL hz hK hnorm s'
    (by rw [hF, hn2]; decide) hBim hplace.2.2 hBV hLV hMV hc hzV hlocal

/-- Checked rigidity lifts the direct natural geometry to the component. -/
theorem source_component_centralizes_natural
    {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) (K M : Subgroup G)
    (hL : Tv (T : Subgroup G) (markedV d.module) ≤
      normalizer (Lv L (markedV d.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.module) ≤
      centralizer ({markedZ d.module} : Set G))
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module))
    (hnorm : Tv (T : Subgroup G) (markedV d.module) ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L (T : Subgroup G) (markedZ d.module) (markedV d.module))]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : NaturalSection (F := F)
      (componentRepresentation K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz)
      (movingSpace K L (T : Subgroup G) (markedZ d.module) (markedV d.module)))
    (hq : IsSQTK KnownSimple.IsKnownSimple (Gv (markedV d.module)))
    (hzOmega : markedZ d.module ∈ omegaOneCenterAmbient
      (Tv (T : Subgroup G) (markedV d.module)))
    (hpush : HigherFieldParabolics.CharacteristicNormalizerObstruction
      (Tv (T : Subgroup G) (markedV d.module)) K)
    (hSylow : Chapter1.IsSylowIn 2
      (Tv (T : Subgroup G) (markedV d.module)) (Gv (markedV d.module)))
    (hf : Theory.GroupTheory.generalizedFitting (Gv (markedV d.module)) =
      pCore 2 (Gv (markedV d.module)))
    (P : Sylow 2 (K ⊔ Tv (T : Subgroup G) (markedV d.module) : Subgroup G))
    (hP : (P : Subgroup (K ⊔ Tv (T : Subgroup G) (markedV d.module) : Subgroup G)) =
      (Tv (T : Subgroup G) (markedV d.module)).subgroupOf
        (K ⊔ Tv (T : Subgroup G) (markedV d.module)))
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
    (h1324 : ChapterB.baumann (T : Subgroup G) ≤
      Tv (T : Subgroup G) (markedV d.module))
    (h1325 : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M)
    (hMV : normalizer (V : Set G) ≤ M)
    (hBV : Mv M (markedV d.module) ≤ normalizer (V : Set G))
    (hlocal : (pResidual 2 (Mv M (markedV d.module))).map
      (Mv M (markedV d.module)).subtype ≤
      Lv L (markedV d.module) ⊔ (M ⊓ centralizer (V : Set G))) :
    n = 2 ∧ K ≤ centralizer ({markedA d.module} : Set G) := by
  obtain ⟨_, _, _, _, _, _, _, hn2, _, _, _, hcheck⟩ :=
    source_geometry_natural d K M hL hz hK hnorm hF hb s hq hzOmega hpush hSylow hf
      P hP hmin h1324 h1325 hMV hBV hlocal
  refine ⟨hn2, ?_⟩
  exact CheckedRigidity.source_marked_centralizes d K hK.1.1 hnorm
    hK.1.2.2.1 (hn2 ▸ hb) hcheck

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry
