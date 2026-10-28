module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection.Marked
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SourcePreparation

/-!
# The intrinsic G₂(2)′ quotient from the original flag

The original centralizer supplies its Sylow subgroup, two-reduced plus action
and quasisimple component image. The complete A.3.6 source theorem and the
proved binary-derived covering theorem identify K/O₂(K) with the literal
G₂(2)′ plus image. The same map gives C_K(W_K)=O₂(K). No minimum, central
cover, A.3.6 callback or block assumption is left explicit.

The subsequent whole-core and natural-action reconstruction in C.1.32 is
still needed to invoke the already proved G₂ block exclusion of 13.6.22.
Source: Aschbacher--Smith 13.6.22, printed p.932, first paragraph.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
open ComponentSelection A5Module ComponentReduction InitialSieve SourceContainment
open SourceOrthogonal.Selection
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- The original binary-G₂ plus marking is the intrinsic quotient marking,
with precisely its original action kernel. -/
theorem g2_intrinsic_marking_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (e : plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ∃ eK : K ⧸ pCore 2 K ≃* commutator (Atlas.G2.Model (ZMod 2)),
      (∀ k : K, eK (QuotientGroup.mk' _ k) =
        e (intrinsicToPlus K L (T : Subgroup G) (markedZ d.flag.module)
          (markedV d.flag.module) hK.1.1 hL hz k)) ∧
      (centralizer (WK K L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) : Set G)).subgroupOf K = pCore 2 K := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.flag.module))
      (Gv (markedV d.flag.module)) := ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩
  let : IsQuasisimple (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K) := plusImage_K_quasisimple_source
    K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz hK hSylow
  let : IsQuasisimple (commutator (Atlas.G2.Model (ZMod 2))) :=
    IsQuasisimple.of_mulEquiv e
  have hR := LinearThree.CentralAction.ModuleAlternatives.plus_twoCore_eq_bot
    K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)
    hK.1.1 hL hz hSylow
  exact G2Selection.exists_intrinsic_marking
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    K L (T : Subgroup G) _ _
    (standing.qtke.involution_centralizer_sqtk (marked_orders d.flag.module).2)
    hL hz hK hR e

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
