module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Completion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalAlignedLinear

/-!
# Marked linear quotients in the original Chapter 14 completion

The original source data supply the two aligned cubic normalizers with
surjective GL₂(3) actions, whose kernels are their original marked cores.
Both literal inclusions of the whole Borel feed a joint linear action with
kernel the common order81 core and image of order36. On each side the
Borel image is the normalizer of the marked cubic Sylow image.

These are consequences of the source configuration, with no matrix-model
premise. The actual faithful generating completion and all markings remain
intact. Identification of the whole endpoint actions with the Atlas amalgam
and the independent strongly-three-embedded exclusion still belong to the
I.4.5 assembly; this is not unconditional recognition.
Source: Aschbacher–Smith I.4.5, p.417, and 14.4.14, pp.1008–1010.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour Chapter14.Section04.DimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Actual marked endpoint and Borel quotient maps in the large-core source branch. -/
theorem source_cubic_linear_completion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c) (m : c.M) (g : G),
      let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
      let D := cubicOddCore c t.x
      let R := cubicOddCore (swapFactors c) t.y
      orderOf m=3 ∧ MulAut.conj g (m:G)∈E ∧
      MulAut.conj g (m:G)∉zpowers ((t.x:c.H):G) ∧
      MulAut.conj g (m:G)∉zpowers ((t.y:c.H):G) ∧
      ((c.H≠⊤ ∧ 3∣Nat.card c.H ∧
        ∀ a : G, a∉c.H →
          ¬3∣Nat.card (c.H ⊓ c.H.map (MulAut.conj a).toMonoidHom : Subgroup G)) ∨
      (Nat.card D=243 ∧ Nat.card R=243 ∧
        ∃ p : AlignedCubicPair t,
          Nat.card t.leftCubicBorel=2916 ∧
          p.leftEndpoint ⊓ p.rightEndpoint=t.leftCubicBorel ∧
          p.leftEndpoint ⊔ p.rightEndpoint=⊤ ∧
          Nonempty (RankTwoAmalgam.FaithfulCompletion p.amalgam (G:=G)) ∧
          Function.Surjective p.leftLinearAction ∧ Function.Surjective p.rightLinearAction ∧
          p.leftLinearAction.ker=p.leftCore.subgroupOf p.leftEndpoint ∧
          p.rightLinearAction.ker=p.rightCore.subgroupOf p.rightEndpoint ∧
          p.middleLinearAction.ker=(p.leftCore⊓p.rightCore).subgroupOf t.leftCubicBorel ∧
          Nat.card p.middleLinearAction.range=36 ∧
          (t.leftCubicBorel.subgroupOf p.leftEndpoint).map p.leftLinearAction=
            normalizer (((t.leftCoreExtension.subgroupOf p.leftEndpoint).map
              p.leftLinearAction):Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) ∧
          (t.leftCubicBorel.subgroupOf p.rightEndpoint).map p.rightLinearAction=
            normalizer (((t.leftCoreExtension.subgroupOf p.rightEndpoint).map
              p.rightLinearAction):Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))))) := by
  obtain ⟨c,t,m,g,hm,hg,hgx,hgy,h⟩ := source_cubic_aligned_completion d earlier hq chosen
    structural alternatives F hne hZ hcard localData
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  rcases h with hsmall | ⟨hx,hy,p,hB,hI,hgen,hcomp⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨hx,hy,p,hB,hI,hgen,hcomp,p.leftLinearAction_surjective,
      p.rightLinearAction_surjective,p.leftLinearAction_kernel,p.rightLinearAction_kernel,
      p.middleLinearAction_kernel,p.middleLinearAction_range_card,
      p.leftLinearAction_borel,p.rightLinearAction_borel⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
