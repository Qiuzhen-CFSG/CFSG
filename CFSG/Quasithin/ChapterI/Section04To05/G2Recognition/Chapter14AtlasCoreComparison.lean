module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Completion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalAlignedLinear
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.AtlasCoreComparison

/-!
# Concrete Atlas core targets in the literal Chapter 14 branch

Apply the canonical reconstruction to both original cores, with the actual
Atlas radicals, their four-dimensional quotients, and normalized cubic
markings. This discharges the previously abstract target-extension and
kernel-coordinate premises. The quotient-form comparisons remain explicit;
they must still be constructed with actor compatibility and matching on
the whole middle to obtain an Atlas amalgam isomorphism.

The original faithful completion, generation and whole Borel overlap are
retained, as is the independently owned strongly-three-embedded exclusion.
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

theorem source_cubic_atlas_core_lifts (d : Counterexample T L)
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
          p.leftEndpoint ⊓ p.rightEndpoint=t.leftCubicBorel ∧
          p.leftEndpoint ⊔ p.rightEndpoint=⊤ ∧
          Nonempty (RankTwoAmalgam.FaithfulCompletion p.amalgam (G:=G)) ∧
          (∀ (e : (D ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V),
            (∀ v w,t.cubicLineScalar (t.cubicCommutatorLine p.core_order v w)=
              Multiplicative.ofAdd (Atlas.G2.TernaryCore.shortForm (e v) (e w))) →
            ∃ f : D ≃* Atlas.G2.LieParabolicSetup.radical₁ (F:=ZMod 3),
              (∀ x,Atlas.G2.TernaryCore.shortQuotient (f x)=
                e (QuotientGroup.mk' (cubicCoreLine c t.x) x)) ∧
              f t.cubicLineGenerator=Atlas.G2.TernaryCore.short 1 1) ∧
          (∀ (e : (R ⧸ cubicCoreLine (swapFactors c) t.swap.x) ≃* Atlas.G2.TernaryCore.V),
            (∀ v w,t.swap.cubicLineScalar (t.swap.cubicCommutatorLine p.right_core_order v w)=
              Multiplicative.ofAdd (Atlas.G2.TernaryCore.longForm (e v) (e w))) →
            ∃ f : R ≃* Atlas.G2.LieParabolicSetup.radical₂ (F:=ZMod 3),
              (∀ x,Atlas.G2.TernaryCore.longQuotient (f x)=
                e (QuotientGroup.mk' (cubicCoreLine (swapFactors c) t.swap.x) x)) ∧
              f (t.swap.cubicLineGenerator : cubicOddCore (swapFactors c) t.swap.x)=Atlas.G2.TernaryCore.long 1 1))) := by
  obtain ⟨c,t,m,g,hm,hg,hgx,hgy,h⟩ := source_cubic_aligned_completion d earlier hq chosen
    structural alternatives F hne hZ hcard localData
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  rcases h with hsmall | ⟨hx,hy,p,_hB,hI,hgen,hcomp⟩
  · exact Or.inl hsmall
  · refine Or.inr ⟨hx,hy,p,hI,hgen,hcomp,?_,?_⟩
    · intro e hform
      exact ⟨t.cubicAtlasShortEquiv p.core_order e hform,
        t.cubicAtlasShortEquiv_quotient p.core_order e hform,
        t.cubicAtlasShortEquiv_generator p.core_order e hform⟩
    · intro e hform
      exact ⟨t.swap.cubicAtlasLongEquiv p.right_core_order e hform,
        t.swap.cubicAtlasLongEquiv_quotient p.right_core_order e hform,
        t.swap.cubicAtlasLongEquiv_generator p.right_core_order e hform⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
