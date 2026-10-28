module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Completion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.AtlasFormCoordinates

/-!
# Actual Atlas core models in the literal Chapter 14 source branch

Apply the constructed form coordinates and cubic reconstruction to the two
original marked cores. The resulting isomorphisms have the actual aligned
cores as domains and the literal Atlas short and long radicals as targets.
Their cubic markings, quotient squares and distinguished involutions are
proved, with no assumed form comparison. The original endpoint generation,
whole Borel overlap and faithful completion are retained.

The maps here identify cores. Compatible full endpoint maps on the whole
middle, and exclusion of the original strongly-three-embedded alternative,
are still required for source I.4.5. Source: Aschbacher–Smith, printed p.417,
and the dimension-four application in 14.4.14, pp.1008–1010.
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

/-- The literal source branch now has actual Atlas core models, with no assumed
quotient-form comparison, while retaining the original faithful completion. -/
theorem source_cubic_atlas_core_models (d : Counterexample T L)
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
          ∃ (f : p.leftCore ≃* Atlas.G2.LieParabolicSetup.radical₁ (F:=ZMod 3))
            (j : p.rightCore ≃* Atlas.G2.LieParabolicSetup.radical₂ (F:=ZMod 3)),
            f t.cubicLineGenerator=Atlas.G2.TernaryCore.short 1 1 ∧
            j (p.rightCoreTransport t.swap.cubicLineGenerator)=Atlas.G2.TernaryCore.long 1 1 ∧
            (∀ x,Atlas.G2.TernaryCore.shortQuotient (f x)=
              t.cubicAtlasShortCoordinates p.core_order
                (QuotientGroup.mk' (cubicCoreLine c t.x) x)) ∧
            (∀ x,Atlas.G2.TernaryCore.longQuotient (j x)=
              t.swap.cubicAtlasLongCoordinates p.right_core_order
                (QuotientGroup.mk' (cubicCoreLine (swapFactors c) t.swap.x)
                  (p.rightCoreTransport.symm x))) ∧
            (∀ x,f (t.cubicInvolutionExtension.involution x)=
              Atlas.G2.TernaryCore.shortInvolution (f x)) ∧
            (∀ x,j (p.rightCoreTransport (t.swap.cubicInvolutionExtension.involution x))=
              Atlas.G2.TernaryCore.longInvolution (j (p.rightCoreTransport x))))) := by
  obtain ⟨c,t,m,g,hm,hg,hgx,hgy,h⟩ := source_cubic_aligned_completion d earlier hq chosen
    structural alternatives F hne hZ hcard localData
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  rcases h with hsmall | ⟨hx,hy,p,_hB,hI,hgen,hcomp⟩
  · exact Or.inl hsmall
  · refine Or.inr ⟨hx,hy,p,hI,hgen,hcomp,p.leftAtlasCoreModel,p.rightAtlasCoreModel,
      p.leftAtlasCoreModel_generator,p.rightAtlasCoreModel_generator,
      p.leftAtlasCoreModel_quotient,p.rightAtlasCoreModel_quotient,
      t.cubicAtlasShortModel_involution p.core_order,?_⟩
    intro x
    rw [p.rightAtlasCoreModel_transport,p.rightAtlasCoreModel_transport,
      t.swap.cubicAtlasLongModel_involution]

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
