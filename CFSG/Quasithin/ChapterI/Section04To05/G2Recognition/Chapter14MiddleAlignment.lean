module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Completion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalMiddleAlignment

/-!
# Whole-middle alignment in the original Chapter 14 application

In the original large-core branch, both full endpoint isomorphisms are
corrected by inner conjugations so that their restrictions identify the
whole order-2916 middle with the Atlas Borel and its original Klein four
with the split torus. Their explicit discrepancy preserves the whole
six-root subgroup and cannot exchange the two endpoint radicals.

The actual original group completes the corresponding faithful twist of
the exact Atlas amalgam, retaining the original endpoint involutions and
their orders two, two and six. Removing that discrepancy remains necessary
before applying the proved completion-recognition theorem. The original
strongly-three-embedded alternative and universal earlier-source premises
are retained; their final discharge is not asserted here.
Source: Aschbacher–Smith I.4.5, p.417, and 14.4.14, pp.1008–1010.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour Chapter14.Section04.DimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal source application constructs the corrected endpoint maps and
whole-middle discrepancy, with no extra identification premise. -/
theorem source_cubic_middle_alignment (d : Counterexample T L)
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
        ∃ (p : AlignedCubicPair t) (a : p.MiddleAlignment),
          Nat.card t.leftCubicBorel=2916 ∧
          p.leftEndpoint ⊓ p.rightEndpoint=t.leftCubicBorel ∧
          p.leftEndpoint ⊔ p.rightEndpoint=⊤ ∧
          Nonempty (RankTwoAmalgam.FaithfulCompletion
            (RankTwoAmalgam.twistRight (ChapterF.GreenBook.LieModels.G2.amalgam (F:=ZMod 3))
              a.atlasDifference) (G:=G)) ∧
          RankTwoAmalgam.Faithful
            (RankTwoAmalgam.twistRight (ChapterF.GreenBook.LieModels.G2.amalgam (F:=ZMod 3))
              a.atlasDifference) ∧
          (Atlas.G2.TernaryBorel.A.subgroupOf Atlas.G2.TernaryBorel.B).map
            a.difference.toMonoidHom=Atlas.G2.TernaryBorel.A.subgroupOf Atlas.G2.TernaryBorel.B ∧
          (Atlas.G2.TernaryBorel.U.subgroupOf Atlas.G2.TernaryBorel.B).map
            a.difference.toMonoidHom=Atlas.G2.TernaryBorel.U.subgroupOf Atlas.G2.TernaryBorel.B ∧
          (Atlas.G2.TernaryBorel.middleRadical false).map a.difference.toMonoidHom≠
            Atlas.G2.TernaryBorel.middleRadical true ∧
          p.leftReflection∈a.atlasTwistCompletion.left.range ∧
          p.rightReflection∈a.atlasTwistCompletion.right.range ∧
          p.leftReflection∉a.atlasTwistCompletion.middle.range ∧
          p.rightReflection∉a.atlasTwistCompletion.middle.range ∧
          orderOf p.leftReflection=2 ∧ orderOf p.rightReflection=2 ∧
          orderOf (p.leftReflection*p.rightReflection)=6)) := by
  obtain ⟨c,t,m,g,hm,hg,hgx,hgy,h⟩ := source_cubic_aligned_completion d earlier hq chosen
    structural alternatives F hne hZ hcard localData
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  rcases h with hsmall | ⟨hx,hy,p,hB,hI,hgen,_⟩
  · exact Or.inl hsmall
  · obtain ⟨a⟩ := p.nonempty_middleAlignment
    exact Or.inr ⟨hx,hy,p,a,hB,hI,hgen,⟨a.atlasTwistCompletion⟩,
      a.atlasTwist_faithful,a.difference_torus,a.difference_unipotent,a.difference_not_exchange,
      a.atlasTwistCompletion_involutions⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
