module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Completion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalMiddleRigidity

/-!
# The original Chapter 14 discrepancy on the entire middle

The literal source construction now fixes both Atlas radicals individually
and its split torus pointwise. A single two-parameter central-shift formula gives
both middle restrictions on every original middle element. The same
faithful twisted completion and original endpoint involutions are retained.
Endpoint extension of the remaining shifts and the independent strongly-
three-embedded exclusion are not asserted. The universal earlier-source
premises are retained without inferring them from same-group instances.
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

/-- The original whole-middle maps have explicit simultaneous coordinates,
with both radical invariance and pointwise torus fixation proved. -/
theorem source_cubic_middle_coordinates (d : Counterexample T L)
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
          (∀ side,(Atlas.G2.TernaryBorel.middleRadical side).map a.difference.toMonoidHom=
            Atlas.G2.TernaryBorel.middleRadical side) ∧
          (∀ x∈Atlas.G2.TernaryBorel.A.subgroupOf Atlas.G2.TernaryBorel.B,a.difference x=x) ∧
          (∃ (j k : ZMod 3),
            ∀ b : t.leftCubicBorel,
              ∃ (v : Fin 6 → ZMod 3) (l m : (ZMod 3)ˣ),
                a.leftMiddle b=Atlas.G2.TernaryBorel.positive v*Atlas.G2.TernaryBorel.diagonal l m ∧
                a.rightMiddle b=
                  Atlas.G2.TernaryBorel.positive (Atlas.G2.TernaryBorel.twistCoordinates 1 1 j k v)*
                    Atlas.G2.TernaryBorel.diagonal l m) ∧
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
    obtain ⟨a,j,k,_,_,_,hcoords⟩ := a.exists_normalized_restrictions
    exact Or.inr ⟨hx,hy,p,a,hB,hI,hgen,⟨a.atlasTwistCompletion⟩,
      a.atlasTwist_faithful,a.difference_torus,a.difference_unipotent,a.difference_not_exchange,
      a.difference_radicals,a.difference_torus_pointwise,⟨j,k,hcoords⟩,
      a.atlasTwistCompletion_involutions⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
