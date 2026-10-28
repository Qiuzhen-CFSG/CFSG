module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Completion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCoreNonquadratic

/-!
# The original nonquadratic action in the Chapter 14 branch

The literal aligned completion now supplies an elementary common core and an
actual opposite-core actor with nonzero second displacement on the first core's
abelianization. The second image is its original opposite derived line and the
third displacement vanishes. No quotient-action comparison is an input.

The strongly-three-embedded alternative and the existing universal Chapter12/13
conditional inputs remain explicit. This does not infer those universal inputs
from guarded same-G,T hypotheses. Their earlier-source discharge and the compatible
Atlas endpoint maps remain necessary for I.4.5 and the original 14.4.14 application.
Source: Aschbacher–Smith, printed pp.417 and 1008–1010.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour Chapter14.Section04.DimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Original source application of the proved nonquadratic cubic action and its marked image. -/
theorem source_cubic_nonquadratic_action (d : Counterexample T L)
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
          IsElementaryAbelian 3 (p.leftCore⊓p.rightCore:Subgroup G) ∧
          ∃ r : p.rightCore, (r:G)∉p.leftCore ∧
            (p.oppositeDisplacement r).comp (p.oppositeDisplacement r)≠1 ∧
            (∀ v, p.oppositeDisplacement r
              (p.oppositeDisplacement r (p.oppositeDisplacement r v))=1) ∧
            ((p.oppositeDisplacement r).comp (p.oppositeDisplacement r)).range=
              (⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore).map
                (QuotientGroup.mk' (cubicCoreLine c t.x)))) := by
  obtain ⟨c,t,m,g,hm,hg,hgx,hgy,h⟩ := source_cubic_aligned_completion d earlier hq chosen
    structural alternatives F hne hZ hcard localData
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  rcases h with hsmall | ⟨hx,hy,p,hB,hI,hgen,hcomp⟩
  · exact Or.inl hsmall
  · obtain ⟨r,hr,hnq⟩ := p.exists_oppositeDisplacement_nonquadratic
    exact Or.inr ⟨hx,hy,p,hB,hI,hgen,hcomp,p.aligned_common_core_elementary,
      r,hr,hnq,p.oppositeDisplacement_cube r,p.oppositeDisplacement_square_range r hr⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
