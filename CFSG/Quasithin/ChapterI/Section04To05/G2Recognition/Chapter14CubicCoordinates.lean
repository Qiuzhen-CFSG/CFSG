module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Completion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCubicCoordinates

/-!
# Constructed cubic coordinates in the original Chapter 14 application

The original aligned completion supplies an escaping opposite-core cubic.
Its full action on the four-dimensional abelianization is now identified
with the literal Atlas short-root generator. An inner GL₂ marking retains
that actual actor, and the original opposite derived line goes to the
second coordinate line. No cubic-action comparison is an input.

These are coordinates for one generator. Form preservation and the Weyl
generator equation must still be proved on compatible coordinates, followed
by agreement of both endpoint maps on the whole common middle. The original
strongly-three-embedded alternative and universal earlier-source premises
remain explicit; no inference from guarded same-G,T hypotheses to universal
ones is made here. Final earlier-source discharge remains with the assembly.

Source: Aschbacher–Smith I.4.5, printed p.417, and 14.4.14, pp.1008–1010.
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

/-- The literal source application of the constructed first-generator comparison,
retaining the actual actor, opposite line, whole middle and generating completion. -/
theorem source_cubic_root_coordinates (d : Counterexample T L)
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
            ∃ (κ : Atlas.G2.TernaryLevi.GL23 ≃* Atlas.G2.TernaryLevi.GL23)
              (e : (p.leftCore ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V),
              t.cubicGLAbelianizationAction p.core_order
                (κ.symm (Atlas.G2.TernaryLevi.generator false))=p.oppositeAbelianizationActor r ∧
              (∀ v,e (t.cubicGLAbelianizationAction p.core_order
                (κ.symm (Atlas.G2.TernaryLevi.generator false)) v)=
                  Atlas.G2.TernaryLevi.shortQuotientAction
                    (Atlas.G2.TernaryLevi.generator false) (e v)) ∧
              (∀ v,v∈(⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore).map
                (QuotientGroup.mk' (cubicCoreLine c t.x)) ↔
                  (e v).toAdd 0=0 ∧ (e v).toAdd 2=0 ∧ (e v).toAdd 3=0))) := by
  obtain ⟨c,t,m,g,hm,hg,hgx,hgy,h⟩ := source_cubic_aligned_completion d earlier hq chosen
    structural alternatives F hne hZ hcard localData
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  rcases h with hsmall | ⟨hx,hy,p,hB,hI,hgen,hcomp⟩
  · exact Or.inl hsmall
  · obtain ⟨r,hr,_⟩ := p.exists_oppositeDisplacement_nonquadratic
    exact Or.inr ⟨hx,hy,p,hB,hI,hgen,hcomp,p.aligned_common_core_elementary,
      r,hr,p.exists_shortRoot_comparison r hr⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
