module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Completion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalWeylCoordinates

/-!
# Both full endpoint models in the original Chapter 14 application

In the large-core branch the actual original endpoints are now isomorphic
to the two Atlas parabolics. Both isomorphisms extend the constructed core
maps and intertwine the whole GL₂(3) actors, with the original right Sylow
aligner retained. This discharges the previously explicit full-action
comparison premises on one simultaneous cubic/form/Weyl coordinate system.

The original intersection of order2916 and endpoint generation remain in
the statement. Agreement of these maps on that whole middle and recognition
of the original completion still require proof. The strongly-three-embedded
alternative and all universal earlier-source inputs remain explicit; no
same-G,T instance is promoted to a universal theorem.
Source: Aschbacher–Smith I.4.5, p.417, and 14.4.14, pp.1008–1010.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour Chapter14.Section04.DimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The source large-core branch constructs both full Atlas endpoint maps.
The whole common middle is retained; its two restrictions still must be matched. -/
theorem source_cubic_endpoint_models (d : Counterexample T L)
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
          ∃ (l : t.ShortQuotientComparison p.core_order)
            (r : t.swap.LongQuotientComparison p.right_core_order)
            (e₁ : p.leftEndpoint ≃* Atlas.G2.LieParabolicSetup.parabolic₁ (F:=ZMod 3))
            (e₂ : p.rightEndpoint ≃* Atlas.G2.LieParabolicSetup.parabolic₂ (F:=ZMod 3)),
            (∀ x : p.leftCore,(e₁ (inclusion t.cubicCore_le_normalizer x):Atlas.G2.Model (ZMod 3))=
              t.cubicAtlasShortEquiv p.core_order l.coordinates l.form x) ∧
            (∀ x : cubicOddCore (swapFactors c) t.swap.x,
              (e₂ (p.rightEndpointEquiv (inclusion t.swap.cubicCore_le_normalizer x)):
                Atlas.G2.Model (ZMod 3))=
                t.swap.cubicAtlasLongEquiv p.right_core_order r.coordinates r.form x) ∧
            (∀ a : Atlas.G2.TernaryLevi.GL23,
              (e₁ (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv p.core_order).symm a)):
                Atlas.G2.Model (ZMod 3))=Atlas.G2.TernaryLevi.embedding false (l.actor a)) ∧
            (∀ a : Atlas.G2.TernaryLevi.GL23,
              (e₂ (p.rightEndpointEquiv (inclusion t.swap.cubicLevi_le_normalizer
                ((t.swap.cubicLeviLinearEquiv p.right_core_order).symm a))):
                Atlas.G2.Model (ZMod 3))=Atlas.G2.TernaryLevi.embedding true (r.actor a)))) := by
  obtain ⟨c,t,m,g,hm,hg,hgx,hgy,h⟩ := source_cubic_aligned_completion d earlier hq chosen
    structural alternatives F hne hZ hcard localData
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  rcases h with hsmall | ⟨hx,hy,p,hB,hI,hgen,hcomp⟩
  · exact Or.inl hsmall
  · obtain ⟨⟨l⟩,⟨r⟩⟩ := p.nonempty_endpoint_comparisons
    exact Or.inr ⟨hx,hy,p,hB,hI,hgen,hcomp,l,r,
      p.leftAtlasEndpointEquiv l,p.rightAtlasEndpointEquiv r,
      p.leftAtlasEndpointEquiv_core l,p.rightAtlasEndpointEquiv_core r,
      p.leftAtlasEndpointEquiv_actor l,p.rightAtlasEndpointEquiv_actor r⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
