module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Completion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.AtlasEndpointActions

/-!
# Full endpoint comparison in the literal Chapter 14 branch

Apply the constructed Atlas actor embeddings and semidirect decompositions
to the original aligned completion. Once the two form-preserving quotient-action
comparisons, allowing actor basis changes, are supplied, the resulting actual endpoint maps extend both
core reconstructions for the supplied quotient coordinates and retain both entire GL₂(3) actors and the Sylow aligner.

The action equalities, whole-middle compatibility and independent exclusion
of the strongly-three-embedded alternative remain undischarged. The earlier
Chapter12/13 premises here are the existing universal conditional interfaces;
this does not infer them from guarded same-G,T hypotheses. Their separate
source discharge remains necessary. Source: Aschbacher–Smith I.4.5, p.417,
and the original 14.4.14 application, pp.1008–1010.
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

/-- Literal source application of the two constructed full model actors. The remaining
quotient-action comparison inputs are explicit, and the whole-middle square is not asserted. -/
theorem source_cubic_atlas_endpoint_actions (d : Counterexample T L)
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
          (∀ (l : t.ShortQuotientComparison p.core_order)
            (r : t.swap.LongQuotientComparison p.right_core_order),
            ∃ (f : p.leftEndpoint ≃* Atlas.G2.LieParabolicSetup.parabolic₁ (F:=ZMod 3))
              (j : p.rightEndpoint ≃* Atlas.G2.LieParabolicSetup.parabolic₂ (F:=ZMod 3)),
              (∀ x : p.leftCore,
                (f (inclusion t.cubicCore_le_normalizer x):Atlas.G2.Model (ZMod 3))=t.cubicAtlasShortEquiv p.core_order l.coordinates l.form x) ∧
              (∀ x : cubicOddCore (swapFactors c) t.swap.x,
                (j (p.rightEndpointEquiv (inclusion t.swap.cubicCore_le_normalizer x)):
                  Atlas.G2.Model (ZMod 3))=t.swap.cubicAtlasLongEquiv p.right_core_order r.coordinates r.form x) ∧
              (∀ a : Atlas.G2.TernaryLevi.GL23,
                (f (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv p.core_order).symm a)):
                  Atlas.G2.Model (ZMod 3))=Atlas.G2.TernaryLevi.embedding false (l.actor a)) ∧
              (∀ a : Atlas.G2.TernaryLevi.GL23,
                (j (p.rightEndpointEquiv (inclusion t.swap.cubicLevi_le_normalizer
                  ((t.swap.cubicLeviLinearEquiv p.right_core_order).symm a))):
                    Atlas.G2.Model (ZMod 3))=Atlas.G2.TernaryLevi.embedding true (r.actor a))))) := by
  obtain ⟨c,t,m,g,hm,hg,hgx,hgy,h⟩ := source_cubic_aligned_completion d earlier hq chosen
    structural alternatives F hne hZ hcard localData
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  rcases h with hsmall | ⟨hx,hy,p,hB,hI,hgen,hcomp⟩
  · exact Or.inl hsmall
  · refine Or.inr ⟨hx,hy,p,hB,hI,hgen,hcomp,?_⟩
    intro hl hr
    exact ⟨p.leftAtlasEndpointEquiv hl,p.rightAtlasEndpointEquiv hr,
      p.leftAtlasEndpointEquiv_core hl,p.rightAtlasEndpointEquiv_core hr,
      p.leftAtlasEndpointEquiv_actor hl,p.rightAtlasEndpointEquiv_actor hr⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
