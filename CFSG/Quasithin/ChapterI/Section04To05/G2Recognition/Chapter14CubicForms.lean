module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Completion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCubicForms

/-!
# The original Chapter 14 application of simultaneous cubic/form coordinates

The large-core source branch now supplies a single quotient equivalence
preserving the actual commutator form and intertwining the chosen opposite
cubic. Its scalar map retains the original cubic generator; reversing the
escaping cubic when necessary fixes the sign. The original opposite derived
line has the literal Atlas coordinate. Reconstruction gives an actual core
isomorphism on these same coordinates, equivariant for the marked Levi cubic.

The entire order2916 middle and generating faithful completion remain in the
statement. Weyl compatibility and agreement on that whole middle still need
proof. The original strongly-three-embedded alternative and universal earlier
premises remain explicit; no guarded same-G,T instance is promoted to a
universal theorem. Final earlier-source discharge remains with assembly.
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

/-- The literal source application constructs simultaneous form/cubic coordinates
and their full core map, retaining the original middle and both source branches. -/
theorem source_cubic_form_coordinates (d : Counterexample T L)
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
              (∀ v w,t.cubicLineScalar (t.cubicCommutatorLine p.core_order v w)=
                Multiplicative.ofAdd (Atlas.G2.TernaryCore.shortForm (e v) (e w))) ∧
              (∀ v,v∈(⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore).map
                (QuotientGroup.mk' (cubicCoreLine c t.x)) ↔
                  (e v).toAdd 0=0 ∧ (e v).toAdd 2=0 ∧ (e v).toAdd 3=0) ∧
              ∃ core : p.leftCore ≃* Atlas.G2.LieParabolicSetup.radical₁ (F:=ZMod 3),
                (∀ x,Atlas.G2.TernaryCore.shortQuotient (core x)=
                  e (QuotientGroup.mk' (cubicCoreLine c t.x) x)) ∧
                core t.cubicLineGenerator=Atlas.G2.TernaryCore.short 1 1 ∧
                (∀ x,core (t.cubicGLCoreAction p.core_order
                  (κ.symm (Atlas.G2.TernaryLevi.generator false)) x)=
                    Atlas.G2.TernaryLevi.coreAction false
                      (Atlas.G2.TernaryLevi.generator false) (core x)))) := by
  obtain ⟨c,t,m,g,hm,hg,hgx,hgy,h⟩ := source_cubic_aligned_completion d earlier hq chosen
    structural alternatives F hne hZ hcard localData
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  rcases h with hsmall | ⟨hx,hy,p,hB,hI,hgen,hcomp⟩
  · exact Or.inl hsmall
  · obtain ⟨r₀,hr₀,_⟩ := p.exists_oppositeDisplacement_nonquadratic
    obtain ⟨r,κ,e,_,hr,hκ,he,hform,hline⟩ := p.exists_shortRoot_form_comparison r₀ hr₀
    refine Or.inr ⟨hx,hy,p,hB,hI,hgen,hcomp,p.aligned_common_core_elementary,
      r,hr,κ,e,hκ,he,hform,hline,t.cubicAtlasShortEquiv p.core_order e hform,
      t.cubicAtlasShortEquiv_quotient p.core_order e hform,
      t.cubicAtlasShortEquiv_generator p.core_order e hform,?_⟩
    intro x
    apply t.cubicAtlasShortEquiv_action p.core_order e hform
      (κ.symm (Atlas.G2.TernaryLevi.generator false))
      (Atlas.G2.TernaryLevi.endpointEmbedding false (Atlas.G2.TernaryLevi.generator false))
      (Atlas.G2.TernaryLevi.embedding_commutes false (Atlas.G2.TernaryLevi.generator false))
    intro v
    rw [t.cubicAbelianizationAction_factor p.core_order]
    have hb : t.cubicLinearAction p.core_order (inclusion t.cubicLevi_le_normalizer
      ((t.cubicLeviLinearEquiv p.core_order).symm
        (κ.symm (Atlas.G2.TernaryLevi.generator false))))=
          κ.symm (Atlas.G2.TernaryLevi.generator false) :=
      (t.cubicLeviLinearEquiv p.core_order).apply_symm_apply _
    rw [hb]
    exact he v

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
