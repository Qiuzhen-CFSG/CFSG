module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14CoreAction
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCoreReconstruction

/-!
# Canonical full-core reconstruction in the literal Chapter 14 branch

Apply the inverted sections and their multiplication and equivariance laws
on both sides of the original aligned completion. The section correction
is the original commutator form, so no independently chosen central cocycle
is required. The whole-middle overlap, generation, and original completion
remain those already constructed from SourceLocalData.

The remaining Atlas quotient comparisons must preserve these forms and
agree on the whole middle. The independently owned strongly-three-embedded
exclusion is still explicit. This is an application of the reconstruction
calculation, not a claim of completed I.4.5 recognition.
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

/-- Both original cores have their canonical full multiplication and GL₂(3)
actions, preserving the original faithful completion and all its markings. -/
theorem source_cubic_reconstructed_completion (d : Counterexample T L)
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
          (∀ v w,t.cubicInvertedSection (v*w)=t.cubicInvertedSection v*t.cubicInvertedSection w*
            (t.cubicCommutatorPairing v w:D)) ∧
          (∀ v w,t.swap.cubicInvertedSection (v*w)=
            t.swap.cubicInvertedSection v*t.swap.cubicInvertedSection w*
              (t.swap.cubicCommutatorPairing v w:cubicOddCore (swapFactors c) t.swap.x)) ∧
          (∀ a v,t.cubicGLCoreAction p.core_order a (t.cubicInvertedSection v)=
            t.cubicInvertedSection (t.cubicAbelianizationAction
              (inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv p.core_order).symm a)) v)) ∧
          (∀ a v,t.swap.cubicGLCoreAction p.right_core_order a (t.swap.cubicInvertedSection v)=
            t.swap.cubicInvertedSection (t.swap.cubicAbelianizationAction
              (inclusion t.swap.cubicLevi_le_normalizer
                ((t.swap.cubicLeviLinearEquiv p.right_core_order).symm a)) v)))) := by
  obtain ⟨c,t,m,g,hm,hg,hgx,hgy,h⟩ := source_cubic_aligned_completion d earlier hq chosen
    structural alternatives F hne hZ hcard localData
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  rcases h with hsmall | ⟨hx,hy,p,_hB,hI,hgen,hcomp⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨hx,hy,p,hI,hgen,hcomp,t.cubicInvertedSection_mul,
      t.swap.cubicInvertedSection_mul,t.cubicGLCoreAction_section p.core_order,
      t.swap.cubicGLCoreAction_section p.right_core_order⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
