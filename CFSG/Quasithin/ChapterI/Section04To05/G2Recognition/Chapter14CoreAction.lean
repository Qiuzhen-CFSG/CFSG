module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Completion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalAlignedSplit

/-!
# Full endpoint coordinates for the original Chapter 14 configuration

Apply the full-core semidirect products to the two original aligned cubic
normalizers. Both maps retain the whole original Borel as the preimage of
the corresponding linear Borel, and the original generating completion.
The four-dimensional core module has its literal equivariant central
projection and alternating commutator pairing, with radical the center plane.

This discharges the construction of full original endpoint coordinates,
without assuming an abstract core action. The Atlas action comparison and
both commuting squares still remain, as does the independently owned
strongly-three-embedded exclusion. The source local-data premise remains
with the Chapter14 assembly owner. Source: Aschbacher–Smith I.4.5, p.417,
and 14.4.14, pp.1008–1010.
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

/-- The literal large-core source branch has full marked endpoint coordinates,
with both whole-middle preimages and the original core commutator module. -/
theorem source_cubic_core_completion (d : Counterexample T L)
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
          (∀ v : p.leftSplitDomain,p.leftLinearAction (p.leftSplitEquiv v)=v.right) ∧
          (∀ v : p.rightSplitDomain,p.rightLinearAction (p.rightSplitEquiv v)=v.right) ∧
          (t.leftCubicBorel.subgroupOf p.leftEndpoint).comap p.leftSplitEquiv.toMonoidHom=
            (normalizer (((t.leftCoreExtension.subgroupOf p.leftEndpoint).map
              p.leftLinearAction):Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))).comap
                SemidirectProduct.rightHom ∧
          (t.leftCubicBorel.subgroupOf p.rightEndpoint).comap p.rightSplitEquiv.toMonoidHom=
            (normalizer (((t.leftCoreExtension.subgroupOf p.rightEndpoint).map
              p.rightLinearAction):Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))).comap
                SemidirectProduct.rightHom ∧
          Function.Injective (t.cubicGLFourRepresentation p.core_order) ∧
          Function.Injective (t.swap.cubicGLFourRepresentation p.right_core_order) ∧
          Nat.card t.cubicCenterPlane=9 ∧ Nat.card t.swap.cubicCenterPlane=9 ∧
          (∀ v, (∀ w,t.cubicCommutatorPairing v w=1) ↔ v∈t.cubicCenterPlane) ∧
          (∀ v, (∀ w,t.swap.cubicCommutatorPairing v w=1) ↔ v∈t.swap.cubicCenterPlane))) := by
  obtain ⟨c,t,m,g,hm,hg,hgx,hgy,h⟩ := source_cubic_aligned_completion d earlier hq chosen
    structural alternatives F hne hZ hcard localData
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  rcases h with hsmall | ⟨hx,hy,p,_hB,hI,hgen,hcomp⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨hx,hy,p,hI,hgen,hcomp,p.leftSplitEquiv_linear,p.rightSplitEquiv_linear,
      p.leftSplitEquiv_middle,p.rightSplitEquiv_middle,
      t.cubicGLFourRepresentation_injective p.core_order,
      t.swap.cubicGLFourRepresentation_injective p.right_core_order,
      t.cubicCenterPlane_card p.core_order,t.swap.cubicCenterPlane_card p.right_core_order,
      t.cubicCommutatorPairing_radical,t.swap.cubicCommutatorPairing_radical⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
