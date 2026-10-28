module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14MaximalCore
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalPlaneNormalizer

/-!
# The exact plane normalizer at the original Chapter14 consumer

The literal SourceLocalData supplies the original G₂(3) configuration,
its cubic plane, and a conjugated cubic from the actual M outside both
factor lines. The large-core branch now has the full plane-normalizer
split, its exact order and three-core, and the marked involution's
centralizer in N(U) and in its faithful quotient by the self-centralizing U.

Every clause of strong three-embedding remains in the other branch.
The I.4.5 recognition and its actual Atlas equivalence remain unproved;
no additional local structure is assumed here. Source: Aschbacher–Smith
I.4.5, printed p.417, used in Theorem14.4.14. SourceLocalData production
and the final Chapter14 assembly retain their existing owners.
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

theorem source_cubic_maximal_plane_normalizer (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c) (m : c.M) (g : G),
      let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
      let U := E⊔(cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y)
      orderOf m=3 ∧ MulAut.conj g (m:G)∈E ∧
      MulAut.conj g (m:G)∉zpowers ((t.x:c.H):G) ∧
      MulAut.conj g (m:G)∉zpowers ((t.y:c.H):G) ∧
      ((c.H≠⊤ ∧ 3∣Nat.card c.H ∧
        ∀ a : G, a∉c.H →
          ¬3∣Nat.card (c.H ⊓ c.H.map (MulAut.conj a).toMonoidHom : Subgroup G)) ∨
      (Nat.card (cubicOddCore c t.x)=243 ∧
        Nat.card (cubicOddCore (swapFactors c) t.y)=243 ∧
        Nat.card U=81 ∧ IsElementaryAbelian 3 U ∧
        Subgroup.centralizer (U:Set G)=U ∧
        normalizer (E:Set G)=U⊔t.torus.map c.H.subtype ∧
        Disjoint U (t.torus.map c.H.subtype) ∧
        Nat.card (normalizer (E:Set G))=324 ∧
        (normalizer (E:Set G)).pCoreIn 3=U ∧
        normalizer (U:Set G)⊓c.H=E⊔t.torus.map c.H.subtype ∧
        Nat.card (normalizer (U:Set G)⊓Subgroup.centralizer ({(t.z:G)}:Set G):Subgroup G)=36 ∧
        ∃ z : normalizer (U:Set G), (z:G)=(t.z:G) ∧
          orderOf (NormalizerAction.quotient U z)=2 ∧
          Nonempty ((Subgroup.centralizer
            ({NormalizerAction.quotient U z}:Set (NormalizerAction.Star U))) ≃*
              t.torus.map c.H.subtype))) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  obtain ⟨m,g,hm,hg,hgx,hgy⟩ := exists_marked_M_diagonal c t.x t.y t.x_order t.y_order
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  by_cases hbig : 3^3∣Nat.card G
  · obtain ⟨hx,hy⟩ := t.paired_oddCore_maximal_of_cube_dvd hbig
    obtain ⟨hu,hUc,_⟩ := t.maximal_plane_elementary_extension hx
    obtain ⟨hN,hd⟩ := t.maximal_plane_normalizer_split hx
    exact Or.inr ⟨hx,hy,hUc,hu,t.maximal_plane_extension_selfCentralizing hx,hN,hd,
      t.maximal_plane_normalizer_card hx,t.maximal_plane_normalizer_threeCore hx,
      t.maximal_extension_normalizer_inf_H hx,
      t.maximal_extension_normalizer_involution_centralizer_card hx,
      t.maximal_extension_quotient_involution_centralizer hx⟩
  · exact Or.inl (t.H_strongly_three_embedded_of_not_cube_dvd hbig)

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
