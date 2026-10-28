module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14SylowNine
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCoreIntersection

/-!
# The order-243-core plane at the original Chapter14 consumer

The literal SourceLocalData produces the original marked configuration.
In its large-core branch the common intersection is elementary of order9,
and adjoining it to the original cubic plane gives a self-centralizing
elementary81. This is the actual three-core of the full plane centralizer,
which has order162 and splits over the marked central involution.

The other branch retains every clause of strong three-embedding of H.
No recognition conclusion is assumed or claimed. Source: Aschbacher–Smith
I.4.5, printed p.417, used in Theorem14.4.14. SourceLocalData production
and final Chapter14 assembly retain their existing owners.
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

theorem source_cubic_maximal_core_plane (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c),
      let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
      let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
      let U := E⊔K
      (c.H≠⊤ ∧ 3∣Nat.card c.H ∧
        ∀ g : G, g∉c.H →
          ¬3∣Nat.card (c.H ⊓ c.H.map (MulAut.conj g).toMonoidHom : Subgroup G)) ∨
      (Nat.card (cubicOddCore c t.x)=243 ∧
        Nat.card (cubicOddCore (swapFactors c) t.y)=243 ∧
        Nat.card K=9 ∧ IsElementaryAbelian 3 K ∧
        Nat.card U=81 ∧ IsElementaryAbelian 3 U ∧
        Subgroup.centralizer (E:Set G)=U⊔zpowers (t.z:G) ∧
        Nat.card (Subgroup.centralizer (E:Set G))=162 ∧
        (Subgroup.centralizer (E:Set G)).pCoreIn 3=U ∧
        Subgroup.centralizer (U:Set G)=U) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  refine ⟨c,t,?_⟩
  by_cases hbig : 3^3∣Nat.card G
  · obtain ⟨hx,hy⟩ := t.paired_oddCore_maximal_of_cube_dvd hbig
    obtain ⟨hu,hUc,hC⟩ := t.maximal_plane_elementary_extension hx
    exact Or.inr ⟨hx,hy,t.maximal_core_intersection_card hx,
      t.maximal_core_intersection_elementary hx,hUc,hu,hC,
      t.maximal_plane_centralizer_card hx,t.maximal_plane_threeCore hx,
      t.maximal_plane_extension_selfCentralizing hx⟩
  · exact Or.inl (t.H_strongly_three_embedded_of_not_cube_dvd hbig)

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
