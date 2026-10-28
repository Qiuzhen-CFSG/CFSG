module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14PairedCoreExclusion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.SylowNineLocal

/-!
# The Sylow-nine source branch at Chapter14

The literal SourceLocalData gives either two marked odd cores of order243,
or strong three-embedding of the original involution centralizer H. In the
latter branch the actual M-cubic, conjugated into the original plane, has
centralizer equal to that plane times the original central involution.
Its full line normalizer lies in H.

This discharges the diagonal-centralizer and strong-three-embedding
reductions in the exceptional q=3 recognition argument. It does not exclude
that branch or discharge the recognize callback. Source: Aschbacher–Smith
I.4.5, printed p.417, used in Theorem14.4.14. The SourceLocalData producer
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

theorem source_cubic_sylow_nine_local (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c) (m : c.M) (g : G),
      let E : Subgroup G := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
      let u : G := MulAut.conj g (m:G)
      orderOf m=3 ∧ u∈E ∧
      ((3^6∣Nat.card G ∧ Nat.card (cubicOddCore c t.x)=243 ∧
          Nat.card (cubicOddCore (swapFactors c) t.y)=243) ∨
        (c.H≠⊤ ∧ 3∣Nat.card c.H ∧
          (∀ a : G, a∉c.H →
            ¬3∣Nat.card (c.H ⊓ c.H.map (MulAut.conj a).toMonoidHom : Subgroup G)) ∧
          Subgroup.centralizer ({u}:Set G)=E ⊔ zpowers (t.z:G) ∧
          Nat.card (Subgroup.centralizer ({u}:Set G))=18 ∧
          normalizer (zpowers u:Set G)≤c.H)) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  obtain ⟨m,g,hm,hu,hux,huy⟩ := exists_marked_M_diagonal c t.x t.y t.x_order t.y_order
  refine ⟨c,t,m,g,hm,hu,?_⟩
  by_cases hbig : 3^3∣Nat.card G
  · obtain ⟨hx,hy⟩ := t.paired_oddCore_maximal_of_cube_dvd hbig
    exact Or.inl ⟨cubic_maximal_core_sixth_power_dvd c t.x t.x_order hx,hx,hy⟩
  · have hS := t.cubic_plane_sylow_iff.mpr (t.small_cores_iff_not_cube_dvd.mpr hbig)
    have hstrong := t.H_strongly_three_embedded_of_not_cube_dvd hbig
    have hu3 : orderOf (MulAut.conj g (m:G))=3 :=
      ((MulAut.conj g).orderOf_eq (m:G)).trans ((orderOf_coe m).trans hm)
    exact Or.inr ⟨hstrong.1,hstrong.2.1,hstrong.2.2,
      t.diagonal_centralizer_of_sylow hS _ hu3 hu hux huy,
      t.diagonal_centralizer_card_of_sylow hS _ hu3 hu hux huy,
      t.plane_cubic_normalizer_le_H_of_sylow hS _ hu3 hu⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
