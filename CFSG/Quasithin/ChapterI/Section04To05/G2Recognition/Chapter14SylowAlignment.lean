module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14MaximalStructure
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalAmbientSylow

/-!
# Original Sylow alignment and whole endpoint overlap at Chapter14

Apply the original local constructor to the literal source configuration,
retaining the selected M-cubic and both marked cores. In the large-core
branch, the two order729 extensions are ambient Sylow subgroups and can
be conjugated onto each other. Their entire normalizers are the actual
order2916 Borels. The resulting cubic-normalizer endpoints have this
whole Borel as their intersection. Their original derived lines span the
common Sylow center, and their cores generate the Sylow and intersect in
order81.

This discharges the ambient placement and whole-overlap requirements of
the original I.4.5 construction. Both Atlas commuting squares, compatible
endpoint maps, generation and the order-six involution product still need
proofs. The genuine strongly-three-embedded alternative is retained.
Source: Aschbacher–Smith I.4.5, printed p.417, and 14.4.14, pp.1008–1010.
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

theorem source_cubic_maximal_sylow_alignment (d : Counterexample T L)
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
        ∃ (P Q : Sylow 3 G) (a : G),
          (P:Subgroup G)=t.leftCoreExtension ∧
          (Q:Subgroup G)=t.swap.leftCoreExtension ∧
          t.swap.leftCoreExtension.map (MulAut.conj a).toMonoidHom=t.leftCoreExtension ∧
          normalizer (t.leftCoreExtension:Set G)=t.leftCubicBorel ∧
          normalizer (t.swap.leftCoreExtension:Set G)=t.swap.leftCubicBorel ∧
          Nat.card t.leftCubicBorel=2916 ∧
          t.swap.leftCubicBorel.map (MulAut.conj a).toMonoidHom=t.leftCubicBorel ∧
          cubicNormalizer c t.x ⊓
            (cubicNormalizer (swapFactors c) t.y).map (MulAut.conj a).toMonoidHom=t.leftCubicBorel ∧
          zpowers ((t.x:c.H):G) ⊔
            (zpowers ((t.y:c.H):G)).map (MulAut.conj a).toMonoidHom=
              _root_.centerIn t.leftCoreExtension ∧
          D ⊔ R.map (MulAut.conj a).toMonoidHom=t.leftCoreExtension ∧
          Nat.card (D⊓R.map (MulAut.conj a).toMonoidHom:Subgroup G)=81 ∧
          ⁅D,D⁆=zpowers ((t.x:c.H):G) ∧
          ⁅R.map (MulAut.conj a).toMonoidHom,R.map (MulAut.conj a).toMonoidHom⁆=
            (zpowers ((t.y:c.H):G)).map (MulAut.conj a).toMonoidHom)) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  obtain ⟨m,g,hm,hg,hgx,hgy⟩ := exists_marked_M_diagonal c t.x t.y t.x_order t.y_order
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  by_cases hbig : 3^3∣Nat.card G
  · obtain ⟨hx,hy⟩ := t.paired_oddCore_maximal_of_cube_dvd hbig
    obtain ⟨P,hP⟩ := t.maximal_extension_sylow hx
    obtain ⟨Q,hQ⟩ := t.swap.maximal_extension_sylow hy
    obtain ⟨a,ha⟩ := t.maximal_extensions_conjugate hx
    obtain ⟨hjoin,hint,hderived⟩ := t.maximal_aligned_core_pair hx a ha
    exact Or.inr ⟨hx,hy,P,Q,a,hP,hQ,ha,
      t.maximal_sylow_normalizer_eq hx,t.swap.maximal_sylow_normalizer_eq hy,
      (t.maximal_leftCubicBorel_split hx).2.2.2,t.maximal_aligned_borels hx a ha,
      t.maximal_aligned_endpoint_overlap hx a ha,t.maximal_aligned_center_lines hx a ha,
      hjoin,hint,t.maximal_core_derived hx,hderived⟩
  · exact Or.inl (t.H_strongly_three_embedded_of_not_cube_dvd hbig)

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
