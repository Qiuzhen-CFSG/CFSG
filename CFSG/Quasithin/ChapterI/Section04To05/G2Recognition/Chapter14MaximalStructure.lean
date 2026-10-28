module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14MaximalBorels
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCoreStructure

/-!
# The original large-core structure at the Chapter14 consumer

The source-local configuration supplies both actual marked cubic cores.
In the large-core branch they are nonabelian of order243, with their
original cubic lines as derived subgroups and centers of order27. Their
normalizers are exactly the original cubic normalizers. Each local
order729 extension has an elementary center of order nine, whose full
ambient centralizer is that extension. Its normalizer is the normalizer
of this actual center plane. The fixed
plane of the original outer involution is conjugate to the original
H-plane, with the involution transported to the original central one.

These consequences discharge core-structure premises in the original
I.4.5 completion construction. The theorem retains the actual M-cubic
and the strongly-three-embedded alternative. Compatible Atlas endpoint
maps, endpoint generation and the involution product remain to be proved;
this is not recognition. Source: Aschbacher–Smith I.4(G1)–(G2), printed
p.417, applied to Theorem14.4.14, printed pp.1008–1010.
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

theorem source_cubic_maximal_core_structure (d : Counterexample T L)
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
        ¬IsMulCommutative D ∧ ¬IsMulCommutative R ∧
        ⁅D,D⁆=zpowers ((t.x:c.H):G) ∧ ⁅R,R⁆=zpowers ((t.y:c.H):G) ∧
        Nat.card (_root_.centerIn D)=27 ∧ Nat.card (_root_.centerIn R)=27 ∧
        normalizer (D:Set G)=cubicNormalizer c t.x ∧
        normalizer (R:Set G)=cubicNormalizer (swapFactors c) t.y ∧
        Nat.card t.leftCoreExtension=729 ∧ Nat.card t.swap.leftCoreExtension=729 ∧
        Nat.card (_root_.centerIn t.leftCoreExtension)=9 ∧
        Nat.card (_root_.centerIn t.swap.leftCoreExtension)=9 ∧
        IsElementaryAbelian 3 (_root_.centerIn t.leftCoreExtension) ∧
        IsElementaryAbelian 3 (_root_.centerIn t.swap.leftCoreExtension) ∧
        Subgroup.centralizer (_root_.centerIn t.leftCoreExtension:Set G)=t.leftCoreExtension ∧
        Subgroup.centralizer (_root_.centerIn t.swap.leftCoreExtension:Set G)=t.swap.leftCoreExtension ∧
        normalizer (t.leftCoreExtension:Set G)=normalizer (_root_.centerIn t.leftCoreExtension:Set G) ∧
        normalizer (t.swap.leftCoreExtension:Set G)=normalizer (_root_.centerIn t.swap.leftCoreExtension:Set G) ∧
        (∃ a : G, MulAut.conj a (t.n:G)=(t.z:G) ∧
          (D⊓Subgroup.centralizer ({(t.n:G)}:Set G)).map (MulAut.conj a).toMonoidHom=E) ∧
        (∃ b : G, MulAut.conj b (t.n:G)=(t.z:G) ∧
          (R⊓Subgroup.centralizer ({(t.n:G)}:Set G)).map (MulAut.conj b).toMonoidHom=E))) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  obtain ⟨m,g,hm,hg,hgx,hgy⟩ := exists_marked_M_diagonal c t.x t.y t.x_order t.y_order
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  by_cases hbig : 3^3∣Nat.card G
  · obtain ⟨hx,hy⟩ := t.paired_oddCore_maximal_of_cube_dvd hbig
    refine Or.inr ⟨hx,hy,t.maximal_core_not_commutative hx,t.swap.maximal_core_not_commutative hy,
      t.maximal_core_derived hx,t.swap.maximal_core_derived hy,
      t.maximal_core_center_card hx,t.swap.maximal_core_center_card hy,
      t.maximal_core_normalizer hx,t.swap.maximal_core_normalizer hy,
      t.maximal_leftCoreExtension_card hx,t.swap.maximal_leftCoreExtension_card hy,
      t.maximal_extension_center_card hx,t.swap.maximal_extension_center_card hy,
      t.maximal_extension_center_elementary hx,t.swap.maximal_extension_center_elementary hy,
      t.maximal_extension_center_centralizer hx,t.swap.maximal_extension_center_centralizer hy,
      t.maximal_extension_normalizer hx,t.swap.maximal_extension_normalizer hy,
      t.maximal_core_outer_fixed_conjugate hx,?_⟩
    simpa only [CubicTorus.swap,swapFactors,sup_comm] using
      t.swap.maximal_core_outer_fixed_conjugate hy
  · exact Or.inl (t.H_strongly_three_embedded_of_not_cube_dvd hbig)

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
