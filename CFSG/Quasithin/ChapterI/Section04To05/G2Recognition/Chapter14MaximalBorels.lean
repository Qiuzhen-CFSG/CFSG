module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14MaximalNormalizer
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCubicBorels

/-!
# Original cubic Borels at the Chapter14 consumer

The original SourceLocalData constructs the G₂(3) configuration and the
marked M-cubic in its plane. In the large-core branch, each original cubic
normalizer now has its actual order729 local Sylow, an index-four Borel
normalizing it, and a quotient by its marked three-core identified with the
original order48 actor. Both endpoint markings and their whole intersection
are retained. The two unaligned normalizers cannot themselves be the ranges
of a completion of the exact Atlas amalgam, whose middle is larger.

This supplies local structure needed by the original I.4.5 construction,
used in Theorem14.4.14. It does not assert compatible adjacent endpoints or
recognition. The strongly-three-embedded branch and final equivalence retain
their original owners. Source: Aschbacher–Smith, printed pp.417 and 1008–1010.
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

theorem source_cubic_maximal_borels (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c) (m : c.M) (g : G),
      let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
      orderOf m=3 ∧ MulAut.conj g (m:G)∈E ∧
      MulAut.conj g (m:G)∉zpowers ((t.x:c.H):G) ∧
      MulAut.conj g (m:G)∉zpowers ((t.y:c.H):G) ∧
      ((c.H≠⊤ ∧ 3∣Nat.card c.H ∧
        ∀ a : G, a∉c.H →
          ¬3∣Nat.card (c.H ⊓ c.H.map (MulAut.conj a).toMonoidHom : Subgroup G)) ∨
      (Nat.card (cubicOddCore c t.x)=243 ∧
        Nat.card (cubicOddCore (swapFactors c) t.y)=243 ∧
        Nat.card t.leftCoreExtension=729 ∧ Nat.card t.swap.leftCoreExtension=729 ∧
        Nat.card t.leftCubicBorel=2916 ∧ Nat.card t.swap.leftCubicBorel=2916 ∧
        t.leftCubicBorel.relIndex (cubicNormalizer c t.x)=4 ∧
        t.swap.leftCubicBorel.relIndex (cubicNormalizer (swapFactors c) t.y)=4 ∧
        (cubicNormalizer c t.x).pCoreIn 3=cubicOddCore c t.x ∧
        (cubicNormalizer (swapFactors c) t.y).pCoreIn 3=cubicOddCore (swapFactors c) t.y ∧
        t.leftCubicBorel.pCoreIn 3=t.leftCoreExtension ∧
        t.swap.leftCubicBorel.pCoreIn 3=t.swap.leftCoreExtension ∧
        cubicNormalizer c t.x ⊓ normalizer (t.leftCoreExtension:Set G)=t.leftCubicBorel ∧
        cubicNormalizer (swapFactors c) t.y ⊓ normalizer (t.swap.leftCoreExtension:Set G)=
          t.swap.leftCubicBorel ∧
        cubicNormalizer c t.x ⊓ cubicNormalizer (swapFactors c) t.y=normalizer (E:Set G) ∧
        t.leftCubicBorel ⊓ t.swap.leftCubicBorel=normalizer (E:Set G) ∧
        (∃ P : Sylow 3 (cubicNormalizer c t.x),
          (P:Subgroup (cubicNormalizer c t.x)).map (cubicNormalizer c t.x).subtype=
            t.leftCoreExtension) ∧
        (∃ P : Sylow 3 (cubicNormalizer (swapFactors c) t.y),
          (P:Subgroup (cubicNormalizer (swapFactors c) t.y)).map
            (cubicNormalizer (swapFactors c) t.y).subtype=t.swap.leftCoreExtension) ∧
        (letI := t.left_core_normal_in_cubic_normalizer;
          Nonempty ((cubicNormalizer c t.x ⧸
            (cubicOddCore c t.x).subgroupOf (cubicNormalizer c t.x)) ≃* t.leftCubicLevi)) ∧
        (letI : ((cubicOddCore (swapFactors c) t.y).subgroupOf
            (cubicNormalizer (swapFactors c) t.y)).Normal :=
            t.swap.left_core_normal_in_cubic_normalizer;
          Nonempty ((cubicNormalizer (swapFactors c) t.y ⧸
            (cubicOddCore (swapFactors c) t.y).subgroupOf
              (cubicNormalizer (swapFactors c) t.y)) ≃* t.swap.leftCubicLevi)) ∧
        ¬ ∃ a : TernaryCompletion.Completion G,
          a.left.range=cubicNormalizer c t.x ∧
          a.right.range=cubicNormalizer (swapFactors c) t.y)) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  obtain ⟨m,g,hm,hg,hgx,hgy⟩ := exists_marked_M_diagonal c t.x t.y t.x_order t.y_order
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  by_cases hbig : 3^3∣Nat.card G
  · obtain ⟨hx,hy⟩ := t.paired_oddCore_maximal_of_cube_dvd hbig
    exact Or.inr ⟨hx,hy,
      t.maximal_leftCoreExtension_card hx,t.swap.maximal_leftCoreExtension_card hy,
      (t.maximal_leftCubicBorel_split hx).2.2.2,(t.swap.maximal_leftCubicBorel_split hy).2.2.2,
      t.maximal_leftCubicBorel_index hx,t.swap.maximal_leftCubicBorel_index hy,
      t.maximal_cubic_normalizer_threeCore hx,t.swap.maximal_cubic_normalizer_threeCore hy,
      t.maximal_leftCubicBorel_threeCore hx,t.swap.maximal_leftCubicBorel_threeCore hy,
      t.maximal_leftCoreExtension_normalizer hx,t.swap.maximal_leftCoreExtension_normalizer hy,
      t.maximal_cubic_normalizers_intersection hx,t.maximal_cubic_borels_intersection hx,
      t.maximal_leftCoreExtension_local_sylow hx,t.swap.maximal_leftCoreExtension_local_sylow hy,
      t.maximal_left_cubic_quotient hx,t.swap.maximal_left_cubic_quotient hy,
      t.maximal_original_pair_not_completion hx⟩
  · exact Or.inl (t.H_strongly_three_embedded_of_not_cube_dvd hbig)

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
