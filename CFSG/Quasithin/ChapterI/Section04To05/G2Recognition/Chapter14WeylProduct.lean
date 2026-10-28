module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14SylowAlignment
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalWeylProduct

/-!
# The original Chapter 14 endpoint product has order six

The original large-core configuration supplies aligned cubic-normalizer
endpoints, their whole order2916 Borel intersection, and marked involutions
outside that intersection with orders two, two and product order six.
The proof uses the elementary torus centralizer and the opposite normal
SL₂(3) factor markings, not an assumed model realization.

This discharges the endpoint product-order hypothesis in the original
completion construction. Compatible Atlas endpoint maps, their commuting
squares and generation remain necessary. The original strongly-three-embedded
alternative is retained for its independent source exclusion.
Source: Aschbacher–Smith I.4.5, printed p.417, and 14.4.14, pp.1008–1010;
the order-six completion consumer is F.4.26, printed p.288.
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

/-- The literal source configuration supplies both endpoint involutions and
their order-six product, with the original torus, cores and whole Borel retained. -/
theorem source_cubic_maximal_weyl_product (d : Counterexample T L)
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
        ∃ a s r : G,
          a∈normalizer (t.torus.map c.H.subtype:Set G) ∧
          t.swap.leftCoreExtension.map (MulAut.conj a).toMonoidHom=t.leftCoreExtension ∧
          cubicNormalizer c t.x ⊓
            (cubicNormalizer (swapFactors c) t.y).map (MulAut.conj a).toMonoidHom=
              t.leftCubicBorel ∧
          Nat.card t.leftCubicBorel=2916 ∧
          s∈cubicNormalizer c t.x ∧
          r∈(cubicNormalizer (swapFactors c) t.y).map (MulAut.conj a).toMonoidHom ∧
          s∉t.leftCubicBorel ∧ r∉t.leftCubicBorel ∧
          orderOf s=2 ∧ orderOf r=2 ∧ orderOf (s*r)=6 ∧
          s∈normalizer (t.torus.map c.H.subtype:Set G) ∧
          r∈normalizer (t.torus.map c.H.subtype:Set G) ∧
          MulAut.conj s (t.z:G)=(t.z:G) ∧
          MulAut.conj s (t.n:G)=(t.z:G)*(t.n:G) ∧
          MulAut.conj r (MulAut.conj a (t.z:G))=MulAut.conj a (t.z:G) ∧
          MulAut.conj r (MulAut.conj a (t.n:G))=
            MulAut.conj a ((t.z:G)*(t.n:G)) ∧
          MulAut.conj a (t.z:G)≠(t.z:G))) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  obtain ⟨m,g,hm,hg,hgx,hgy⟩ := exists_marked_M_diagonal c t.x t.y t.x_order t.y_order
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  by_cases hbig : 3^3∣Nat.card G
  · obtain ⟨hx,hy⟩ := t.paired_oddCore_maximal_of_cube_dvd hbig
    obtain ⟨a,s,r,haA,ha,hover,hs,hr,hsB,hrB,hs2,hr2,hprod,hsA,hrA,hsz,hsn,hrz,hrn,haz⟩ :=
      t.maximal_aligned_endpoint_hexagon_involutions hx
    exact Or.inr ⟨hx,hy,a,s,r,haA,ha,hover,(t.maximal_leftCubicBorel_split hx).2.2.2,
      hs,hr,hsB,hrB,hs2,hr2,hprod,hsA,hrA,hsz,hsn,hrz,hrn,haz⟩
  · exact Or.inl (t.H_strongly_three_embedded_of_not_cube_dvd hbig)

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
