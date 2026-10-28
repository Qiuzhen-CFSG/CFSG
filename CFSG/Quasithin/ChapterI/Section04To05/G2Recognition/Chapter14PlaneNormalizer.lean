module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14MarkedCubic
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.PlaneNormalizer

/-!
# Marked cubic plane normalizers in dimension four

For the configuration constructed from the original SourceLocalData,
the full normalizer of the common cubic plane fixes an original factor
line. The plane is Sylow exactly when that normalizer lies in H; this
is also equivalent to both original cubic odd cores having order three.
In that branch ambient fusion of plane elements is realized inside H.

This applies the marked-M fusion restriction of `PlaneNormalizer` to
Aschbacher–Smith I.4(G1)–(G2), printed p.417, retaining the actual factors,
plane and conjugating elements. The exceptional q=3 exclusions and the
recognition equivalence are still owned by `qt-i45-g2-recognition`.
`qt-d-14414-g2-source` produces SourceLocalData and owns its final discharge.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour Chapter14.Section04.DimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_cubic_plane_normalizer (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c),
      let E : Subgroup G := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
      (normalizer (E:Set G) ≤ cubicNormalizer c t.x ∨
        normalizer (E:Set G) ≤ cubicNormalizer (swapFactors c) t.y) ∧
      (normalizer (E:Set G) ≤ c.H ↔
        Nat.card (cubicOddCore c t.x)=3 ∧
          Nat.card (cubicOddCore (swapFactors c) t.y)=3) ∧
      ((∃ P : Sylow 3 G, (P:Subgroup G)=E) ↔ normalizer (E:Set G) ≤ c.H) ∧
      ((∃ P : Sylow 3 G, (P:Subgroup G)=E) →
        ∀ a ∈ E, ∀ b ∈ E, IsConj a b → ∃ h ∈ c.H, MulAut.conj h a=b) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  refine ⟨c,t,cubic_plane_normalizer_fixes_factor c t.x t.y t.x_order t.y_order,
    t.plane_normalizer_le_H_iff_small_cores,t.plane_sylow_iff_normalizer_le_H,?_⟩
  intro hSylow a ha b hb hab
  exact t.plane_fusion_in_H_of_sylow hSylow a b ha hb hab

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
