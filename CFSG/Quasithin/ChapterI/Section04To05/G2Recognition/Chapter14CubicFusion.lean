module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14CubicThreeCore
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CubicFusion

/-!
# Cubic nonfusion and the Sylow-nine branch in dimension four

The configuration constructed from the original SourceLocalData has two
nonconjugate marked cubic lines. Their join is elementary of order nine,
and it is Sylow precisely when both cubic odd cores have order three.
Consequently divisibility by 3³ implies divisibility by 3⁴.

This applies the q=3 small-core argument of Fong, Nagoya Math. J.39
(1970), §6B, p.75, without importing its q≥5 standing assumption or its
separate branch-exclusion results. The proof uses only the original
configuration and preserves both SL₂(3) embeddings.
The remaining small-core exclusions, BN-pair construction and actual
Atlas.G2.Model equivalence are owned by `qt-i45-g2-recognition`.
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

theorem source_cubic_nonfusion_and_sylow (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c),
      ¬ IsConj ((t.x:c.H):G) ((t.y:c.H):G) ∧
      (∀ g : G, (zpowers ((t.x:c.H):G)).map (MulAut.conj g).toMonoidHom ≠
        zpowers ((t.y:c.H):G)) ∧
      IsElementaryAbelian 3 (zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G) ∧
      Nat.card (zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G)=9 ∧
      ((∃ P : Sylow 3 G, (P : Subgroup G) =
        zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)) ↔
        Nat.card (cubicOddCore c t.x)=3 ∧
          Nat.card (cubicOddCore (swapFactors c) t.y)=3) ∧
      (3^3 ∣ Nat.card G → 3^4 ∣ Nat.card G) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  obtain ⟨he,hc⟩ := cubic_plane_data c t.x t.y t.x_order t.y_order
  exact ⟨c,t,cubic_factors_not_conjugate c t.x t.y t.x_order t.y_order,
    cubic_lines_not_conjugate c t.x t.y t.x_order,he,hc,t.cubic_plane_sylow_iff,
    cubic_cube_dvd_fourth_power c⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
