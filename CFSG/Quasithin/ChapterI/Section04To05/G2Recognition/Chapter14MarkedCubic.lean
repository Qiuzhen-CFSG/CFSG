module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14CubicFusion
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MarkedCubic

/-!
# The third marked cubic class in dimension four

The genuine SourceLocalData configuration supplies a cubic element in its
original M. Its ambient class is different from the classes of both
original factor cubics. More strongly, neither factor cubic belongs to
any conjugate of M, and neither factor line is conjugate to this M-line.
An explicit conjugating element places the M-cubic in the common plane,
outside its two marked factor lines, without any ambient Sylow assumption.

This applies the elementary-eight normalizer obstruction to the literal
configuration of Aschbacher–Smith I.4.5, printed p.417. It assumes neither
ambient simplicity nor prime-three divisibility. The exceptional small-core
exclusions and the actual Atlas.G2.Model recognition remain with
`qt-i45-g2-recognition`; `qt-d-14414-g2-source` produces SourceLocalData
and discharges that explicit premise in the final Chapter14 assembly.
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

theorem source_marked_M_cubic_nonfusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c) (m : c.M) (k : G),
      orderOf m=3 ∧
      MulAut.conj k (m:G) ∈ zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) ∧
      MulAut.conj k (m:G) ∉ zpowers ((t.x:c.H):G) ∧
      MulAut.conj k (m:G) ∉ zpowers ((t.y:c.H):G) ∧
      ¬ IsConj ((t.x:c.H):G) ((t.y:c.H):G) ∧
      ¬ IsConj ((t.x:c.H):G) (m:G) ∧
      ¬ IsConj ((t.y:c.H):G) (m:G) ∧
      (∀ g : G, ((t.x:c.H):G) ∉ c.M.map (MulAut.conj g).toMonoidHom ∧
        ((t.y:c.H):G) ∉ c.M.map (MulAut.conj g).toMonoidHom) ∧
      (∀ g : G, (zpowers ((t.x:c.H):G)).map (MulAut.conj g).toMonoidHom ≠
          zpowers (m:G) ∧
        (zpowers ((t.y:c.H):G)).map (MulAut.conj g).toMonoidHom ≠ zpowers (m:G)) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  obtain ⟨m,k,hm,hplane,hleft,hright⟩ := exists_marked_M_diagonal c t.x t.y t.x_order t.y_order
  exact ⟨c,t,m,k,hm,hplane,hleft,hright,
    cubic_factors_not_conjugate c t.x t.y t.x_order t.y_order,
    cubic_factor_not_conjugate_M c t.x t.x_order m,
    cubic_factor_not_conjugate_M (swapFactors c) t.y t.y_order m,
    fun g => ⟨cubic_factor_not_mem_conjugate_M c t.x t.x_order g,
      cubic_factor_not_mem_conjugate_M (swapFactors c) t.y t.y_order g⟩,
    fun g => ⟨cubic_factor_line_not_conjugate_M c t.x t.x_order m g,
      cubic_factor_line_not_conjugate_M (swapFactors c) t.y t.y_order m g⟩⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
