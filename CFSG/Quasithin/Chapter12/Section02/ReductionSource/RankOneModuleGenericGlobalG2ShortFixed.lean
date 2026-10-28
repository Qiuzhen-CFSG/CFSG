module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortFixed
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2ShortOrbits

/-!
# The G₂ short-root fixed coset in the literal Chapter 12 setup

The full common stabilizer of the marked long and short roots normalizes L,
without assuming S=T. Under S=T, the marked long root fixes exactly one coset
of N_G(L) intersect C_G(v) in C_G(v). The perfect affine action then yields
C_G(v) <= N_G(L). Odd original degree supplies S=T from the existing field-index
argument. All roots come from the same compatible parabolic comparison.

Source: Aschbacher–Smith F.4.42, printed p.295, and its application in 5.3.3,
p.659, with the Chapter 12 setup, p.795 (`refs/quasithin.pdf`). The original
uniqueness and compatible comparison are retained inputs; even-degree transfer
and the full generic-global classification remain with the assembly owner.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The common stabilizer bound and the conditional fixed-coset conclusion
use one literal comparison and the original source S. -/
theorem rankOne_global_g2_short_fixed_coset_geometry
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F)).reverse)) :
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      let l := (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0).subtype.comp
        e.left.symm.toMonoidHom
      centralizer ({l Global.G2ShortAction.short} : Set G) ⊓
        centralizer ({l Global.G2ShortAction.long} : Set G) ≤ normalizer (L : Set G) ∧
      (Global.sourceS L H=(T : Subgroup G) →
        (∃! q : centralizer ({l Global.G2ShortAction.short} : Set G) ⧸
          (normalizer (L : Set G)).subgroupOf (centralizer ({l Global.G2ShortAction.short} : Set G)),
          Global.G2ShortAction.longMark l • q=q) ∧
        centralizer ({l Global.G2ShortAction.short} : Set G) ≤ normalizer (L : Set G)) :=
  d.g2_short_fixed_coset_geometry (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F he

/-- At odd original degrees the full short-root centralizer lies in N_G(L),
and the pinned long root has its unique fixed coset. -/
theorem rankOne_global_g2_short_centralizer_of_odd
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n) (hnodd : Odd n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F)).reverse)) :
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      let l := (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0).subtype.comp
        e.left.symm.toMonoidHom
      (∃! q : centralizer ({l Global.G2ShortAction.short} : Set G) ⧸
          (normalizer (L : Set G)).subgroupOf (centralizer ({l Global.G2ShortAction.short} : Set G)),
          Global.G2ShortAction.longMark l • q=q) ∧
        centralizer ({l Global.G2ShortAction.short} : Set G) ≤ normalizer (L : Set G) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨e,_,hfixed⟩ := d.g2_short_fixed_coset_geometry hi hH hp F he
  exact ⟨e,hfixed (d.g2_short_root_not_fused_of_odd hi hH hp hnodd F he).1⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
