module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortOrbits
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2LocalFusion

/-!
# Distinct long-root orbits in the Chapter 12 short-root centralizer

The original compatible comparison gives two ambient-conjugate long roots
that are not conjugate in the full short-root centralizer. Both representatives
remain in the same left parabolic. Commuting-pair exchange and the original
right two-core prove separation without assuming S=T. The right-factor
centralizer is also identified with C_S(v).

These are steps in the orbital comparison of F.4.42. Exhaustive orbit coverage,
the common-stabilizer containment, and the unique fixed coset still remain.
Source: Aschbacher–Smith F.4.42, printed p.295, applied in 5.3.3, p.659,
and the Chapter 12 setup, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Distinct orbits in the full centralizer, retaining the original local maps. -/
theorem rankOne_global_g2_short_centralizer_distinct_long_orbits
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
      let f := (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0).subtype.comp
        e.left.symm.toMonoidHom
      let z := Global.G2ShortAction.longMark f
      let u := Global.G2ShortOrbits.outsideMark f
      IsConj z.val u.val ∧ ¬ IsConj z u :=
  d.g2_short_centralizer_distinct_long_orbits
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he

/-- The right-factor centralizer equals C_S(v), before assuming S=T. -/
theorem rankOne_global_g2_short_factor_centralizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (G2.amalgam (F := F)).reverse) :
    let v := (e.right.symm (Global.G2CompletionFusion.short (1:F))).val
    residual H ⊓ centralizer ({v} : Set G) =
      Global.sourceS L H ⊓ centralizer ({v} : Set G) :=
  d.g2_short_factor_centralizer (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp F e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
