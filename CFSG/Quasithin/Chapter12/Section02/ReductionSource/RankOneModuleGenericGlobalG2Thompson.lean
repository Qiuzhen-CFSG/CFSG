module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Thompson
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2Generation

/-!
# Thompson's mixed-pair counts in the literal Chapter 12 completion

For the same compatible G₂ comparison and the same two marked roots, both
mixed-pair counts equal their concrete model values. The all-degree equality
S=T and the two full centralizer bounds place each counted pair in its
original factor. The actual parabolic maps preserve the product, its order,
its half-order power and both ambient involution classes.

This gives the original ambient order in terms of the two native counts and
the two full ambient centralizer orders, and bounds it by the native group
order times the larger parabolic index in its original normalizer. Bounding
those indices, proving geometric smallness, exhaustive amalgam selection
and original uniqueness remain with the generic-global assembly.
Source: Aschbacher–Smith F.4.43, p.296, and 5.3.3–4, p.659,
with the Chapter 12 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2 TwoInvolutionClassOrder
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal prepared pair has the native Thompson counts at every
original exponent n>1, with both marked roots and parabolic maps retained. -/
theorem rankOne_global_g2_thompson_counts
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
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      let z : G := (e.right.symm (Global.G2CompletionFusion.long (1:F))).val
      let v : G := (e.right.symm (Global.G2CompletionFusion.short (1:F))).val
      kappa z v z = kappa (rootA (1:F)) (rootC (1:F)) (rootA (1:F)) ∧
      kappa z v v = kappa (rootA (1:F)) (rootC (1:F)) (rootC (1:F)) ∧
      Nat.card G =
        kappa (rootA (1:F)) (rootC (1:F)) (rootA (1:F)) *
          Nat.card (centralizer ({v} : Set G)) +
        kappa (rootA (1:F)) (rootC (1:F)) (rootC (1:F)) *
          Nat.card (centralizer ({z} : Set G)) ∧
      Nat.card G ≤
        max ((ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0).relIndex
          (normalizer (L : Set G)))
          ((ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1).relIndex
            (normalizer (residual H : Set G))) * Nat.card (Model F) :=
  d.g2_thompson_counts (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
