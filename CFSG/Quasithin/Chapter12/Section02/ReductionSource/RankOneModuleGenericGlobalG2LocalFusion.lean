module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2LocalFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2ShortAction

/-!
# The full local G₂ fusion comparison in Chapter 12

The original chosen-module inputs supply the two distinct ambient root
classes. Reduction inside either whole parabolic then preserves and reflects
ambient involution fusion under the same compatible comparison, including
pairs from different endpoints. This supplies the local class comparison in
F.4.42's orbital exchange without assuming S=T or a completion isomorphism.

The full-centralizer orbit comparison and unique-fixed-coset condition remain
to be proved. Even-degree transfer, exhaustive comparison, original uniqueness
and concrete completion recognition remain with the generic-global assembly.
Source: Aschbacher–Smith F.4.35 and F.4.42, printed pp.292 and 295, applied
in 5.3.3, p.659, and the Chapter 12 setup, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Both whole original parabolics and their mixed pairs have precisely the
model's ambient involution fusion under the retained compatible maps. -/
theorem rankOne_global_g2_parabolic_involution_fusion
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
      (G2.amalgam (F := F)).reverse,
      ¬ IsConj (e.right.symm (Global.G2CompletionFusion.long (1:F))).val
        (e.right.symm (Global.G2CompletionFusion.short (1:F))).val ∧
      (∀ x y : ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0,
        orderOf x = 2 → orderOf y = 2 →
          (IsConj x.val y.val ↔ IsConj (e.left x).val (e.left y).val)) ∧
      (∀ x y : ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1,
        orderOf x = 2 → orderOf y = 2 →
          (IsConj x.val y.val ↔ IsConj (e.right x).val (e.right y).val)) ∧
      (∀ (x : ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0)
        (y : ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1),
        orderOf x = 2 → orderOf y = 2 →
          (IsConj x.val y.val ↔ IsConj (e.left x).val (e.right y).val)) :=
  d.g2_parabolic_involution_fusion
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
