module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2ShortSylow

/-!
# The terminal G₂ short-centralizer argument in Chapter 12

The original long-core derived group is the A–B root plane under the same
compatible comparison. Its perfect affine block acts nontrivially. I.8.5
therefore forces the full short-root centralizer into N_G(L), provided the
pinned long root has a unique fixed coset of the local centralizer. The
explicit model centralizer orbit propagates this single condition over the
whole nonidentity plane. Both marked roots retain the original right map.

The unique-fixed-coset condition is the remaining orbital comparison in
F.4.42, not a consequence asserted by this module. Even-degree transfer,
exhaustive comparison, original uniqueness and concrete completion recognition
remain with the generic-global assembly.
Source: Aschbacher–Smith F.4.42, printed p.295, applied in 5.3.3, p.659,
and the Chapter 12 setup, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original Chapter 12 inputs discharge the parameter, perfect-action,
normality and root-plane premises of the terminal F.4.42 contradiction. -/
theorem rankOne_global_g2_short_centralizer_of_long_unique_fixed
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1<n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (G2.amalgam (F := F)).reverse) :
    let f := (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0).subtype.comp
      e.left.symm.toMonoidHom
    let v : G := f Global.G2ShortAction.short
    v = (e.right.symm (Global.G2CompletionFusion.short (1:F))).val ∧
      (Global.G2ShortAction.longMark f).val =
        (e.right.symm (Global.G2CompletionFusion.long (1:F))).val ∧
      Global.G2ShortAction.plane f = ⁅L.pCoreIn 2,L.pCoreIn 2⁆ ∧
      ((∃! q : centralizer ({v} : Set G) ⧸ (normalizer (L : Set G)).subgroupOf
          (centralizer ({v} : Set G)), Global.G2ShortAction.longMark f • q=q) →
        centralizer ({v} : Set G) ≤ normalizer (L : Set G)) :=
  d.g2_short_centralizer_of_long_unique_fixed
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp F e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
