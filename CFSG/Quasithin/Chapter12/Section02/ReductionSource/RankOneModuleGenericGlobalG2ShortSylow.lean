module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2AmbientOrder

/-!
# The designated G₂ short-root centralizer in Chapter 12

The compatible comparison and S=T now prove the literal F.4.40 conclusion:
C_S(v) is Sylow in C_G(v), with order q⁴ and v marked by the same right map.
The odd-degree application discharges S=T by the original field-index result.
The full-centralizer containment of F.4.42, even-degree transfer, exhaustive
comparison and completion recognition remain separate source obligations.

Source: Aschbacher–Smith F.4.40, printed p.294, applied in 5.3.3, p.659,
and the original Chapter 12 setup on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- F.4.40 at the original S=T, preserving the designated root and both maps. -/
theorem rankOne_global_g2_short_centralizer_sylow
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1<n)
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
        (G2.amalgam (F := F)).reverse))
    (hST : Global.sourceS L H=(T : Subgroup G)) :
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (G2.amalgam (F := F)).reverse,
      let v : G := (e.right.symm (Global.G2CompletionFusion.short (1:F))).val
      Nat.card (Global.sourceS L H ⊓ centralizer ({v} : Set G) : Subgroup G)=Nat.card F^4 ∧
        ∃ P : Sylow 2 (centralizer ({v} : Set G)),
          (P : Subgroup (centralizer ({v} : Set G)))=
            (Global.sourceS L H).subgroupOf (centralizer ({v} : Set G)) :=
  d.g2_short_centralizer_sylow (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he hST

/-- Odd original degree discharges the Sylow equality without a transfer premise. -/
theorem rankOne_global_g2_short_centralizer_sylow_of_odd
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1<n) (hnodd : Odd n)
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
      let v : G := (e.right.symm (Global.G2CompletionFusion.short (1:F))).val
      Nat.card (Global.sourceS L H ⊓ centralizer ({v} : Set G) : Subgroup G)=Nat.card F^4 ∧
        ∃ P : Sylow 2 (centralizer ({v} : Set G)),
          (P : Subgroup (centralizer ({v} : Set G)))=
            (Global.sourceS L H).subgroupOf (centralizer ({v} : Set G)) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.g2_short_centralizer_sylow hi hH hp F he
    (d.g2_short_root_not_fused_of_odd hi hH hp hnodd F he).1

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
