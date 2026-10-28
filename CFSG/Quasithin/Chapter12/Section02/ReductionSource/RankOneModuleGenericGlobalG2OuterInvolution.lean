module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2OuterInvolution
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2Transfer

/-!
# Outer involutions in the literal Chapter 12 G₂ comparison

The compatible comparison supplies an odd Hall torus in the whole overlap.
Its normalizer in the original T complements the original S. In particular,
S<T constructs an actual involution outside S; no parity or splitting
hypothesis is added. These are the splitting and existence inputs to
F.4.37–38, not the still-needed centralizer order and Sylow placement.

Source: Aschbacher–Smith F.4.29(2), F.4.37–38, pp.289,293–294,
and 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Subgroup.OddHall Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual whole-overlap torus supplies a cyclic complement to S in T. -/
theorem rankOne_global_g2_source_sylow_torus_split
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
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    let C := ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H)
    ∃ Y : Subgroup G, Y ≤ C ∧ IsHallSubgroup oddPrimes (Y.subgroupOf C) ∧
      (∀ b : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        b.val ∈ Y ↔ (e.middle b).val ∈ Atlas.G2.splitTorus) ∧
      Disjoint (Global.sourceS L H) (normalizer (Y : Set G)) ∧
      IsCyclic ((T : Subgroup G) ⊓ normalizer (Y : Set G) : Subgroup G) ∧
      (T : Set G) = (Global.sourceS L H : Set G) *
        ((T : Subgroup G) ⊓ normalizer (Y : Set G) : Set G) :=
  d.g2_source_sylow_torus_split (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp F e

/-- The same marking constructs an involution normalizing the Hall torus and
inducing an involution on the actual right quotient field. -/
theorem rankOne_global_g2_exists_outer_involution
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
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hne : Global.sourceS L H ≠ (T : Subgroup G)) :
    let C := ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H)
    ∃ Y : Subgroup G, Y ≤ C ∧ IsHallSubgroup oddPrimes (Y.subgroupOf C) ∧
      (∀ b : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        b.val ∈ Y ↔ (e.middle b).val ∈ Atlas.G2.splitTorus) ∧
      ∃ eR : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group F,
      ∃ t : T, orderOf t=2 ∧ t.val ∉ Global.sourceS L H ∧
        t.val ∈ normalizer (Y : Set G) ∧
        orderOf (Global.residualSylowFieldAction hH.1.1.2 eR t)=2 :=
  d.g2_exists_outer_involution (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp F e hne

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
