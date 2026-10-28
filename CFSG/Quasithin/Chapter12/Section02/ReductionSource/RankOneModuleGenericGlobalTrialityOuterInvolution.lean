module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityOuterInvolution
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityCompletionFusion

/-!
# Triality outer involutions in the literal Chapter 12 setup

The compatible triality comparison supplies a marked Hall torus and a
cyclic complement to the original S in T. If S<T, it constructs an actual
outer involution, with its cubic-field quotient action and exact centralizer
extension factor. No parity, splitting or centralizer-size premise is added.
The fixed-root bound and ambient Sylow placement still belong to the S=T
argument; the final ambient model recognition remains with the assembly.

Source: Aschbacher–Smith F.4.29(2), F.4.37–38, pp.289,293–294,
and 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Subgroup.OddHall Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The whole-overlap torus supplies a cyclic complement to the original S. -/
theorem rankOne_global_triality_source_sylow_torus_split
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    let C := ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H)
    ∃ Y : Subgroup G, Y ≤ C ∧ IsHallSubgroup oddPrimes (Y.subgroupOf C) ∧
      (∀ b : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        b.val ∈ Y ↔ (e.middle b).val ∈ torus (binaryParameters m hm)) ∧
      Disjoint (Global.sourceS L H) (normalizer (Y : Set G)) ∧
      IsCyclic ((T : Subgroup G) ⊓ normalizer (Y : Set G) : Subgroup G) ∧
      (T : Set G) = (Global.sourceS L H : Set G) *
        ((T : Subgroup G) ⊓ normalizer (Y : Set G) : Set G) :=
  d.triality_source_sylow_torus_split (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp m hm e


/-- The same marked involution retains its cubic-field coefficient and the
exact centralizer factor [T:S], bounded by the original exponent. -/
theorem rankOne_global_triality_exists_outer_involution_centralizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hne : Global.sourceS L H ≠ (T : Subgroup G)) :
    let C := ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H)
    ∃ Y : Subgroup G, Y ≤ C ∧ IsHallSubgroup oddPrimes (Y.subgroupOf C) ∧
      (∀ b : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        b.val ∈ Y ↔ (e.middle b).val ∈ torus (binaryParameters m hm)) ∧
      ∃ eR : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group (ExtensionField (binaryParameters m hm)),
      ∃ t : T, orderOf t=2 ∧ t.val ∉ Global.sourceS L H ∧
        t.val ∈ normalizer (Y : Set G) ∧ orderOf (Global.residualSylowFieldAction hH.1.1.2 eR t)=2 ∧
        Nat.card (FixedBy.subfield (ExtensionField (binaryParameters m hm)) (Global.residualSylowFieldAction hH.1.1.2 eR t))^2=Nat.card (ExtensionField (binaryParameters m hm)) ∧
        Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) =
          Nat.card (Global.sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) *
            (Global.sourceS L H).relIndex (T : Subgroup G) ∧
        Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤
          Nat.card (Global.sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) * n :=
  d.triality_exists_outer_involution_centralizer (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp m hm e hne

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
