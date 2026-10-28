module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourReduced
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalUnitaryRestriction

/-!
# Original U₄ extension restriction at the Chapter 12 consumer

For every actual preparation and selected perfect R, the broad original
marking identifies both relative Sylows and the exact inner S image. The
same original endpoint maps restrict to their two-residuals and give the
ordinary U₄ comparison on S₀=T∩L, including both whole-Borel squares.
The genuine native placement theorem then conjugates each involution in
the reduced overlap into an original selected-factor two-core.

These statements retain both orientations and any outer part of S. The
remaining normalized-Borel bound on that outer action, exhaustive DGS
markings, original uniqueness and unconditional GlobalExit assembly still
need their proofs. Neither S=T nor R=O²(H) is imposed.
Source: Aschbacher--Smith F.1.12, pp.263--264, 5.2.6--7, pp.650--651,
F.4.35, p.292, and the literal Chapter 12 setup, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original chosen pair has a common native Sylow of order q⁶;
the exact original S image may still have an outer part. -/
theorem rankOne_global_original_unitaryFour_intersections
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) (m : ℕ) (hm : 1 ≤ m) (point : Bool)
    (e : Global.OriginalUnitaryFour.Marking m hm point L R (Global.sourceS L H)) :
    1 < m ∧ Global.sourceS L H ⊓ R = (T : Subgroup G) ⊓ L ∧
      Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) = (2^m)^6 ∧
      e.sylowHom.range ⊓ MulAut.innerSubgroup (ProjectiveGroup m hm) =
        (upperProjective m hm).map MulAut.conj := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hs := d.original_unitaryFour_intersections hi hH.1.1.2 hp m hm point e
  have hc := (d.original_unitaryFour_intersections_card hi hH.1.1.2 hp m hm point e).1
  rw [d.left_intersection] at hc
  exact ⟨d.original_unitaryFour_nonbinary hi hH.1.1.2 hp m hm point e,
    hs.symm.trans d.left_intersection,hc,
    d.original_unitaryFour_source_inner hi hH.1.1.2 hp m hm point e⟩

/-- The full native right Borel normalizes the original source S image. -/
theorem rankOne_global_original_unitaryFour_borel_normalizes
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) (m : ℕ) (hm : 1 ≤ m) (point : Bool)
    (e : Global.OriginalUnitaryFour.Marking m hm point L R (Global.sourceS L H)) :
    (Global.OriginalUnitaryFour.nativeResidual m hm (!point) ⊓
      normalizer (upperProjective m hm : Set (ProjectiveGroup m hm))).map MulAut.conj ≤
        normalizer (e.sylowHom.range : Set _) :=
  d.original_unitaryFour_borel_normalizes
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm point e

/-- Both literal two-residuals retain their original selected factors and
admit the ordinary U₄ comparison, with both inclusion squares. -/
theorem rankOne_global_original_unitaryFour_reduced_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) (m : ℕ) (hm : 1 ≤ m) (point : Bool)
    (e : Global.OriginalUnitaryFour.Marking m hm point L R (Global.sourceS L H)) :
    (∀ i : Fin 2, ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i =
      (pResidual 2 (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i)).map
        (ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) i).subtype) ∧
    (∀ i : Fin 2, (solvableResidual
      (ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i)).map
      (ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i).subtype = ![L,R] i) ∧
    Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] ((T : Subgroup G) ⊓ L))
      (Global.OriginalUnitaryFour.nativeAmalgam m hm point)) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.original_unitaryFour_reduced_parabolics hi hH.1.1.2 hp m hm point e,
    d.original_unitaryFour_reduced_residuals hi hH.1.1.2 hp m hm point e,
    ⟨d.originalUnitaryFourReducedComparison hi hH.1.1.2 hp m hm point e⟩⟩

/-- Apply native involution placement to the actual Chapter 12 factors,
with conjugators in the literal reduced endpoints. -/
theorem rankOne_global_original_unitaryFour_involution_placement
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
    (hp : Group.IsPerfect R) (m : ℕ) (hm : 1 ≤ m) (point : Bool)
    (e : Global.OriginalUnitaryFour.Marking m hm point L R (Global.sourceS L H))
    (x : G) (hx : x ∈ ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 0 ⊓
      ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 1) (hx2 : x^2=1) :
    (∃ g ∈ ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 0,
      g*x*g⁻¹ ∈ R.pCoreIn 2) ∨
    (∃ g ∈ ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 1,
      g*x*g⁻¹ ∈ L.pCoreIn 2) :=
  d.original_unitaryFour_involution_placement
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm point e x hx hx2
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
