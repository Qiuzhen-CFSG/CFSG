module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NonsolvableFieldDegree
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionPreparation
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobal

/-!
# The original chosen-factor field obstruction

The prepared original pair supplies nonsolvability of both parabolics and
its actual left PSL2 marking. Apply the two-branch source field equation to
this same pair and full Borel. At the full KnownSimple Chapter 12 consumer,
the original field exponent must be even and at least four. In particular,
the field-four alpha branch is impossible, independently of any reflection,
apartment exchange or finite-quotient construction.

The critical alpha endpoint is the original left factor; the opposite
orientation is not excluded here. General even exponents, original
preparation and exhaustive source assembly retain their existing owners.
Source: DGS (11.7)--(11.8), pp.174--177; Aschbacher--Smith 5.2.4--6,
pp.649--651, F.1.12, pp.263--264, and the application to 12.2.2, p.795.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open Subgroup Theory.GroupTheory ChapterF.Source
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}

/-- The literal commuting branch on the prepared original pair forces the
original left field degree to be twice a degree greater than one. -/
theorem commuting_one_field_degree
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false)
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true))
    (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false),
      Z (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)⁆ = ⊥) :
    ∃ m : ℕ, 1 < m ∧ n = 2*m :=
  original_nonsolvable_commuting_one_field_degree (d.hypothesisF11 h hTH) hc hb hcomm
    (d.parabolics_not_solvable h hp) (by have := h.exponent; omega) h.linear

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Chapter6.Source.RankOneGeneric
open ChapterF.Source.DGS85 Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
  (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
    (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false)
    (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true))
  (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 1)
  (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false),
    Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true)⁆ = ⊥)
include D h hmany hn hpsl hH d hp hc hb hcomm

/-- Both source branches retain the original field exponent at the full
KnownSimple chosen-module consumer. No quotient marking or reflection is input. -/
theorem rankOne_commuting_one_field_degree :
    ∃ m : ℕ, 1 < m ∧ n = 2*m :=
  d.commuting_one_field_degree (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp hc hb hcomm

/-- The original PSL2(4) factor cannot be the critical alpha endpoint of a
commuting distance-one pair with the prepared nonsolvable right factor. -/
theorem rankOne_not_commuting_one_of_small_degree (hsmall : n < 4) : False := by
  obtain ⟨m,hm,he⟩ := D.rankOne_commuting_one_field_degree h hmany hn hpsl hH d hp hc hb hcomm
  omega

/-- Odd original field exponents also exclude this oriented source branch. -/
theorem rankOne_not_commuting_one_of_odd_degree (hodd : Odd n) : False := by
  obtain ⟨m,hm,he⟩ := D.rankOne_commuting_one_field_degree h hmany hn hpsl hH d hp hc hb hcomm
  obtain ⟨k,hk⟩ := hodd
  omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
