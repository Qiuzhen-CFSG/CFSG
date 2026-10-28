module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalUnitaryFourReduced

/-!
# Original U₄ outer-action restriction at the Chapter 12 consumer

Every actual preparation and selected perfect R has the plane-first U₄
orientation and n=2m. The original S is the product of its actual right
join-core and T∩L. Their exact intersection and index identify the remaining
outer size with the enlargement of O₂(R), including the possible degree-two
extension. The same original marked action is inner on the native right
quotient; its canonical PSL₂(2ᵐ) field coefficient vanishes.

The broad original marking remains the explicit earlier DGS input. The
native degree bound, full comparison, exhaustive markings, uniqueness and
unconditional GlobalExit assembly are still required; no source Sylow or
selected factor is replaced by an ambient one.
Source: Aschbacher--Smith F.1.12, pp.263--264, 5.2.6--7, pp.650--651,
and the literal Chapter 12 setup, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
  (hp : Group.IsPerfect R) (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (e : Global.OriginalUnitaryFour.Marking m hm point L R (Global.sourceS L H))
include D h hmany hn hpsl hH d hp e

/-- The original selected pair fixes the U₄ orientation and both native
residuals, before any outer-action bound or pure-model recognition. -/
theorem rankOne_global_original_unitaryFour_factors :
    1 < m ∧ point = false ∧ n = 2*m ∧ Nonempty (L ≃* L2 m hm) ∧
      Nonempty (R ≃* PointLocal.ProjectiveLocal m hm) ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^m) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.original_unitaryFour_nonbinary hi hH.1.1.2 hp m hm point e,
    d.original_unitaryFour_orientation hi hH.1.1.2 hp m hm point e,
    d.original_unitaryFour_factors hi hH.1.1.2 hp m hm point e⟩

/-- All remaining outer size lies in the actual right join-core, with its
exact intersection and order, on the same arbitrary selected perfect R. -/
theorem rankOne_global_original_unitaryFour_join_core :
    Global.sourceS L H = (R ⊔ Global.sourceS L H).pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ L) ∧
    ((T : Subgroup G) ⊓ L) ⊓ (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧
    ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H) =
      (R.pCoreIn 2).relIndex ((R ⊔ Global.sourceS L H).pCoreIn 2) ∧
    Nat.card ((R ⊔ Global.sourceS L H).pCoreIn 2) =
      (2^m)^5 * ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.original_unitaryFour_source_factorization hi hH.1.1.2 hp m hm point e,
    d.original_unitaryFour_join_core_intersection hi hH.1.1.2 hp m hm point e,
    d.original_unitaryFour_outer_index hi hH.1.1.2 hp m hm point e,
    d.original_unitaryFour_join_core_card hi hH.1.1.2 hp m hm point e⟩

/-- The literal original S action on the right native residual quotient
is inner, and its actual right join-core acts trivially. -/
theorem rankOne_global_original_unitaryFour_quotient_action :
    (∀ s : Global.sourceS L H,
      s.val ∈ (R ⊔ Global.sourceS L H).pCoreIn 2 →
        Global.Preparation.originalUnitaryFourRightQuotientAction m hm point e s = 1) ∧
    (∀ s : Global.sourceS L H,
      Global.Preparation.originalUnitaryFourRightQuotientAction m hm point e s ∈
        MulAut.innerSubgroup (rightResidualImage (Global.OriginalUnitaryFour.endpoint m hm (!point)) ⧸
          pCore 2 (rightResidualImage (Global.OriginalUnitaryFour.endpoint m hm (!point))))) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.original_unitaryFour_core_quotient_action hi hH.1.1.2 hp m hm point e,
    d.original_unitaryFour_right_quotient_inner hi hH.1.1.2 hp m hm point e⟩

omit point e in
include D h hmany hn hpsl hH d hp in
/-- The canonical native point-quotient field coefficient is trivial in
the surviving original orientation; the full graph action remains allowed. -/
theorem rankOne_global_original_unitaryFour_point_field
    (e : Global.OriginalUnitaryFour.Marking m hm false L R (Global.sourceS L H)) :
    ∃ hmgt : 1 < m, ∀ s : Global.sourceS L H,
      Theory.PSL2.fieldProjection (PointLocal.FixedField m)
        ((MulAut.congr (Global.OriginalUnitaryFour.pointQuotient m hm hmgt))
          (Global.Preparation.originalUnitaryFourRightQuotientAction m hm false e s)) = 1 := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.original_unitaryFour_nonbinary hi hH.1.1.2 hp m hm false e,
    d.original_unitaryFour_point_field_trivial hi hH.1.1.2 hp m hm e⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
