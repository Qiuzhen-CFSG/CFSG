module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourCatalogue
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalUnitaryFourGraphRigidity

/-!
# The full original U₄ catalogue comparison in Chapter 12

For every selected perfect R, the original marking now gives the ordinary
or degree-two catalogue amalgam, including both endpoint squares and its
whole odd Borel. The same source S is used throughout. Genuine reduced-row
restoration supplies the marking; no graph action or endpoint identification
is added as a hypothesis. For R=O²(H), the existing prepared U₄ recognition
therefore gives the strict-exponent GlobalExit in both branches.

Exhaustive DGS source selection, the other original rows, prepared U₅,
uniqueness and unconditional generic assembly remain separate obligations.
Source: Aschbacher--Smith F.1.12, pp.263--264, 5.2.6--7, pp.650--651,
5.3.2--4, pp.658--659, and Chapter 12, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R)
  (hp : Group.IsPerfect R) (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (mark : Global.OriginalUnitaryFour.Marking m hm point L R (Global.sourceS L H))
include D h hmany hn hpsl hH d hp mark

/-- The actual original degree-two branch is the fixed catalogue amalgam,
with no residual-H restriction on the selected perfect R. -/
theorem rankOne_global_original_unitaryFour_extension_comparison
    (hi : ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2) :
    Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))
      (Extension.amalgam m hm).reverse) :=
  d.original_unitaryFour_amalgam_of_index_two
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm point mark hi

/-- Both original extension indices now give the concrete comparison
needed by the universal selected-R preparation consumer. -/
theorem rankOne_global_comparison_of_original_unitaryFour :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.concreteComparison_of_original_unitaryFour
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm point mark

omit mark in
include D h hmany hn hpsl hH d hp in
/-- The genuine reduced U₄ source row restores the full original comparison,
including its possible degree-two extension and the full odd overlap. -/
theorem rankOne_global_comparison_of_reduced_unitaryFour
    (hmgt : 1 < m)
    (r : RankTwoAmalgam.Iso
      (ChapterF.Source.DGS85.OriginalExtension.reducedAmalgam ![L,R] (Global.sourceS L H))
      (ChapterF.Source.DGS85.OriginalExtension.UnitaryFourNative.amalgam m hm point)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  let input := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨mark⟩ := ChapterF.Source.DGS85.OriginalExtension.exists_original_unitaryFour_marking_of_reduced_iso
    (d.hypothesisF11 input hH.1.1.2) m hm hmgt point r
  exact D.rankOne_global_comparison_of_original_unitaryFour h hmany hn hpsl hH d hp m hm point mark

omit d hp mark in
include D h hmany hn hpsl hH in
/-- The full original marked U₄ row has the actual strict-exponent GlobalExit,
including the exceptional degree-two action branch. -/
theorem rankOne_globalExit_of_original_unitaryFour
    (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (mark : Global.OriginalUnitaryFour.Marking m hm point L (residual H) (Global.sourceS L H)) :
    RankOneModule.GlobalExit G := by
  let input := D.rankOne_generic_input_of_many h hmany hn hpsl
  rcases d.original_unitaryFour_amalgam_alternatives input hH.1.1.2 hp m hm point mark with he | he
  · exact D.rankOne_globalExit_of_unitaryFour h hmany hn hpsl hH d hp m hm (Or.inl (Or.inr he))
  · exact D.rankOne_globalExit_of_unitaryFour h hmany hn hpsl hH d hp m hm (Or.inr (Or.inr he))

omit d hp mark in
include D h hmany hn hpsl hH in
/-- The original reduced source row feeds prepared recognition without a
remaining graph-extension premise. -/
theorem rankOne_globalExit_of_reduced_unitaryFour
    (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (hmgt : 1 < m)
    (r : RankTwoAmalgam.Iso
      (ChapterF.Source.DGS85.OriginalExtension.reducedAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.Source.DGS85.OriginalExtension.UnitaryFourNative.amalgam m hm point)) :
    RankOneModule.GlobalExit G := by
  let input := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨mark⟩ := ChapterF.Source.DGS85.OriginalExtension.exists_original_unitaryFour_marking_of_reduced_iso
    (d.hypothesisF11 input hH.1.1.2) m hm hmgt point r
  exact D.rankOne_globalExit_of_original_unitaryFour h hmany hn hpsl hH m hm point d hp mark
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
