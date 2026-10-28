module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourSplitPair
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalUnitaryFourGraphAction

/-!
# The whole original U₄ split pair in Chapter 12

For every selected perfect R, one actual source-S involution splits both
full endpoints and their full Borel. The resulting native semidirect amalgam
retains both inclusion squares and the same conjugate graph action on L.
The producer proves that all three actions restrict the same original native
outer involution. Reduced DGS recognition supplies the broad original marking;
the prepared application combines the result with the completed ordinary exit.

Identifying the constructed action with the prescribed native graph extension
remains required. DGS exhaustion, prepared U₅, uniqueness and unconditional
GlobalExit are not discharged here. The original S and full odd overlap are
retained throughout, including q=4.
Source: Aschbacher--Smith F.1.12, pp.263--264, 5.2.6--7, pp.650--651,
and the Chapter 12 application, p.795 (`refs/quasithin.pdf`).
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

/-- The same actual outer involution splits both whole native endpoints
and their entire common Borel. Its full left residual graph marking is retained. -/
theorem rankOne_global_original_unitaryFour_full_split_pair
    (hi : ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2) :
    let input := D.rankOne_generic_input_of_many h hmany hn hpsl
    ∃ (a : L ≃* L2 m hm) (t : Global.sourceS L H)
      (hout : t.val ∉ L) (ht : orderOf t.val=2),
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))
        (RankTwoAmalgam.semidirect
          (d.originalUnitaryFourNativePairAction input hH.1.1.2 hp m hm point mark hi t hout ht))) ∧
      ∃ c : (L ⊔ Global.sourceS L H : Subgroup G),
        Global.Preparation.originalUnitaryFourResidualAction input hH.1.1.2 m hm a (inclusion le_sup_right t) =
          Global.Preparation.originalUnitaryFourResidualAction input hH.1.1.2 m hm a c * Extension.L2Aut m hm *
            (Global.Preparation.originalUnitaryFourResidualAction input hH.1.1.2 m hm a c)⁻¹ := by
  let input := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨_,⟨a⟩,_,_⟩ := d.original_unitaryFour_factors input hH.1.1.2 hp m hm point mark
  exact ⟨a,d.original_unitaryFour_full_split_pair input hH.1.1.2 hp m hm point mark hi a⟩

omit mark in
include D h hmany hn hpsl hH d hp in
/-- Reduced DGS recognition restores the original marking and constructs
the complete degree-two split pair, retaining both full Borel squares. -/
theorem rankOne_global_full_split_pair_of_reduced_unitaryFour
    (hmgt : 1 < m)
    (r : RankTwoAmalgam.Iso
      (ChapterF.Source.DGS85.OriginalExtension.reducedAmalgam ![L,R] (Global.sourceS L H))
      (ChapterF.Source.DGS85.OriginalExtension.UnitaryFourNative.amalgam m hm point))
    (hi : ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2) :
    let input := D.rankOne_generic_input_of_many h hmany hn hpsl
    ∃ (mark : Global.OriginalUnitaryFour.Marking m hm point L R (Global.sourceS L H))
      (t : Global.sourceS L H) (hout : t.val ∉ L) (ht : orderOf t.val=2),
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))
        (RankTwoAmalgam.semidirect
          (d.originalUnitaryFourNativePairAction input hH.1.1.2 hp m hm point mark hi t hout ht))) := by
  let input := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨mark⟩ := ChapterF.Source.DGS85.OriginalExtension.exists_original_unitaryFour_marking_of_reduced_iso
    (d.hypothesisF11 input hH.1.1.2) m hm hmgt point r
  obtain ⟨_,t,hout,ht,he,_⟩ := D.rankOne_global_original_unitaryFour_full_split_pair
    h hmany hn hpsl hH d hp m hm point mark hi
  exact ⟨mark,t,hout,ht,he⟩

omit d hp mark in
include D h hmany hn hpsl hH in
/-- The prepared original row has either its ordinary global exit or the
constructed split native pair. Identifying the latter action with the prescribed
native graph extension remains necessary for final recognition. -/
theorem rankOne_globalExit_or_original_unitaryFour_full_split_pair
    (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (mark : Global.OriginalUnitaryFour.Marking m hm point L (residual H) (Global.sourceS L H)) :
    let input := D.rankOne_generic_input_of_many h hmany hn hpsl
    RankOneModule.GlobalExit G ∨
      ∃ (hi : ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2)
        (t : Global.sourceS L H) (hout : t.val ∉ L) (ht : orderOf t.val=2),
        Nonempty (RankTwoAmalgam.Iso
          (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
          (RankTwoAmalgam.semidirect
            (d.originalUnitaryFourNativePairAction input hH.1.1.2 hp m hm point mark hi t hout ht))) := by
  rcases D.rankOne_globalExit_or_original_unitaryFour_degree_two h hmany hn hpsl hH
    m hm point d hp mark with hx | hi
  · exact Or.inl hx
  · obtain ⟨_,t,hout,ht,he,_⟩ := D.rankOne_global_original_unitaryFour_full_split_pair
      h hmany hn hpsl hH d hp m hm point mark hi
    exact Or.inr ⟨hi,t,hout,ht,he⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
