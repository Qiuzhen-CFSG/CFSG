module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourCoreCollapse
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalUnitaryFourLeftCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitarySource.Recognition

/-!+# Original U₄ core collapse and the ordinary Chapter 12 exit

For every selected perfect R, the original residual centralizer C_S(L)
vanishes and O₂(LS)=O₂(L). The actual S has outer index one or two.
The index-one branch has a full original comparison, preserving both
endpoint inclusion squares and the odd overlap. When R is the residual,
the existing prepared recognition therefore yields the literal GlobalExit.

The final reduction retains the exact degree-two branch. Its graph-action
identification, exhaustive DGS recognition and unconditional assembly are
still required. Reduced-row applications use the genuine original marking
restoration, without imposing S=T or R=O²(H) on arbitrary preparations.
Source: Aschbacher--Smith F.1.12, pp.263--264; 5.2.6--7, pp.650--651;
5.3.2--4, pp.658--659; Chapter 12, p.795 (`refs/quasithin.pdf`).
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
  (e : Global.OriginalUnitaryFour.Marking m hm point L R (Global.sourceS L H))
include D h hmany hn hpsl hH d hp e

/-- The right core detects automorphisms of the actual selected factor. -/
theorem rankOne_global_original_unitaryFour_right_core_action_faithful :
    Function.Injective (MulAut.characteristic (pCore 2 R)) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.original_unitaryFour_right_core_action_faithful hi hH.1.1.2 hp m hm point e

/-- The original residual centralizer is trivial and the left core does not enlarge. -/
theorem rankOne_global_original_unitaryFour_core_collapse :
    Global.sourceS L H ⊓ centralizer (L : Set G) = ⊥ ∧
      (L ⊔ Global.sourceS L H).pCoreIn 2 = L.pCoreIn 2 := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.original_unitaryFour_residual_centralizer_eq_bot hi hH.1.1.2 hp m hm point e,
    d.original_unitaryFour_left_core_eq hi hH.1.1.2 hp m hm point e⟩

/-- The full original index bound has no unproved centralizer denominator. -/
theorem rankOne_global_original_unitaryFour_outer_index_one_or_two :
    ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=1 ∨
      ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2 := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.original_unitaryFour_outer_index_one_or_two hi hH.1.1.2 hp m hm point e

/-- The two literal original orders retain the possible outer involution. -/
theorem rankOne_global_original_unitaryFour_orders :
    (Nat.card (Global.sourceS L H) = (2^m)^6 ∨
      Nat.card (Global.sourceS L H) = 2*(2^m)^6) ∧
    (Nat.card ((R ⊔ Global.sourceS L H).pCoreIn 2) = (2^m)^5 ∨
      Nat.card ((R ⊔ Global.sourceS L H).pCoreIn 2) = 2*(2^m)^5) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.original_unitaryFour_sourceS_card hi hH.1.1.2 hp m hm point e,
    d.original_unitaryFour_right_core_card hi hH.1.1.2 hp m hm point e⟩

/-- The original ordinary branch supplies the actual catalogue comparison. -/
theorem rankOne_global_comparison_of_original_unitaryFour_index_one
    (hi : ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=1) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  let hi' := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.concreteComparison_of_original_unitaryFour_index_one hi' hH.1.1.2 hp m hm point e hi

/-- The literal original comparison is reduced to its single degree-two action branch. -/
theorem rankOne_global_original_unitaryFour_comparison_or_degree_two :
    Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) (amalgam m hm).reverse) ∨
    (((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2 ∧
      (R.pCoreIn 2).relIndex ((R ⊔ Global.sourceS L H).pCoreIn 2)=2) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.original_unitaryFour_comparison_or_degree_two hi hH.1.1.2 hp m hm point e

omit e in
include D h hmany hn hpsl hH d hp in
/-- Genuine reduced-row restoration discharges the broad marking premise
in the original centralizer and full-index conclusions. -/
theorem rankOne_global_core_collapse_of_reduced_unitaryFour
    (hmgt : 1 < m)
    (r : RankTwoAmalgam.Iso
      (ChapterF.Source.DGS85.OriginalExtension.reducedAmalgam ![L,R] (Global.sourceS L H))
      (ChapterF.Source.DGS85.OriginalExtension.UnitaryFourNative.amalgam m hm point)) :
    Global.sourceS L H ⊓ centralizer (L : Set G) = ⊥ ∧
      (L ⊔ Global.sourceS L H).pCoreIn 2 = L.pCoreIn 2 ∧
      (((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=1 ∨
        ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨e⟩ := ChapterF.Source.DGS85.OriginalExtension.exists_original_unitaryFour_marking_of_reduced_iso
    (d.hypothesisF11 hi hH.1.1.2) m hm hmgt point r
  exact ⟨d.original_unitaryFour_residual_centralizer_eq_bot hi hH.1.1.2 hp m hm point e,
    d.original_unitaryFour_left_core_eq hi hH.1.1.2 hp m hm point e,
    d.original_unitaryFour_outer_index_one_or_two hi hH.1.1.2 hp m hm point e⟩

omit d hp e in
include D h hmany hn hpsl hH in
/-- The completed ordinary comparison feeds the actual prepared recognition,
while the degree-two action remains an explicit unfinished branch. -/
theorem rankOne_globalExit_or_original_unitaryFour_degree_two
    (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (e : Global.OriginalUnitaryFour.Marking m hm point L (residual H) (Global.sourceS L H)) :
    RankOneModule.GlobalExit G ∨
      ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2 := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  rcases d.original_unitaryFour_comparison_or_degree_two hi hH.1.1.2 hp m hm point e with hc | hc
  · exact Or.inl (D.rankOne_globalExit_of_unitaryFour h hmany hn hpsl hH d hp m hm
      (Or.inl (Or.inr hc)))
  · exact Or.inr hc.1

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
