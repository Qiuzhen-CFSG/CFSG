module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourGraphRigidity
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalUnitaryFourSplitPair

/-!
# The native ambient graph involution in the original Chapter 12 pair

The plane residual now detects the entire native automorphism: its fixed
point radical recovers the opposite parabolic, perfectness determines that
residual, and the source Borel generators determine the whole carrier.
The actual source involution therefore induces the specified ambient graph
involution up to the retained original LS conjugator. Its full split pair
preserves both endpoint and full-overlap inclusion squares.

Reduced DGS recognition still supplies the broad marking. Identifying this
split pair with the fixed catalogue extension, DGS exhaustion, prepared U₅,
uniqueness and unconditional GlobalExit remain with the original assembly.
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

/-- The original chosen-module pair has the full split comparison and the
same ambient conjugate graph involution, for every selected perfect R. -/
theorem rankOne_global_original_unitaryFour_ambient_graph_pair
    (hi : ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2) :
    let input := D.rankOne_generic_input_of_many h hmany hn hpsl
    ∃ (t : Global.sourceS L H) (hout : t.val ∉ L) (ht : orderOf t.val=2),
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))
        (RankTwoAmalgam.semidirect
          (d.originalUnitaryFourNativePairAction input hH.1.1.2 hp m hm point mark hi t hout ht))) ∧
      ∃ c : (L ⊔ Global.sourceS L H : Subgroup G),
        mark.sylowHom t=mark.left (inclusion le_sup_left c) * Extension.projectiveAut m hm *
          (mark.left (inclusion le_sup_left c))⁻¹ :=
  d.original_unitaryFour_ambient_graph_split_pair
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm point mark hi

omit mark in
include D h hmany hn hpsl hH d hp in
/-- Genuine reduced DGS restoration supplies the original marking used by
the ambient graph identification; no graph-action premise is added. -/
theorem rankOne_global_ambient_graph_pair_of_reduced_unitaryFour
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
          (d.originalUnitaryFourNativePairAction input hH.1.1.2 hp m hm point mark hi t hout ht))) ∧
      ∃ c : (L ⊔ Global.sourceS L H : Subgroup G),
        mark.sylowHom t=mark.left (inclusion le_sup_left c) * Extension.projectiveAut m hm *
          (mark.left (inclusion le_sup_left c))⁻¹ := by
  let input := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨mark⟩ := ChapterF.Source.DGS85.OriginalExtension.exists_original_unitaryFour_marking_of_reduced_iso
    (d.hypothesisF11 input hH.1.1.2) m hm hmgt point r
  exact ⟨mark,D.rankOne_global_original_unitaryFour_ambient_graph_pair
    h hmany hn hpsl hH d hp m hm point mark hi⟩

omit d hp mark in
include D h hmany hn hpsl hH in
/-- The completed ordinary exit and the identified ambient graph action
cover both original extension indices in the prepared Chapter 12 row. -/
theorem rankOne_globalExit_or_original_unitaryFour_ambient_graph_pair
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
            (d.originalUnitaryFourNativePairAction input hH.1.1.2 hp m hm point mark hi t hout ht))) ∧
        ∃ c : (L ⊔ Global.sourceS L H : Subgroup G),
          mark.sylowHom t=mark.left (inclusion le_sup_left c) * Extension.projectiveAut m hm *
            (mark.left (inclusion le_sup_left c))⁻¹ := by
  rcases D.rankOne_globalExit_or_original_unitaryFour_degree_two h hmany hn hpsl hH
    m hm point d hp mark with hx | hi
  · exact Or.inl hx
  · exact Or.inr ⟨hi,D.rankOne_global_original_unitaryFour_ambient_graph_pair
      h hmany hn hpsl hH d hp m hm point mark hi⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
