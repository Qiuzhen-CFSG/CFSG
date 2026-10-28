module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourGraphLift
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalUnitaryFourQuadraticQuotient

/-!
# Original Chapter 12 involutions in the degree-two U₄ branch

Hermitian H¹ now lifts the canonical graph quotient actor to an actual
involution of the original LS. It splits LS over L and, after conjugation
inside that same LS, splits the original S over T∩L. The quotient action and
its conjugating element are retained, as are arbitrary selected perfect R,
the broad original marking, either input orientation and q=4.

The reduced DGS consumer restores that marking. On the prepared residual
row, completed ordinary recognition leaves this actual split degree-two
branch. Matching the full residual action and constructing the full graph
amalgam with both Borel squares remain necessary, as do DGS exhaustion,
uniqueness and unconditional GlobalExit.
Source: Aschbacher--Smith F.1.12, pp.263--264, I.1.6(3), p.408,
5.2.6--7, pp.650--651, and Chapter 12, p.795 (`refs/quasithin.pdf`).
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

/-- Every involution in the actual left two-core quotient lifts in the
same original LS, with its literal quotient class unchanged. -/
theorem rankOne_global_original_unitaryFour_involution_lifts
    (x : (L ⊔ Global.sourceS L H : Subgroup G) ⧸
      pCore 2 (L ⊔ Global.sourceS L H : Subgroup G)) (hx : orderOf x=2) :
    ∃ t : (L ⊔ Global.sourceS L H : Subgroup G), orderOf t.val=2 ∧
      QuotientGroup.mk' (pCore 2 (L ⊔ Global.sourceS L H : Subgroup G)) t=x :=
  d.original_unitaryFour_quotient_involution_lifts
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm point mark x hx

/-- The canonical graph quotient involution gives an actual complement
to L in the original LS, without assuming a graph-extension comparison. -/
theorem rankOne_global_original_unitaryFour_left_split
    (hi : ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2) :
    ∃ q : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group (MatrixField m),
    ∃ t : (L ⊔ Global.sourceS L H : Subgroup G), orderOf t.val=2 ∧
      (L.subgroupOf (L ⊔ Global.sourceS L H)).IsComplement' (zpowers t) ∧
      Global.Preparation.originalUnitaryFourJoinAction
        (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 m q t =
          MulAut.congr (Global.OriginalUnitaryFour.planeQuotient m hm) (Extension.L2QuotientAut m hm) := by
  let hi' := D.rankOne_generic_input_of_many h hmany hn hpsl
  let q := d.originalUnitaryFourQuotientCoordinates hi' hH.1.1.2 hp m hm point mark
  exact ⟨q,d.original_unitaryFour_left_split hi' hH.1.1.2 hp m hm point mark q hi⟩

/-- The original S splits over its own inner Sylow; no equality S=T
or identification of the selected R with the residual of H is used. -/
theorem rankOne_global_original_unitaryFour_source_split
    (hi : ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2) :
    ∃ t : Global.sourceS L H, orderOf t.val=2 ∧
      (((T : Subgroup G) ⊓ L).subgroupOf (Global.sourceS L H)).IsComplement' (zpowers t) :=
  d.original_unitaryFour_source_split
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm point mark hi

omit mark in
include D h hmany hn hpsl hH d hp in
/-- Genuine reduced DGS data supply the same original Sylow splitting
after restoration of the entire broad marking. -/
theorem rankOne_global_source_split_of_reduced_unitaryFour
    (hmgt : 1 < m)
    (r : RankTwoAmalgam.Iso
      (ChapterF.Source.DGS85.OriginalExtension.reducedAmalgam ![L,R] (Global.sourceS L H))
      (ChapterF.Source.DGS85.OriginalExtension.UnitaryFourNative.amalgam m hm point))
    (hi : ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2) :
    ∃ t : Global.sourceS L H, orderOf t.val=2 ∧
      (((T : Subgroup G) ⊓ L).subgroupOf (Global.sourceS L H)).IsComplement' (zpowers t) := by
  let hi' := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨mark⟩ := ChapterF.Source.DGS85.OriginalExtension.exists_original_unitaryFour_marking_of_reduced_iso
    (d.hypothesisF11 hi' hH.1.1.2) m hm hmgt point r
  exact D.rankOne_global_original_unitaryFour_source_split h hmany hn hpsl hH d hp m hm point mark hi

omit d hp mark in
include D h hmany hn hpsl hH in
/-- Completed ordinary recognition leaves an actual split degree-two
original S; this does not yet identify its full graph amalgam. -/
theorem rankOne_globalExit_or_original_unitaryFour_source_split
    (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (mark : Global.OriginalUnitaryFour.Marking m hm point L (residual H) (Global.sourceS L H)) :
    RankOneModule.GlobalExit G ∨
      (((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2 ∧
        ∃ t : Global.sourceS L H, orderOf t.val=2 ∧
          (((T : Subgroup G) ⊓ L).subgroupOf (Global.sourceS L H)).IsComplement' (zpowers t)) := by
  rcases D.rankOne_globalExit_or_original_unitaryFour_degree_two h hmany hn hpsl hH
    m hm point d hp mark with hx | hi
  · exact Or.inl hx
  · exact Or.inr ⟨hi,D.rankOne_global_original_unitaryFour_source_split
      h hmany hn hpsl hH d hp m hm point mark hi⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
