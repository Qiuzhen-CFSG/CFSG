module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourQuadraticQuotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalUnitaryFourCoreCollapse

/-!
# The exact quadratic quotient in the original Chapter 12 U₄ row

The index-two branch now has the actual quotient LS/O₂(LS), with its
canonical quadratic field action and the same original representatives.
The graph actor of the native plane quotient has an original representative
g outside L with g² in O₂(L). The order-two assertion is on its quotient
class; lifting it to an involution of the full original group remains a
separate calculation.

These applications retain every selected perfect R, the broad original
marking, either input orientation and q=4. Reduced DGS recognition restores
the marking. On the residual row the existing ordinary recognition leaves
only this exact quadratic quotient branch. The full graph amalgam, DGS
exhaustion, uniqueness and unconditional GlobalExit are still required.
Source: Aschbacher--Smith F.1.12, pp.263--264, 5.2.6--7, pp.650--651,
and Chapter 12, p.795 (`refs/quasithin.pdf`).
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

/-- The exact degree-two quotient, with the original L and outer S actions. -/
theorem rankOne_global_original_unitaryFour_quadratic_quotient
    (hi : ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2) :
    ∃ q : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group (MatrixField m),
    ∃ e : ((L ⊔ Global.sourceS L H : Subgroup G) ⧸
      pCore 2 (L ⊔ Global.sourceS L H : Subgroup G)) ≃*
        Global.OriginalUnitaryFour.quadraticQuotient m,
      (∀ l : L, (e (QuotientGroup.mk' (pCore 2 (L ⊔ Global.sourceS L H : Subgroup G))
        (inclusion le_sup_left l))).val = MulAut.conj (q (QuotientGroup.mk' (pCore 2 L) l))) ∧
      (∀ s : Global.sourceS L H, s.val ∉ L →
        Theory.PSL2.fieldProjection (MatrixField m)
          (e (QuotientGroup.mk' (pCore 2 (L ⊔ Global.sourceS L H : Subgroup G))
            (inclusion le_sup_right s))).val = fieldConj m) ∧
      ∃ g : (L ⊔ Global.sourceS L H : Subgroup G), g.val ∉ L ∧ g.val^2 ∈ L.pCoreIn 2 ∧
        (e (QuotientGroup.mk' (pCore 2 (L ⊔ Global.sourceS L H : Subgroup G)) g)).val =
          MulAut.congr (Global.OriginalUnitaryFour.planeQuotient m hm) (Extension.L2QuotientAut m hm) ∧
        orderOf (QuotientGroup.mk' (pCore 2 (L ⊔ Global.sourceS L H : Subgroup G)) g)=2 := by
  let hi' := D.rankOne_generic_input_of_many h hmany hn hpsl
  let q := d.originalUnitaryFourQuotientCoordinates hi' hH.1.1.2 hp m hm point mark
  let e := d.originalUnitaryFourQuadraticQuotientEquiv hi' hH.1.1.2 hp m hm point mark q hi
  refine ⟨q,e,d.originalUnitaryFourQuadraticQuotientEquiv_left hi' hH.1.1.2 hp m hm point mark q hi,
    d.originalUnitaryFourQuadraticQuotientEquiv_outer hi' hH.1.1.2 hp m hm point mark q hi,?_⟩
  obtain ⟨g,hg,hsq,hact,ho⟩ := d.original_unitaryFour_graph_quotient_lift hi' hH.1.1.2 hp m hm point mark q hi
  refine ⟨g,hg,hsq,?_,ho⟩
  exact (d.originalUnitaryFourQuadraticQuotientEquiv_mk hi' hH.1.1.2 hp m hm point mark q hi g).trans hact

omit mark in
include D h hmany hn hpsl hH d hp in
/-- The genuine reduced DGS marking supplies the quadratic quotient in
its original index-two branch, without a graph-comparison premise. -/
theorem rankOne_global_quadratic_quotient_of_reduced_unitaryFour
    (hmgt : 1 < m)
    (r : RankTwoAmalgam.Iso
      (ChapterF.Source.DGS85.OriginalExtension.reducedAmalgam ![L,R] (Global.sourceS L H))
      (ChapterF.Source.DGS85.OriginalExtension.UnitaryFourNative.amalgam m hm point))
    (hi : ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2) :
    Nonempty (((L ⊔ Global.sourceS L H : Subgroup G) ⧸
      pCore 2 (L ⊔ Global.sourceS L H : Subgroup G)) ≃*
        Global.OriginalUnitaryFour.quadraticQuotient m) := by
  let hi' := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨mark⟩ := ChapterF.Source.DGS85.OriginalExtension.exists_original_unitaryFour_marking_of_reduced_iso
    (d.hypothesisF11 hi' hH.1.1.2) m hm hmgt point r
  obtain ⟨q,e,_⟩ := D.rankOne_global_original_unitaryFour_quadratic_quotient
    h hmany hn hpsl hH d hp m hm point mark hi
  exact ⟨e⟩

omit d hp mark in
include D h hmany hn hpsl hH in
/-- Prepared ordinary recognition leaves only the constructed original
quadratic quotient and its genuine outer quotient involution. -/
theorem rankOne_globalExit_or_original_unitaryFour_quadratic_quotient
    (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (mark : Global.OriginalUnitaryFour.Marking m hm point L (residual H) (Global.sourceS L H)) :
    RankOneModule.GlobalExit G ∨
      (((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2 ∧
        ∃ e : ((L ⊔ Global.sourceS L H : Subgroup G) ⧸
          pCore 2 (L ⊔ Global.sourceS L H : Subgroup G)) ≃*
            Global.OriginalUnitaryFour.quadraticQuotient m,
        ∃ g : (L ⊔ Global.sourceS L H : Subgroup G), g.val ∉ L ∧ g.val^2 ∈ L.pCoreIn 2 ∧
          (e (QuotientGroup.mk' (pCore 2 (L ⊔ Global.sourceS L H : Subgroup G)) g)).val =
            MulAut.congr (Global.OriginalUnitaryFour.planeQuotient m hm) (Extension.L2QuotientAut m hm) ∧
          orderOf (QuotientGroup.mk' (pCore 2 (L ⊔ Global.sourceS L H : Subgroup G)) g)=2) := by
  rcases D.rankOne_globalExit_or_original_unitaryFour_degree_two h hmany hn hpsl hH
    m hm point d hp mark with hx | hi
  · exact Or.inl hx
  · obtain ⟨q,e,_,_,g,hg⟩ := D.rankOne_global_original_unitaryFour_quadratic_quotient
      h hmany hn hpsl hH d hp m hm point mark hi
    exact Or.inr ⟨hi,e,g,hg⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
