module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourGraphAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalOriginalUnitaryFourGraphLift

/-!
# Full residual graph action in the original Chapter 12 U₄ extension

For every selected perfect R and broad original marking, the degree-two
branch gives an actual isomorphism from LS to the concrete plane residual
extended by its specified graph involution. It restricts to the same residual
coordinates on every element of L. Relative Sylow conjugacy places an actual
involution in the literal source S, retaining its full residual action and
the exact inner conjugating element in LS.

Reduced DGS restoration supplies the broad marking in the source application.
The prepared application combines this with completed ordinary recognition.
Both full endpoint maps and their entire Borel squares still need assembly;
this local join recognition does not prove the full amalgam comparison.
DGS exhaustion, prepared U₅, uniqueness and unconditional GlobalExit remain.
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

/-- The graph lift acts correctly on the entire original L in any specified
residual coordinates, not just on L/O₂(L). -/
theorem rankOne_global_original_unitaryFour_full_graph_action
    (a : L ≃* L2 m hm)
    (hi : ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2) :
    ∃ t : (L ⊔ Global.sourceS L H : Subgroup G), t.val ∉ L ∧ orderOf t.val=2 ∧
      ∀ x : L, (a.symm (Extension.L2Aut m hm (a x))).val=t.val*x.val*t.val⁻¹ :=
  d.original_unitaryFour_full_graph_action
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm point mark a hi

/-- Recognize the actual LS as the native plane graph extension, with the
residual map preserved on every element. No residual isomorphism is assumed. -/
theorem rankOne_global_original_unitaryFour_graph_extension
    (hi : ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2) :
    ∃ a : L ≃* L2 m hm,
    ∃ e : (L ⊔ Global.sourceS L H : Subgroup G) ≃* Global.OriginalUnitaryFour.PlaneGraphExtension m hm,
      ∀ x : L, e (inclusion le_sup_left x)=SemidirectProduct.inl (a x) := by
  let hi' := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨_,⟨a⟩,_,_⟩ := d.original_unitaryFour_factors hi' hH.1.1.2 hp m hm point mark
  exact ⟨a,d.originalUnitaryFourGraphExtensionEquiv hi' hH.1.1.2 hp m hm point mark a hi,
    d.originalUnitaryFourGraphExtensionEquiv_left hi' hH.1.1.2 hp m hm point mark a hi⟩

/-- The actual S-involution retains its full residual graph action through
the same LS conjugating element, without identifying S with the ambient T. -/
theorem rankOne_global_original_unitaryFour_source_full_graph_involution
    (a : L ≃* L2 m hm)
    (hi : ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2) :
    ∃ t : Global.sourceS L H, t.val ∉ L ∧ orderOf t.val=2 ∧
      ∃ c : (L ⊔ Global.sourceS L H : Subgroup G),
        Global.Preparation.originalUnitaryFourResidualAction
          (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 m hm a (inclusion le_sup_right t) =
          Global.Preparation.originalUnitaryFourResidualAction
            (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 m hm a c * Extension.L2Aut m hm *
              (Global.Preparation.originalUnitaryFourResidualAction
                (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 m hm a c)⁻¹ :=
  d.original_unitaryFour_source_full_graph_involution
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm point mark a hi

/-- The constructed equivalence also retains the actual source-S involution
and its full conjugate graph image in the same concrete carrier. -/
theorem rankOne_global_original_unitaryFour_graph_source_image
    (a : L ≃* L2 m hm)
    (hi : ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2) :
    let hi' := D.rankOne_generic_input_of_many h hmany hn hpsl
    let e := d.originalUnitaryFourGraphExtensionEquiv hi' hH.1.1.2 hp m hm point mark a hi
    ∃ t : Global.sourceS L H, t.val ∉ L ∧ orderOf t.val=2 ∧
      ∃ c : (L ⊔ Global.sourceS L H : Subgroup G),
        e (inclusion le_sup_right t) = e c *
          SemidirectProduct.inr Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.generator * (e c)⁻¹ :=
  d.originalUnitaryFourGraphExtensionEquiv_source_graph
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm point mark a hi

omit mark in
include D h hmany hn hpsl hH d hp in
/-- Genuine reduced DGS recognition restores the broad marking and gives
the concrete full-residual graph extension of the same original LS. -/
theorem rankOne_global_graph_extension_of_reduced_unitaryFour
    (hmgt : 1 < m)
    (r : RankTwoAmalgam.Iso
      (ChapterF.Source.DGS85.OriginalExtension.reducedAmalgam ![L,R] (Global.sourceS L H))
      (ChapterF.Source.DGS85.OriginalExtension.UnitaryFourNative.amalgam m hm point))
    (hi : ((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2) :
    ∃ a : L ≃* L2 m hm,
    ∃ e : (L ⊔ Global.sourceS L H : Subgroup G) ≃* Global.OriginalUnitaryFour.PlaneGraphExtension m hm,
      ∀ x : L, e (inclusion le_sup_left x)=SemidirectProduct.inl (a x) := by
  let hi' := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨mark⟩ := ChapterF.Source.DGS85.OriginalExtension.exists_original_unitaryFour_marking_of_reduced_iso
    (d.hypothesisF11 hi' hH.1.1.2) m hm hmgt point r
  exact D.rankOne_global_original_unitaryFour_graph_extension h hmany hn hpsl hH d hp m hm point mark hi

omit d hp mark in
include D h hmany hn hpsl hH in
/-- The prepared original branch either has its completed ordinary global
exit or the newly recognized concrete left graph extension. Both full Borel
squares remain required before applying the degree-two completion theorem. -/
theorem rankOne_globalExit_or_original_unitaryFour_graph_extension
    (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (mark : Global.OriginalUnitaryFour.Marking m hm point L (residual H) (Global.sourceS L H)) :
    RankOneModule.GlobalExit G ∨
      (((T : Subgroup G) ⊓ L).relIndex (Global.sourceS L H)=2 ∧
        ∃ a : L ≃* L2 m hm,
        ∃ e : (L ⊔ Global.sourceS L H : Subgroup G) ≃* Global.OriginalUnitaryFour.PlaneGraphExtension m hm,
          ∀ x : L, e (inclusion le_sup_left x)=SemidirectProduct.inl (a x)) := by
  rcases D.rankOne_globalExit_or_original_unitaryFour_degree_two h hmany hn hpsl hH
    m hm point d hp mark with hx | hi
  · exact Or.inl hx
  · exact Or.inr ⟨hi,D.rankOne_global_original_unitaryFour_graph_extension
      h hmany hn hpsl hH d hp m hm point mark hi⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
