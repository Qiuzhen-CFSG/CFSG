module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSpanRecognition
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Refinement
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan

/-!
# The dual-natural commutator span in the central branch

In case (i) of 14.7.20(2), R ≤ C_H(U) and U ∩ R = E imply [R,L₁] ≤ E.
Thus E/V is an irreducible noncentral plane and R/E is central for L₁.
Refine the central upper interval to an actual chief series; exactly one
factor is noncentral. The five proved model counts exclude all but the
natural module in the switched marking. Undoing that marking gives an
explicit equivalence with the dual of the original natural L-action.

The final original-group application strengthens the existing centralizer
alternatives by this recognition. The faithful order-64 branch keeps its
exact kernel and both central flanks; its further reduction remains open.
Source: Aschbacher–Smith 14.7.23(1), printed pp.1050–1051,
refs/quasithin.pdf. Structural1222, Theorem12213 and the earlier faithful
classification retain their existing producers and final discharge with
qt-d-14775-source.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

open BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- In the central alternative of 14.7.20(2), the actual E/V plane is the
only noncentral L₁-chief factor on R/V. -/
theorem extraspecial_span_count_one_of_central
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W}
    (s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
      (conjugateSpanBy ⁅F.U,Q T L⁆ L) V ρ) :
    HasCount (ρ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
      (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) 1 := by
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let j : F.Li L 1 →* (L ⊔ (T : Subgroup G) : Subgroup G) :=
    inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
  let : Finite W := Finite.of_surjective (fun r => (s.coordinates r).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨c,hs,_,_,_,_,_,_,_,_,_,_,hRC,_,hinter,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  have hcomm : ⁅F.Li L 1,R⁆ ≤ ⁅F.U,Q T L⁆ := by
    rw [←hinter]
    apply le_inf
    · rw [commutator_comm]
      exact (commutator_mono (hRC.trans inf_le_right) (pointResidual_le F)).trans hc
    · exact le_normalizer_iff_commutator_le_right.mp
        ((((F.Li_le L 1).trans inf_le_left).trans le_sup_left).trans s.normalized)
  obtain ⟨D,hD,hirr⟩ := extraspecial_span_plane_irreducible h hab structural previous faithful he s
  have hatom : IsAtom D := (Subrepresentation.irreducible_iff_isAtom D).mp hirr
  have hupper : Central D ⊤ := by
    intro a w _
    change ρ (j a) w - w ∈ D.toSubmodule
    rw [hD]
    apply s.imageSpace_mono hcomm
    rw [s.imageSpace_commutator (F.Li L 1) R
      (((F.Li_le L 1).trans inf_le_left).trans le_sup_left) le_rfl,
      s.imageSpace_self]
    exact Submodule.subset_span ⟨j a,a.property,w,Submodule.mem_top,rfl⟩
  have hlower : ¬ Central ⊥ D := by
    intro htriv
    obtain ⟨a,ha,hn⟩ := extraspecial_span_plane_cubic_norm h hab structural previous he s
    apply hatom.ne_bot
    apply le_antisymm _ bot_le
    intro w hw
    have hfix : ρ a w = w := sub_eq_zero.mp (htriv ⟨a,ha⟩ w hw)
    have hh := hn w (hD ▸ hw)
    rw [hfix,hfix] at hh
    have hww : w+w=0 := by
      calc w+w = (2 : ZMod 2) • w := (two_smul (ZMod 2) w).symm
           _ = 0 := by simp
    change w = 0
    simpa only [hww,zero_add] using hh
  simpa only [HasCount,Nat.add_zero] using
    exists_series_count_join
      (exists_noncentral_chief_series ⊥ D (bot_covBy_iff.mpr hatom) hlower)
      (exists_central_series D ⊤ le_top hupper)

open BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- The central branch of 14.7.23 identifies the actual R/V with the dual
of the original natural action, through the original quotient map on L. -/
theorem extraspecial_span_dual_of_central
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
      (_s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
        (conjugateSpanBy ⁅F.U,Q T L⁆ L) V ρ),
      (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker ∧
      Nonempty (Representation.Equiv (ρ.comp (inclusion le_sup_left))
        (BinaryLinearThree.W.dual.comp (SpanMarking.qL h))) ∧
      HasCount (ρ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
        (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) 1 := by
  obtain ⟨W,ha,hm,ρ,s,e,σ,hker,hσ,_,hP,⟨ed⟩,hclass,_⟩ :=
    extraspecial_span_module_alternatives h hab structural previous faithful he
  have hcount := extraspecial_span_count_one_of_central h hab structural previous faithful he hc s
  let q := e.symm.toMonoidHom.comp (SpanMarking.qL h)
  have hnat : Nonempty (σ.Equiv BinaryLinearThree.W) := by
    rcases extraspecial_span_counted_alternatives q hP σ hσ hclass with hh | hh | hh | hh | hh
    · exact hh.1
    all_goals have := hcount.unique hh.2; omega
  obtain ⟨en⟩ := hnat
  refine ⟨W,ha,hm,ρ,s,hker,?_,hcount⟩
  rw [←hσ]
  exact ⟨(restrictEquiv en q).trans (restrictEquiv ed (SpanMarking.qL h))⟩

open NoncentralChiefRefinement BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- Original-group application: the centralizer alternatives now carry the
proved dual-natural R/V recognition in the central case. The faithful
order-64 interval retains its exact kernel and both central flanks. -/
theorem extraspecial_span_central_or_faithful
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ((F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2) ∧
      ((⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∧
        ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
          (ρ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) W)
          (_s : BinaryConjugationSection (L ⊔ (T : Subgroup G))
            (conjugateSpanBy ⁅F.U,Q T L⁆ L) V ρ),
          (Q T L).subgroupOf (L ⊔ (T : Subgroup G)) ≤ ρ.ker ∧
          Nonempty (Representation.Equiv (ρ.comp (inclusion le_sup_left))
            (BinaryLinearThree.W.dual.comp (SpanMarking.qL h))) ∧
          HasCount (ρ.comp (inclusion (((F.Li_le L 1).trans inf_le_left).trans
            (le_sup_left : L ≤ L ⊔ (T : Subgroup G))))) 1) ∨
        ∃ N B : NormalNode F.H, N ⋖ B ∧
          F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
          ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
          Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U) := by
  obtain ⟨hp,hc | hf⟩ := extraspecial_centralizer_core_reduction_no_small_intervals
    h hab structural previous faithful he
  · exact ⟨hp,Or.inl ⟨hc,extraspecial_span_dual_of_central h hab structural previous faithful he hc⟩⟩
  · exact ⟨hp,Or.inr hf⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
