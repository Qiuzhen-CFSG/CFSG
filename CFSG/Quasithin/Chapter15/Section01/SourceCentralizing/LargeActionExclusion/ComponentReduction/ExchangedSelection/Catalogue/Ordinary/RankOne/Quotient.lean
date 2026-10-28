module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.QuotientModels
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Ordinary

/-!
# Quotient assembly from full ordinary source rows

The two excluded constructors retain their actual Borel equality and
proper-parabolic clauses. In the surviving rows the model isomorphisms
pass to the literal quotient L/O₂(L), using Z(L)=O₂(L) from the same
pre-exclusion witness. The exchanged-source application retains this
witness on the very same component.

These adapters do not prove the initial classification or its two row
exclusions. Those obligations remain with the ordinary catalogue and
ordinary rank-one owners. No 15.1.22 parabolic refinement is required.
Source: Aschbacher--Smith 15.1.20(3), 15.1.21, pp.1094--1098.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Eliminate the full source rows, retaining their Borel and parabolic hypotheses. -/
theorem Ordinary20Alternatives.postRankOneModel_of_row_exclusions
    {d : CaseIComponentData T M Mc V} (ha : d.Ordinary20Alternatives)
    (hc : center d.L = pCore 2 d.L)
    (hB : (IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) →
      d.ML = d.ordinaryBorel → False)
    (hH : d.OrdinaryHigherField → d.OrdinaryParabolic d.ML →
      (d.ML = d.ordinaryBorel ∨ IsCoatom (d.ML.subgroupOf d.L)) → False) :
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  have quotientModel {X : Type} [Group X] (e : d.L ≃* X)
      (hz : center X = ⊥) : Nonempty ((d.L ⧸ pCore 2 d.L) ≃* X) := by
    have he : (pCore 2 d.L).map e.toMonoidHom = ⊥ := by
      rw [← hc]
      apply bot_unique
      rintro _ ⟨x,hx,rfl⟩
      exact hz ▸ (centerCongr e ⟨x,hx⟩).property
    exact ⟨(QuotientGroup.congr _ ⊥ e he).trans QuotientGroup.quotientBot⟩
  cases ha with
  | rankOne hm hb => exact (hB hm hb).elim
  | higherField hm hp hb => exact (hH hm hp hb).elim
  | binaryRankTwo hm _ =>
      unfold OrdinaryBinaryRankTwo at hm
      rcases hm with hm | hm | hm <;> obtain ⟨e⟩ := hm
      · exact .inr (.inl (.inr (.inl (quotientModel e g2.1))))
      · exact .inr (.inl (.inr (.inr
          (quotientModel e (Facts.of_equiv Tits.parrottFiniteImageEquiv tits_facts).1))))
      · exact .inr (.inr (.inr (.inr (.inr (quotientModel e
          (Triality.Standard.binaryCarrier_center_eq_bot 1 Nat.zero_lt_one))))))
  | sporadic name hn3 hn4 hm _ =>
      cases name with
      | m11 => exact .inl (.inl hm)
      | m12 => exact .inl (.inr (.inl hm))
      | m22 => exact .inl (.inr (.inr (.inl hm)))
      | m23 => exact .inl (.inr (.inr (.inr (.inl hm))))
      | m24 => exact .inl (.inr (.inr (.inr (.inr (.inl hm)))))
      | j2 => exact .inl (.inr (.inr (.inr (.inr (.inr hm)))))
      | j3 => exact (hn3 rfl).elim
      | j4 => exact (hn4 rfl).elim
      | hs => exact .inr (.inr (.inl hm))
      | he => exact .inr (.inr (.inr (.inl hm)))
      | ru => exact .inr (.inr (.inr (.inr (.inl hm))))
  | linear n hn e _ _ =>
      obtain ⟨q⟩ := quotientModel e (Theory.SpecificGroups.BinaryComponentResidual.linear hn).1
      refine .inr (.inl (.inl ⟨n,hn,?_⟩))
      exact ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,
        ⟨q.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega)).symm⟩⟩

/-- The early quotient argument retains the pre-exclusion witness on the
same component selected by the exchanged-source argument. The initial
catalogue and the two full-row exclusions remain explicit obligations. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_rows
    {d : CaseIComponentData T M Mc V} (e : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hcatalogue : IsComponent d.G1 (d.L.subgroupOf d.G1) → d.Ordinary20Alternatives)
    (hB : IsComponent d.G1 (d.L.subgroupOf d.G1) →
      (IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) →
      d.ML = d.ordinaryBorel → False)
    (hH : IsComponent d.G1 (d.L.subgroupOf d.G1) →
      d.OrdinaryHigherField → d.OrdinaryParabolic d.ML →
      (d.ML = d.ordinaryBorel ∨ IsCoatom (d.ML.subgroupOf d.L)) → False) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) :=
  e.not_ordinary_of_post_rank_one_catalogue hG hM hu h (fun hL =>
    (hcatalogue hL).postRankOneModel_of_row_exclusions (s.ordinary hL).center_eq (hB hL) (hH hL))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
