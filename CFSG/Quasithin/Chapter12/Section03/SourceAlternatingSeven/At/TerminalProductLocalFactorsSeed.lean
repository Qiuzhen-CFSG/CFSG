module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsSeed
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentAmbientUniqueness
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductLocalFactorsOmega
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductSeed

/-!
# TerminalProductLocalFactorsSeed at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalProductLocalFactorsSeed`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

open scoped commutatorElement

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

theorem exists_weight_two_in_Le_commutator_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    ∃ v : V, v ≠ 1 ∧ weight (D.model.coordinates v).toAdd.val = 2 ∧
      (v : G) ∈ ⁅P.Z,P.Le⁆ := by
  obtain ⟨f,hf,hfT⟩ := D.naturalCoordinates_at.central_representative_weight_at structural
    (n := 6) (Or.inr (Or.inr rfl))
  have hfZ : (f : G) ∈ P.Z := by
    let := S.chosen.elementary
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨S.chosen.le_sylow f.property,hfT,
      elemPow_eq_one_of_isElementaryAbelian _ f.property⟩
  obtain ⟨v,hv,hvw,hvm⟩ := P.exists_weight_two_in_cyclic_Le_commutator f hf
  exact ⟨v,hv,hvw,commutator_mono (zpowers_le.mpr hfZ) le_rfl hvm⟩

theorem Le_commutator_centralizer_le_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    centralizer (⁅P.Z,P.Le⁆ : Subgroup G) ≤ normalizer (L : Set G) := by
  obtain ⟨v,hv,hvw,hvm⟩ := P.exists_weight_two_in_Le_commutator_at structural
  exact (centralizer_le (Set.singleton_subset_iff.mpr hvm)).trans
    (D.pointCentralizers v hv (Or.inl hvw))

theorem residual_not_centralizes_Le_commutator_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    ¬ P.K ≤ centralizer (⁅P.Z,P.Le⁆ : Subgroup G) := by
  intro h
  exact P.residual_escape_at structural (h.trans (P.Le_commutator_centralizer_le_at structural))

theorem exists_weight_two_in_L2_commutator_of_product_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (C : P.ComponentAnalysis) (hproduct : P.Le = P.L1 ⊔ P.L2) :
    ∃ v : V, v ≠ 1 ∧ weight (D.model.coordinates v).toAdd.val = 2 ∧
      (v : G) ∈ ⁅P.Z,P.L2⁆ := by
  simpa only [P.Le_commutator_eq_L2_of_product C hproduct] using
    P.exists_weight_two_in_Le_commutator_at structural

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

