module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.Projection
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.ProjectiveFixer.Candidate
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.ProjectiveFixer.MatrixFixing
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.ProjectiveFixer.StandardForms
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

/-!
# Transport of the projective pointwise-fixer calculation

Conjugating a subgroup by a standard projective automorphism conjugates its
pointwise fixer inside the same standard subgroup. Sylow conjugacy therefore
identifies the cardinality of the fixer of the faithfully projected residual
with that of the concrete diagonal-and-cycle subgroup in `Model`.

`Candidate` constructs a pointwise-fixing subgroup of order dividing eighteen.
`StandardForms` covers the standard subgroup by linear/field/graph forms, and
`MatrixFixing` places every form fixing the diagonal factor and the cycle in
the candidate. Together they identify the model's pointwise fixer exactly.
The resulting bound for the projected residual requires only the supplied
identification of the intrinsic residual with E₉. The passage to the
central-cover centralizer remains with the residual-action consumer.

Source: Aschbacher--Smith 15.3.38, printed pp.1136--1137, manuscript of
1 March 2004. All fixers here are pointwise fixers, not setwise normalizers.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer

def fixer (P : Subgroup PSL) : Subgroup (MulAut PSL) :=
  PSL3.OuterSolvable.standard F ⊓ fixingSubgroup (MulAut PSL) (P : Set PSL)

theorem fixer_map (P : Subgroup PSL) (a : MulAut PSL)
    (ha : a ∈ PSL3.OuterSolvable.standard F) :
    (fixer P).map (MulAut.conj a).toMonoidHom = fixer (P.map a.toMonoidHom) := by
  rw [fixer, Subgroup.map_inf _ _ _ (MulAut.conj a).injective]
  have hstd : (PSL3.OuterSolvable.standard F).map (MulAut.conj a).toMonoidHom =
      PSL3.OuterSolvable.standard F :=
    mem_normalizer_iff_map_conj_eq.mp ((PSL3.OuterSolvable.standard F).le_normalizer ha)
  rw [hstd, SubMulAction.fixingSubgroup_map_conj_eq
    (show a • (P : Set PSL) = (P.map a.toMonoidHom : Set PSL) from rfl)]
  rfl

theorem fixer_card_map (P : Subgroup PSL) (a : MulAut PSL)
    (ha : a ∈ PSL3.OuterSolvable.standard F) :
    Nat.card (fixer (P.map a.toMonoidHom)) = Nat.card (fixer P) := by
  rw [← fixer_map P a ha, card_map_of_injective (MulAut.conj a).injective]

theorem sylow_fixer_card (P : Sylow 3 PSL) : Nat.card (fixer P) = Nat.card (fixer model) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL sylow P
  have hp : (P : Subgroup PSL) = model.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, sylow_coe]
    rfl
  rw [hp]
  apply fixer_card_map
  exact PSL3.OuterSolvable.inner_le_standard F ⟨g, rfl⟩

theorem candidate_le_fixer_model : candidate ≤ fixer model :=
  le_inf candidate_le_standard candidate_fixes_model

theorem model_fixer_le_candidate_of_standard_forms
    (hform : ∀ a ∈ PSL3.OuterSolvable.standard F,
      ∃ A σ t, a = standardForm A σ t)
    (hcalc : ∀ A σ t,
      (∀ u : Fˣ, standardForm A σ t (diagonal u) = diagonal u) →
      standardForm A σ t cycle = cycle → standardForm A σ t ∈ candidate) :
    fixer model ≤ candidate := by
  intro a ha
  obtain ⟨A, σ, t, rfl⟩ := hform a ha.1
  apply hcalc
  · intro u
    exact ha.2 ⟨diagonal u, diagonal_mem_model u⟩
  · exact ha.2 ⟨cycle, cycle_mem_model⟩

theorem model_fixer_eq_candidate_of_standard_forms
    (hform : ∀ a ∈ PSL3.OuterSolvable.standard F,
      ∃ A σ t, a = standardForm A σ t)
    (hcalc : ∀ A σ t,
      (∀ u : Fˣ, standardForm A σ t (diagonal u) = diagonal u) →
      standardForm A σ t cycle = cycle → standardForm A σ t ∈ candidate) :
    fixer model = candidate :=
  le_antisymm (model_fixer_le_candidate_of_standard_forms hform hcalc) candidate_le_fixer_model

/-- The standard pointwise fixer of the concrete Sylow E₉ is exactly the
image of its inner action and the graph-field involution. -/
theorem model_fixer_eq_candidate : fixer model = candidate :=
  model_fixer_eq_candidate_of_standard_forms exists_standardForm
    standardForm_mem_candidate_of_fixes

end ProjectiveFixer

variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]

theorem projectedResidualFixer_card_eq_model (c : FourCover L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine) :
    Nat.card (projectedResidualFixer c w) = Nat.card (ProjectiveFixer.fixer ProjectiveFixer.model) := by
  have h := ProjectiveFixer.sylow_fixer_card (projectedResidualSylow c w e)
  rw [projectedResidualSylow_coe] at h
  exact h

theorem projectedResidualFixer_card_dvd_of_standard_forms (c : FourCover L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine)
    (hform : ∀ a ∈ PSL3.OuterSolvable.standard F,
      ∃ A σ t, a = ProjectiveFixer.standardForm A σ t)
    (hcalc : ∀ A σ t,
      (∀ u : Fˣ, ProjectiveFixer.standardForm A σ t (ProjectiveFixer.diagonal u) =
        ProjectiveFixer.diagonal u) →
      ProjectiveFixer.standardForm A σ t ProjectiveFixer.cycle = ProjectiveFixer.cycle →
        ProjectiveFixer.standardForm A σ t ∈ ProjectiveFixer.candidate) :
    Nat.card (projectedResidualFixer c w) ∣ 18 := by
  rw [projectedResidualFixer_card_eq_model c w e]
  exact (card_dvd_of_le (ProjectiveFixer.model_fixer_le_candidate_of_standard_forms hform hcalc)).trans
    ProjectiveFixer.candidate_card_dvd

/-- The standard pointwise fixer of the faithfully projected E₉ residual
has order dividing eighteen. -/
theorem projectedResidualFixer_card_dvd (c : FourCover L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine) :
    Nat.card (projectedResidualFixer c w) ∣ 18 := by
  rw [projectedResidualFixer_card_eq_model c w e, ProjectiveFixer.model_fixer_eq_candidate]
  exact ProjectiveFixer.candidate_card_dvd

end Matrix.PSL3Four.ExtendedCentralizer
