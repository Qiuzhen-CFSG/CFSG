module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Source
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Rejection
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Exterior
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Separation.Quadratic

/-!
# Concrete quadratic separation of the square span

The original W-combination is transported by the exact published adapted basis
and restricts to the literal test form. The first 44 separating functionals
annihilate the complete restriction and quadratic spaces. Their checked linear
evaluations reconstruct every square-span element modulo the top-operator
line, by span induction. Vanishing of those evaluations therefore leaves only
that line. A final functional annihilates all source forms and detects the
actual top linear term, rejecting it modulo the restriction space.

Source: KernelBound/source/README.md and kernel-restriction.json.
-/

public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity
open Coordinates SeparationCertificate

attribute [local irreducible] squareBasis testForm topOperator weights survivor

/-- The checked evaluations reconstruct every square-span element up to the
top line, without assuming independence or a dimension calculation. -/
private theorem square_reconstruction (D : HalfMatrix) (hD : D ∈ squareSpan) :
    ∃ a : ZMod 2, D =
      (∑ k : Fin 44, functional (weights.get k.castSucc) (linearTerm testForm D) •
        squareBasis k.castSucc) + a • topOperator := by
  induction hD using Submodule.span_induction with
  | mem D hD =>
    obtain ⟨i, rfl⟩ := hD
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine ⟨1, ?_⟩
      simp only [linear_evaluation, Fin.val_last, lt_self_iff_false, if_false, one_smul]
      rw [show Fin.last 44 = (44 : Fin 45) from rfl]
      exact survivor_relation.symm
    · refine ⟨0, ?_⟩
      simp [linear_evaluation, i.isLt, ← Fin.ext_iff]
  | zero =>
    exact ⟨0, by simp only [map_zero, zero_smul, Finset.sum_const_zero, add_zero]⟩
  | add D E hD hE ihD ihE =>
    obtain ⟨a, ha⟩ := ihD
    obtain ⟨b, hb⟩ := ihE
    refine ⟨a + b, ?_⟩
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    calc
      D + E = _ := congrArg₂ (· + ·) ha hb
      _ = _ := by abel
  | smul a D hD ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨a * b, ?_⟩
    simpa only [map_smul, smul_add, Finset.smul_sum, smul_smul, smul_eq_mul]
      using congrArg (a • ·) hb

/-- The exact test form comes from the complete transported exterior space. -/
theorem testForm_mem_restrictionSpace : testForm ∈ Coordinates.restrictionSpace :=
  SeparationCertificate.testForm_mem

/-- Modulo the complete restriction and quadratic spaces, the only square-span
direction with vanishing linear term is the top-operator line. -/
theorem linearTerm_mem_sup_implies_top (D : Coordinates.HalfMatrix) (hD : D ∈ squareSpan)
    (hL : linearTerm testForm D ∈ Coordinates.restrictionSpace ⊔
      quadraticSpan testForm squareBasis) : ∃ a : ZMod 2, D = a • topOperator := by
  have hz (k : Fin 44) : functional (weights.get k.castSucc) (linearTerm testForm D) = 0 := by
    obtain ⟨R, hR, Q, hQ, hRQ⟩ := Submodule.mem_sup.mp hL
    rw [← hRQ, map_add, restriction_annihilated k hR, quadratic_annihilated k hQ, add_zero]
  obtain ⟨a, ha⟩ := square_reconstruction D hD
  refine ⟨a, ?_⟩
  simpa only [hz, zero_smul, Finset.sum_const_zero, zero_add] using ha

/-- The nonzero top direction is rejected modulo the actual restriction space. -/
theorem topOperator_linearTerm_not_mem :
    linearTerm testForm topOperator ∉ Coordinates.restrictionSpace :=
  SeparationCertificate.top_rejected

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity
