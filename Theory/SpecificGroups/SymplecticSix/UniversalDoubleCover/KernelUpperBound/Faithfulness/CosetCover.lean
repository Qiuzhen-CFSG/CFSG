module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.Relators
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.Certificate.Checked
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.Certificate.Shape

/-!
# A checked 36-coset cover inside the Sp₆(2) presentation

The trace supplies actual subgroup-witness equations for multiplication of
every representative by a, a⁻¹, b and b⁻¹. Word induction then covers the
whole abstract presentation. The only remaining order input is finiteness
and a bound of 40320 for the actual subgroup ⟨a, bab³⟩.

Source: ATLAS `S62G1-P1.M`, M2; see `source/README.md` for the trace.
-/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness
open Subgroup.CosetWordCertificate Certificate

/-- Thirty-six representatives with certified transitions in the presented group. -/
def cosetCover : Subgroup.GeneratorCosetCover s8Subgroup generator (Fin 36) where
  repr i := definitions.repr traceGenerator (survivor i)
  initial := 0
  initial_eq := by change definitions.repr traceGenerator 0 = 1; simp
  step i a := by
    have h := all_hold certificate_valid _ (hlt i (a, true))
    rw [hshape] at h
    obtain ⟨z, hz⟩ := h
    refine ⟨z, dest i (a, true), ?_⟩
    cases a <;> simpa [eval_letter, embed, traceGenerator] using hz
  inv_step i a := by
    have h := all_hold certificate_valid _ (hlt i (a, false))
    rw [hshape] at h
    obtain ⟨z, hz⟩ := h
    refine ⟨z, dest i (a, false), ?_⟩
    cases a <;> simpa [eval_letter, embed, traceGenerator] using hz

/-- The actual consumer of the subgroup order bound, with finiteness retained. -/
theorem presented_finite_card_le_of_subgroup_bound
    (h : Finite s8Subgroup ∧ Nat.card s8Subgroup ≤ 40320) :
    Finite Presented ∧ Nat.card Presented ≤ 1451520 := by
  let : Finite s8Subgroup := h.1
  have hg : Subgroup.closure (Set.range generator) = ⊤ :=
    PresentedGroup.closure_range_of (Set.range KernelPresentation.relator)
  obtain ⟨hf, hb⟩ := cosetCover.finite_card_le hg
  refine ⟨hf, hb.trans ?_⟩
  simpa only [Nat.card_fin] using Nat.mul_le_mul_right 36 h.2

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness
