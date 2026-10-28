module

public import Theory.SpecificGroups.ReeTwo.FixingModelFirstCoreBasic

/-!
# Reducing forty marked models to four

Powers of the order-five action conjugate the twenty census actions in four
orbits of length five. Replacing the cyclic actor by root 2 times that actor
pairs these orbits, while preserving its fourth power. Thus every model is
marked-isomorphic to the model for action 0 or action 2, with the same Boolean
fourth-power parameter. The root-table certificates are kernel checked.

Source: direct calculation in `FixingActionRepresentatives` and the marked
coordinate changes in `CyclicFourFixingTransport`.
-/

@[expose] public section
namespace ReeTwo.FixingModel
open Core Core.CensusPacked Core.FixingActionCensus

/-- Which of the two base models is needed. -/
def baseIndex (i : Fin 20) : Fin 20 :=
  ![0,0,2,0,2,0,2,2,2,0,0,0,2,0,2,0,2,2,2,0] i

/-- The representative before conjugation by a power of `c`. -/
def intermediateIndex (i : Fin 20) : Fin 20 :=
  ![0,0,2,3,2,3,18,2,18,3,3,3,2,0,18,0,2,18,18,0] i

/-- The required conjugating power of `c`. -/
def conjugatingPower (i : Fin 20) : Fin 5 :=
  ![0,4,0,0,3,2,2,2,1,1,4,3,1,2,4,3,4,3,0,1] i

private theorem baseIndex_cases (i : Fin 20) : baseIndex i = 0 ∨ baseIndex i = 2 :=
  (by decide +kernel : ∀ i : Fin 20, baseIndex i = 0 ∨ baseIndex i = 2) i

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem intertwine_codes : ∀ (i : Fin 20) (j : CoreRoot),
    (cAct^[ (conjugatingPower i).val ]) (representativeCodes (intermediateIndex i) j) =
      act (representativeCodes i) ((cAct^[ (conjugatingPower i).val ]) (code (root j))) := by
  decide +kernel

/-- The checked conjugating power intertwines the two actions. -/
theorem intertwine (i : Fin 20) (q : Core) :
    (c ^ (conjugatingPower i).val) (representative (intermediateIndex i) q) =
      representative i ((c ^ (conjugatingPower i).val) q) := by
  have h : (c ^ (conjugatingPower i).val) * representative (intermediateIndex i) =
      representative i * (c ^ (conjugatingPower i).val) := by
    apply Core.aut_ext
    intro j
    apply code_injective
    change code ((c ^ (conjugatingPower i).val) (representative (intermediateIndex i) (root j))) =
      code (representative i ((c ^ (conjugatingPower i).val) (root j)))
    rw [← cAct_iterate_code, representative_root, representativeRoots_code,
      representative_apply, representativeMap_code, ← cAct_iterate_code]
    exact intertwine_codes i j
  exact DFunLike.congr_fun h q

private theorem inner_shift (i j : Fin 20)
    (h : ∀ k : CoreRoot, representativeRoots j k =
      root 2 * representativeRoots i k * (root 2)⁻¹) (q : Core) :
    representative j q = root 2 * representative i q * (root 2)⁻¹ := by
  have he : representative j = (MulAut.conj (root 2)) * representative i := by
    apply Core.aut_ext
    intro k
    simpa only [MulAut.mul_apply, MulAut.conj_apply, representative_root] using h k
  exact DFunLike.congr_fun he q

/-- The two representatives 0 and 3 differ only by an actor change. -/
theorem shift_zero (q : Core) :
    representative 3 q = root 2 * representative 0 q * (root 2)⁻¹ :=
  inner_shift 0 3 (by decide +kernel) q

/-- The two representatives 2 and 18 differ only by an actor change. -/
theorem shift_two (q : Core) :
    representative 18 q = root 2 * representative 2 q * (root 2)⁻¹ :=
  inner_shift 2 18 (by decide +kernel) q

private theorem intermediate_cases (i : Fin 20) :
    (intermediateIndex i = baseIndex i) ∨
    (intermediateIndex i = 3 ∧ baseIndex i = 0) ∨
    (intermediateIndex i = 18 ∧ baseIndex i = 2) :=
  (by decide +kernel : ∀ i : Fin 20,
    (intermediateIndex i = baseIndex i) ∨
    (intermediateIndex i = 3 ∧ baseIndex i = 0) ∨
    (intermediateIndex i = 18 ∧ baseIndex i = 2)) i

/-- Each census model is marked-isomorphic to one of the two base actions,
without changing the split or nonsplit parameter. -/
theorem exists_marked_base_equiv (i : Fin 20) (ε : Bool) :
    ∃ e : Model i ε ≃* Model (baseIndex i) ε,
      e (mark i ε) = mark (baseIndex i) ε := by
  let f : Model (intermediateIndex i) ε ≃* Model i ε :=
    CyclicFourCentralExtension.congr (c ^ (conjugatingPower i).val) (intertwine i)
  have hf : f (mark (intermediateIndex i) ε) = mark i ε :=
    CyclicFourCentralExtension.congr_root_nine ..
  have hfs : f.symm (mark i ε) = mark (intermediateIndex i) ε := by
    rw [← hf, f.symm_apply_apply]
  suffices h : ∃ g : Model (intermediateIndex i) ε ≃* Model (baseIndex i) ε,
      g (mark (intermediateIndex i) ε) = mark (baseIndex i) ε by
    obtain ⟨g, hg⟩ := h
    exact ⟨f.symm.trans g, by simpa only [MulEquiv.trans_apply, hfs] using hg⟩
  rcases intermediate_cases i with h | ⟨h, hb⟩ | ⟨h, hb⟩
  · rw [h]
    exact ⟨MulEquiv.refl _, rfl⟩
  · rw [h, hb]
    exact ⟨CyclicFourCentralExtension.fixingShiftEquiv (representative_root_two 0) shift_zero,
      CyclicFourCentralExtension.fixingShiftEquiv_embed ..⟩
  · rw [h, hb]
    exact ⟨CyclicFourCentralExtension.fixingShiftEquiv (representative_root_two 2) shift_two,
      CyclicFourCentralExtension.fixingShiftEquiv_embed ..⟩

/-- It suffices to certify the two base actions with nonsplit fourth power.
This theorem is the assembly interface for the independent finite certificates. -/
theorem fixed_of_base_certificates
    (hzero : ∀ (a : MulAut (firstCore 0 true)),
      a (centralInvolution 0 true) = centralInvolution 0 true)
    (htwo : ∀ (a : MulAut (firstCore 2 true)),
      a (centralInvolution 2 true) = centralInvolution 2 true)
    (i : Fin 20) (hz : mark i true ∈ firstCore i true)
    (a : MulAut (firstCore i true)) : a ⟨mark i true, hz⟩ = ⟨mark i true, hz⟩ := by
  apply fixed_all_membership_proofs
  intro b
  obtain ⟨e, he⟩ := exists_marked_base_equiv i true
  apply fixed_of_marked_equiv e he _ b
  rcases baseIndex_cases i with h | h
  · rw [h]
    exact hzero
  · rw [h]
    exact htwo

end ReeTwo.FixingModel
