module

public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.CoordinateActions
public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.ShearExtraction
public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.FiniteCriterion

/-!
# From the original reflections to the two root word laws

The exact quotient fixed planes determine nonsingular binary shears. Squares
intertwine these shears with the original central transpositions, so the finite
criterion applies to the actual cross-commutator law. Both original actions
are retained for the later root-plane transport.
Source: Aschbacher, *Sporadic Groups* (1994), proof of 45.3, pp.242–243.
-/

@[expose] public section
noncomputable section
namespace Theory.GroupTheory.HyperbolicRecognition
variable {K : Type*} [Group K] {F : HyperbolicFactors K}
    {P : HyperbolicFrame F.A F.z} {Q : HyperbolicFrame F.B F.u}
namespace MarkedCoordinates
variable (C : MarkedCoordinates F P Q)

private theorem centralWord_add (M : Cross) (c d : Central) :
    centralWord M (c+d) = centralWord M c * centralWord M d := by
  apply Word.ext <;> simp [centralWord]

private theorem central_action (a : MulAut K) (f : Central → Central)
    (hf0 : f 0 = 0) (hfadd : ∀ c d, f (c+d) = f c + f d)
    (hz : C.transport a (centralWord C.matrix cz) = centralWord C.matrix (f cz))
    (hu : C.transport a (centralWord C.matrix cu) = centralWord C.matrix (f cu))
    (c : Central) : C.transport a (centralWord C.matrix c) = centralWord C.matrix (f c) := by
  rcases c with ⟨i,j⟩
  fin_cases i <;> fin_cases j
  · change C.transport a 1 = centralWord C.matrix (f 0)
    rw [map_one,hf0]
    rfl
  · exact hu
  · exact hz
  · change C.transport a (centralWord C.matrix (cz+cu)) = _
    rw [centralWord_add,map_mul,hz,hu,← centralWord_add,← hfadd]
    rfl

/-- The original first reflection has its prescribed action on every central word. -/
theorem first_central_action (a : F.FirstActor) (c : Central) :
    C.transport a.aut (centralWord C.matrix c) =
      centralWord C.matrix (centerReflectA c) := by
  apply C.central_action a.aut centerReflectA rfl (fun c d => by
    ext <;> simp [centerReflectA,add_left_comm,add_comm]) _ _ c
  · rw [← C.map_z,C.transport_apply,C.equiv.symm_apply_apply,a.map_z,C.map_z]
    rfl
  · rw [← C.map_u,C.transport_apply,C.equiv.symm_apply_apply,a.map_u]
    change C.equiv ((F.z : K)*(F.u : K)) = _
    rw [map_mul,C.map_z,C.map_u,← centralWord_add]
    rfl

/-- The original second reflection has its prescribed action on every central word. -/
theorem second_central_action (a : F.SecondActor) (c : Central) :
    C.transport a.aut (centralWord C.matrix c) =
      centralWord C.matrix (centerReflectB c) := by
  apply C.central_action a.aut centerReflectB rfl (fun c d => by
    ext <;> simp [centerReflectB,add_left_comm,add_comm]) _ _ c
  · rw [← C.map_z,C.transport_apply,C.equiv.symm_apply_apply,a.map_z]
    change C.equiv ((F.z : K)*(F.u : K)) = _
    rw [map_mul,C.map_z,C.map_u,← centralWord_add]
    rfl
  · rw [← C.map_u,C.transport_apply,C.equiv.symm_apply_apply,a.map_u,C.map_u]
    rfl

private theorem quadratic_action (a : MulAut K) (f : Central → Central)
    (hc : ∀ c, C.transport a (centralWord C.matrix c) = centralWord C.matrix (f c))
    (v : Vector) : quadratic C.matrix (C.quotientMap a v) = f (quadratic C.matrix v) := by
  apply centralWord_injective C.matrix
  change centralWord C.matrix (quadratic C.matrix (C.transport a (lift C.matrix v)).vector) = _
  rw [← square_word,← map_pow,square_word,hc]
  rfl

/-- The first actual reflection gives a nonsingular square-preserving shear. -/
theorem first_reflection (a : F.FirstActor) :
    ∃ S : Frame, FirstReflection C.matrix S ∧
      ∀ x : K, (C.equiv (a.aut x)).vector = reflectA S (C.equiv x).vector := by
  obtain ⟨S,hS,hform⟩ := exists_first_shear (C.quotientMap a.aut)
    (C.quotientMap_involutive a.aut a.square) (C.quotientMap_first_fixed a)
  refine ⟨S,⟨hS,?_⟩,?_⟩
  · intro v
    rw [← hform]
    exact C.quadratic_action a.aut centerReflectA (C.first_central_action a) v
  · intro x
    rw [← C.quotientMap_original,hform]

/-- The second actual reflection gives the other nonsingular square-preserving shear. -/
theorem second_reflection (a : F.SecondActor) :
    ∃ S : Frame, SecondReflection C.matrix S ∧
      ∀ x : K, (C.equiv (a.aut x)).vector = reflectB S (C.equiv x).vector := by
  obtain ⟨S,hS,hform⟩ := exists_second_shear (C.quotientMap a.aut)
    (C.quotientMap_involutive a.aut a.square) (C.quotientMap_second_fixed a)
  refine ⟨S,⟨hS,?_⟩,?_⟩
  · intro v
    rw [← hform]
    exact C.quadratic_action a.aut centerReflectB (C.second_central_action a) v
  · intro x
    rw [← C.quotientMap_original,hform]

/-- The actual cross law is one of the two UT₃(F₄) laws. -/
theorem twoCases (a : F.FirstActor) (b : F.SecondActor) : TwoCases C.matrix := by
  obtain ⟨S,hS,_⟩ := C.first_reflection a
  obtain ⟨T,hT,_⟩ := C.second_reflection b
  exact twoCases_of_reflections C.matrix ⟨S,hS⟩ ⟨T,hT⟩

end MarkedCoordinates
end Theory.GroupTheory.HyperbolicRecognition
