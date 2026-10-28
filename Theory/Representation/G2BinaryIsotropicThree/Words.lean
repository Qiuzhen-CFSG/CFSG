module

public import Theory.Representation.G2BinaryIsotropicThree.Normalize
public import Theory.Representation.FirstCohomologyG2Natural.BinaryPair

/-!
# Actual octonion words for the fifteen three-space reductions

Interpret the checked finite word table inside the literal G₂(2) model. The
first, second, and inverse letters are commutators; only the faithful target
needs an extra short-root letter. Thus the distinguished orbit is realized
inside G₂(2)′ itself, with no assumed orbit count.

Source: Aschbacher–Smith 13.3.12(3), printed p.890.
-/

@[expose] public section

open Atlas.SplitOctonion Module Submodule Subgroup
namespace Atlas.G2.Natural.BinaryIsotropicThree
open BinaryNondegeneratePlane Atlas.G2.Restricted.NaturalCoordinates

def letter : Fin 5 → Model K :=
  ![(binaryA K).val,(binaryB K).val,rootD 1,(binaryA K).val^3,(binaryB K).val^2]
def word : List (Fin 5) → Model K
  | []=>1
  | i::w=>letter i*word w

private theorem action_a (v : W) :
    rho (binaryA K).val v=Certificate.stepA v := by
  ext i
  fin_cases i <;> simp [Certificate.stepA,action_apply,
    Atlas.G2.Restricted.NaturalCoordinates.projection,representative,traceZeroAction_val,binaryA_apply]
private theorem action_b (v : W) :
    rho (binaryB K).val v=Certificate.stepB v := by
  ext i
  fin_cases i <;> simp [Certificate.stepB,action_apply,
    Atlas.G2.Restricted.NaturalCoordinates.projection,representative,traceZeroAction_val,binaryB_apply]

theorem letter_action (i : Fin 5) (v : W) : rho (letter i) v=Certificate.step i v := by
  fin_cases i
  · exact action_a v
  · exact action_b v
  · simp [letter,Certificate.step,Certificate.stepD]
  · simp [letter,Certificate.step,pow_succ,Module.End.mul_apply,action_a]
  · simp [letter,Certificate.step,pow_succ,Module.End.mul_apply,action_b]

theorem word_action (w : List (Fin 5)) (v : W) : rho (word w) v=Certificate.wordAction w v := by
  induction w with
  | nil => simp [word,Certificate.wordAction]
  | cons i w ih => simp only [word,Certificate.wordAction,map_mul,Module.End.mul_apply,ih,letter_action]

theorem letter_mem_derived (i : Fin 5) (hi : i≠2) : letter i∈commutator (Model K) := by
  fin_cases i
  · exact (binaryA K).property
  · exact (binaryB K).property
  · exact (hi rfl).elim
  · exact (commutator (Model K)).pow_mem (binaryA K).property 3
  · exact (commutator (Model K)).pow_mem (binaryB K).property 2

theorem word_mem_derived (w : List (Fin 5)) (hw : ∀i∈w,i≠2) : word w∈commutator (Model K) := by
  induction w with
  | nil => exact (commutator (Model K)).one_mem
  | cons i w ih =>
    exact (commutator (Model K)).mul_mem (letter_mem_derived i (hw i (List.mem_cons_self)))
      (ih (fun j hj=>hw j (List.mem_cons_of_mem i hj)))

theorem markedPlane_map_le (i : Fin 15) :
    (markedPlane i).map (rho (word (Certificate.words i)))≤target (Certificate.other i) := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro v (rfl|rfl|h)
  · change Certificate.inTarget _ (rho _ _)
    rw [word_action]
    exact (Certificate.image_certificate i).1
  · change Certificate.inTarget _ (rho _ _)
    rw [word_action]
    exact (Certificate.image_certificate i).2.1
  · obtain rfl := h
    change Certificate.inTarget _ (rho _ _)
    rw [word_action]
    exact (Certificate.image_certificate i).2.2
end Atlas.G2.Natural.BinaryIsotropicThree
