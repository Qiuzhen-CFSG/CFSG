module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.Coverage.UpperCenter.Tails

/-!
# Small commutator tests separating the first twenty coordinates

For each generator `g_i`, a displayed test generator gives a commutator with
leading coordinate `pivot i`. Every later generator's commutator with that
same test lies in the strictly later tail. Thus `g_i` fails to centralize the
test modulo that tail, while the whole next tail centralizes it.

The checked words use only sixteen adjacent collection steps each. The finite
certificates inspect twenty test rows and twenty-one generators, never the
2²¹ group elements. Collection proves each equality in the actual presentation;
normal-form uniqueness, through `Tails`, proves each required inequality.

Source: `SylowNormalEights/source/pc.json`, using Mathlib's commutator convention
`a*b*a⁻¹*b⁻¹`. The nearby source README records the original inverse-conjugation
relations and provenance. `UpperCenter/source/discover.py` reproduces the choice
of test and leading coordinate; its output is not used as a proof.
-/

@[expose] public section

namespace Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.Coverage.UpperCenter

open scoped commutatorElement

def test : Fin 20 → Fin 21 :=
  ![15,16,14,15,12,9,12,11,9,12,7,7,4,1,7,2,1,1,2,5]
def pivot : Fin 20 → Fin 21 :=
  ![16,18,17,18,15,14,16,16,17,18,15,16,15,15,18,18,18,19,19,20]
private def response (i : Fin 20) (k : Fin 21) : List (Fin 21) :=
  collect 16 ([k, test i] ++ inverseGeneratorWord k ++ inverseGeneratorWord (test i))

private lemma response_eq (i : Fin 20) (k : Fin 21) :
    wordValue (response i k) = ⁅generator k, generator (test i)⁆ := by
  unfold response
  rw [collect_sound]
  simp only [wordValue_append, wordValue_cons, wordValue_nil, mul_one,
    wordValue_inverseGeneratorWord, commutatorElement_def]

private lemma self_response (i : Fin 20) :
    response i i.castSucc = pivot i :: (response i i.castSucc).tail :=
  (by decide +kernel : ∀ i : Fin 20,
    response i i.castSucc = pivot i :: (response i i.castSucc).tail) i

private lemma self_response_tail (i : Fin 20) :
    (response i i.castSucc).tail.Forall (fun k => (pivot i).val < k.val) :=
  (by decide +kernel : ∀ i : Fin 20,
    (response i i.castSucc).tail.Forall (fun k => (pivot i).val < k.val)) i

private lemma later_response (i : Fin 20) (k : Fin 21) (hik : i.val < k.val) :
    (response i k).Forall (fun j => (pivot i).val < j.val) :=
  (by decide +kernel : ∀ (i : Fin 20) (k : Fin 21), i.val < k.val →
    (response i k).Forall (fun j => (pivot i).val < j.val)) i k hik

lemma later_commutator_mem (i : Fin 20) (k : Fin 21) (hik : i.val < k.val) :
    ⁅generator k, generator (test i)⁆ ∈ tail (pivot i).succ := by
  rw [← response_eq]
  exact word_mem_tail _ _ (fun j hj => (List.forall_iff_forall_mem.mp (later_response i k hik)) j hj)

lemma self_commutator_not_mem (hcard : Nat.card Carrier = 2 ^ 21) (i : Fin 20) :
    ⁅generator i.castSucc, generator (test i)⁆ ∉ tail (pivot i).succ := by
  rw [← response_eq, self_response, wordValue_cons]
  intro h
  apply generator_not_tail hcard (pivot i)
  exact ((tail (pivot i).succ).mul_mem_cancel_right
    (word_mem_tail _ _ (fun j hj =>
      (List.forall_iff_forall_mem.mp (self_response_tail i)) j hj))).mp h

lemma pivot_lt_twenty (i : Fin 20) (hi : i.val < 19) : (pivot i).val < 20 :=
  (by decide +kernel : ∀ i : Fin 20, i.val < 19 → (pivot i).val < 20) i hi

lemma pivot_lt_nineteen (i : Fin 20) (hi : i.val < 17) : (pivot i).val < 19 :=
  (by decide +kernel : ∀ i : Fin 20, i.val < 17 → (pivot i).val < 19) i hi

end Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.Coverage.UpperCenter
