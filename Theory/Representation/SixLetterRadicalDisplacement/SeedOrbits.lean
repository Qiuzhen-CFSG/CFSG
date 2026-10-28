module

public import Theory.Representation.SixLetterRadicalDisplacement
public import Theory.Representation.BinaryPermutation.OrbitSizeSeparation
import Mathlib.Tactic.FinCases

/-!
# Weight separation for the six-letter augmentation seed

The nonzero vectors of the canonical seed plane have weight four. Every
coordinate permutation preserves weight, so no pair vector belongs to any
translate of that plane. This calculation uses the full five-dimensional
augmentation module, including its constant line.

The application is the cover branch of Aschbacher--Smith, Lemma 13.8.33,
printed p.966: a transvection center cannot enter an H-conjugate of V₃.
-/

public section
open BinaryPermutation
namespace Representation.SixLetterRadicalDisplacement

theorem seed_weight (v : U) (hv : v ∈ W) :
    v = 0 ∨ wordWeight v.val = 4 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
  fin_cases a <;> fin_cases b <;> decide

theorem pair_weight (i j : Fin 6) (hij : i ≠ j) :
    wordWeight (q i j).val = 2 := by
  revert i j
  decide

theorem pair_not_mem_seed_orbit (g : Equiv.Perm (Fin 6)) (i j : Fin 6)
    (hij : i ≠ j) :
    q i j ∉ W.map (coreRepresentation (Fin 6) g) := by
  rintro ⟨v, hv, he⟩
  have hw : wordWeight v.val = 2 := by
    have hh := wordWeight_permute g v.val
    change wordWeight (coreRepresentation (Fin 6) g v).val = _ at hh
    rw [he, pair_weight i j hij] at hh
    exact hh.symm
  rcases seed_weight v hv with rfl | hfour
  · simp [wordWeight] at hw
  · omega

end Representation.SixLetterRadicalDisplacement
