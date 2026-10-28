module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Data
import Mathlib.Tactic.FinCases

/-!
# Soundness of the compressed factor evaluator

The shared-word graph is topologically ordered. Induction on its node index
transfers binary composition certificates to word-action correctness. The
expanded root words are compared with the published `FactorWords` in Lean.
The final owner supplies the finite `CompositionCheck` certificates.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
set_option Elab.async false
set_option maxRecDepth 30000

private theorem parents_lt : ∀ j : Fin 121,
    (left j).val < j.val + 4 ∧ (right j).val < j.val + 4 := by
  apply allFin
  decide +kernel

private theorem cacheWord_comp : ∀ j : Fin 121,
    cacheWord ⟨j.val + 4, by omega⟩ = cacheWord (left j) ++ cacheWord (right j) := by
  apply allFin
  decide +kernel

private theorem seed_eq (j : Fin 4) (x : Fin 4060) :
    cache (j.castLE (by decide)) x.val =
      (Part6Tables.eval Part6Tables.gen1 (cacheWord (j.castLE (by decide))) x).val := by
  fin_cases j
  · exact gen1_eq 0 x
  · exact gen1_eq 1 x
  · exact gen1_eq 2 x
  · exact gen1_eq 3 x

public theorem cache_eq_of_compositions (h : ∀ j, CompositionCheck j)
    (j : Fin 125) (x : Fin 4060) : cache j x.val =
      (Part6Tables.eval Part6Tables.gen1 (cacheWord j) x).val := by
  have aux : ∀ n (hn : n < 125) (y : Fin 4060), cache ⟨n, hn⟩ y.val =
      (Part6Tables.eval Part6Tables.gen1 (cacheWord ⟨n, hn⟩) y).val := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn y
      by_cases hs : n < 4
      · exact seed_eq ⟨n, hs⟩ y
      · let k : Fin 121 := ⟨n - 4, by omega⟩
        have hk : k.val + 4 = n := by dsimp [k]; omega
        have hi : (⟨k.val + 4, by omega⟩ : Fin 125) = ⟨n, hn⟩ := Fin.ext hk
        have hw := cacheWord_comp k
        rw [hi] at hw
        rw [hw]
        apply ofComp (cache ⟨n, hn⟩) (cache (left k)) (cache (right k))
          (cacheWord (left k)) (cacheWord (right k))
        · exact fun z => ih (left k).val (by have := (parents_lt k).1; omega) (left k).isLt z
        · exact fun z => ih (right k).val (by have := (parents_lt k).2; omega) (right k).isLt z
        · simpa only [CompositionCheck, hi] using h k
  exact aux j.val j.isLt x

public theorem pieces_eq : ∀ k : Fin 100, expand (pieces k) = FactorWords.word k := by
  apply allFin
  decide +kernel

/-- The compression uses only 554 references, with at most ten per factor. -/
public theorem pieces_length_le : ∀ k : Fin 100, (pieces k).length ≤ 10 := by
  apply allFin
  decide +kernel

private theorem evalCache_eq (h : ∀ j, CompositionCheck j)
    (s : List (Fin 125)) (x : Fin 4060) : evalCache s x.val =
      (Part6Tables.eval Part6Tables.gen1 (expand s) x).val := by
  induction s generalizing x with
  | nil => rfl
  | cons j s ih =>
    rw [evalCache, force_eq, ih, cache_eq_of_compositions h]
    exact congrArg Fin.val (eval_append (cacheWord j) (expand s) x).symm

/-- Binary map certificates suffice for the requested factor-action equality. -/
public theorem map_eq_of_compositions (h : ∀ j, CompositionCheck j)
    (k : Fin 100) (x : Fin 4060) : map k x.val =
      (Part6Tables.eval Part6Tables.gen1 (FactorWords.word k) x).val := by
  rw [map, evalCache_eq h, pieces_eq]

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
