module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Soundness

/-!
# Cached-word certificates for Rudvalis part-5 residuals 69–137

The factor words are concatenations of shared words from the part-6 cache.
Correctness of that cache and the remaining finite point checks imply exactly
those transitions selected by `Part5Residual.target`. The raw point checks are
independent of the cache's composition certificates, so both can be built
separately and combined by the final residual owner.

Source: `OrderLevel0Data`, `OrderLevel0Part5ResidualReduction`, and the shared
ATLAS word certificates in `OrderLevel0Part6Block0.FactorMaps.Soundness`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual1Checks

open Part6Block0.FactorMaps

/-- Shared-word evaluation is sound once the cache compositions are certified. -/
public theorem evalPieces_eq (hc : ∀ j, CompositionCheck j)
    (s : List (Fin 125)) (x : Fin 4060) : evalCache s x.val =
      (Part6Tables.eval Part6Tables.gen1 (expand s) x).val := by
  induction s generalizing x with
  | nil => rfl
  | cons j s ih =>
    rw [evalCache, force_eq, ih, cache_eq_of_compositions hc]
    exact congrArg Fin.val (eval_append (cacheWord j) (expand s) x).symm

/-- The cached slices certify the unchanged representative and factor words. -/
public theorem ofSlices (hc : ∀ j, CompositionCheck j)
    (i : Fin 2) (r : Fin 4060) (u v : List (Fin 4)) (s : List (Fin 125))
    (hu : L0RepWord r = u)
    (hv : L0RepWord (L0Act (i.castLE (by decide)) r) = v)
    (hf : expand s = L0Factor (i.castLE (by decide)) r)
    (h : ∀ b, cachedSlice (evalCache s) i u v b = true) : stepCheck i r := by
  apply Part6Nat.ofSlices
  intro b
  apply (checkFin_spec _).mpr
  intro x
  have hx := (checkFin_spec _).mp (h b) x
  have bound : 20 * b.val + x.val < 4060 := by omega
  have he := evalPieces_eq hc s ⟨20 * b.val + x.val, bound⟩
  rw [hf] at he
  have hn := eval_eq (L0Factor (i.castLE (by decide)) r)
    ⟨20 * b.val + x.val, bound⟩
  have hm := he.trans hn.symm
  simpa only [Part6Nat.point, hu, hv, cachedSlice, hm] using hx

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual1Checks
