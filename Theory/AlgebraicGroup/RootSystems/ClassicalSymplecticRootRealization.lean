module

public import Theory.AlgebraicGroup.RootSystems.Classical
public import Theory.AlgebraicGroup.RootSystems.Dynkin

/-!
This module records the standard type-C Cartan witness for the concrete
coordinate root pairing.  The roots are indexed by pairs of signed coordinate
vectors and signed double coordinate vectors; the base consists of adjacent
differences and the final long root.  The existing coordinate calculation of
the base Cartan matrix is compared directly with `dynkinCartanEntry`, yielding
the `HasDynkinType` interface used by algebraic-group root realizations.

The result is deliberately independent of a particular algebraic group.  A
geometric construction supplies a `RootSystemModel` for this pairing, while
these lemmas supply its standard type-C classification witness.
-/

namespace Theory.AlgebraicGroup

open StandardRootSystem

private lemma dynkinCartanEntry_C_succ_eq_typeCCartanMatrix (m : ℕ)
    (i j : Fin (m + 1)) :
    dynkinCartanEntry ⟨.C, m + 1⟩ i j = typeCCartanMatrix m i j := by
  by_cases hij : i = j
  · subst j
    simp [dynkinCartanEntry, typeCCartanMatrix]
  · simp only [dynkinCartanEntry, typeCCartanMatrix, hij, ↓reduceIte]
    by_cases hforward : i.val + 1 = j.val
    · have hreverse : ¬j.val + 1 = i.val := by omega
      simp [hforward]
    · by_cases hreverse : j.val + 1 = i.val
      · have hilast : (i = Fin.last m) ↔ i.val + 1 = m + 1 := by
          constructor
          · intro h
            subst i
            simp
          · intro h
            apply Fin.ext
            simpa using Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using h)
        by_cases hlast : i = Fin.last m
        · subst i
          simp [hreverse]
        · have hnotlast : ¬i.val + 1 = m + 1 := by
            intro h
            exact hlast (hilast.mpr h)
          have hnotm : ¬i.val = m := by
            intro hi
            apply hlast
            apply Fin.ext
            simpa using hi
          simp [hreverse, hlast, hnotm]
      · simp [hforward, hreverse]

/-- The coordinate root pairing with `m + 1` coordinates has the standard
type `C_{m+1}` Cartan matrix. -/
public theorem typeCRootPairing_hasDynkinType_succ (m : ℕ) :
    HasDynkinType (typeCRootPairing (m + 1)) ⟨.C, m + 1⟩ := by
  refine ⟨typeCRootPairing_base m, (typeCRootPairing_baseEquiv m).symm, ?_⟩
  intro i j
  change (typeCRootPairing_base m).cartanMatrix i j = _
  have h := typeCRootPairing_base_cartanMatrix m
    ((typeCRootPairing_baseEquiv m).symm i)
    ((typeCRootPairing_baseEquiv m).symm j)
  have h' : (typeCRootPairing_base m).cartanMatrix i j =
      typeCCartanMatrix m ((typeCRootPairing_baseEquiv m).symm i)
        ((typeCRootPairing_baseEquiv m).symm j) := by
    simpa using h
  rw [h']
  exact (dynkinCartanEntry_C_succ_eq_typeCCartanMatrix m
    ((typeCRootPairing_baseEquiv m).symm i)
    ((typeCRootPairing_baseEquiv m).symm j)).symm

/-- The standard coordinate pairing has type `C_m` in every positive rank. -/
public theorem typeCRootPairing_hasDynkinType_of_pos (m : ℕ) (hm : 0 < m) :
    HasDynkinType (typeCRootPairing m) ⟨.C, m⟩ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simpa [Nat.succ_eq_add_one] using typeCRootPairing_hasDynkinType_succ n

end Theory.AlgebraicGroup
