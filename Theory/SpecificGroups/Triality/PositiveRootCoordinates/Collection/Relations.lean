module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Curves
public import Theory.SpecificGroups.Triality.Model.QTKEParameters

/-!
# Local identities needed to collect the positive D4 curves

Root height is the restriction of the linear functional `(3, 2, 1, 0)` on the
standard coordinate realization. Thus a root sum has height strictly greater
than either summand, and all twelve positive roots have height less than six.

The two propositions below specify the remaining matrix identities on the
actual integral Geck curves. `SumExchange` is the characteristic-two A2
exchange formula; `NonsumCommute` is the complementary commuting formula.
These are explicit inputs to the collection reduction, not asserted theorems
or a normal-form certificate. They must be proved for the binary parameters.

Source: GLS3, 2.3.6–7 and §§2.4–2.6
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section

open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.PositiveCoordinates

/-- Heights in the published ordering of the twelve positive roots. -/
def collectionHeight : Fin 12 → ℕ := ![1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 5]

private def heightFunctional (v : Vec 4) : ℝ := 3 * v 0 + 2 * v 1 + v 2

private theorem heightFunctional_root (i : Fin 12) :
    heightFunctional ((typeDRootPairing 2).root (rootIndex i)) = collectionHeight i := by
  fin_cases i <;>
    norm_num [heightFunctional, collectionHeight, rootIndex, difference, sumRoot,
      typeDRootPairing_root_val, typeDRootEmbedding, typeDRootVector,
      basisVector, Pi.single_apply, Fin.ext_iff]

/-- The concrete degree used by collection is additive on actual root sums. -/
theorem collectionHeight_add {i j k : Fin 12}
    (h : (typeDRootPairing 2).root (rootIndex k) =
      (typeDRootPairing 2).root (rootIndex i) +
      (typeDRootPairing 2).root (rootIndex j)) :
    collectionHeight k = collectionHeight i + collectionHeight j := by
  have hh := congrArg (fun x : typeDRootSpan 4 => heightFunctional x) h
  have ha (x y : Vec 4) :
      heightFunctional (x + y) = heightFunctional x + heightFunctional y := by
    simp only [heightFunctional, Pi.add_apply]
    ring
  rw [Submodule.coe_add, ha, heightFunctional_root, heightFunctional_root,
    heightFunctional_root] at hh
  exact_mod_cast hh

theorem collectionHeight_pos (i : Fin 12) : 0 < collectionHeight i := by
  fin_cases i <;> decide

theorem collectionHeight_lt_six (i : Fin 12) : collectionHeight i < 6 := by
  fin_cases i <;> decide

theorem collectionHeight_sum_gt {i j k : Fin 12}
    (h : (typeDRootPairing 2).root (rootIndex k) =
      (typeDRootPairing 2).root (rootIndex i) +
      (typeDRootPairing 2).root (rootIndex j)) :
    max (collectionHeight i) (collectionHeight j) < collectionHeight k := by
  have := collectionHeight_add h
  have := collectionHeight_pos i
  have := collectionHeight_pos j
  omega

/-- A sum of two positive roots is a root exactly when it occurs in the
published positive-root enumeration. This connects the finite non-sum test
below to the usual absence of a root sum in the full root system. -/
theorem positive_root_sum_mem_range_iff (i j : Fin 12) :
    (typeDRootPairing 2).root (rootIndex i) +
        (typeDRootPairing 2).root (rootIndex j) ∈ Set.range (typeDRootPairing 2).root ↔
      ∃ k : Fin 12, (typeDRootPairing 2).root (rootIndex k) =
        (typeDRootPairing 2).root (rootIndex i) +
          (typeDRootPairing 2).root (rootIndex j) := by
  constructor
  · rintro ⟨r, hr⟩
    have hpos := (rootIndex_positive i).add (rootIndex_positive j) hr
    have hmem : r ∈ Set.range rootIndex := by
      rw [range_rootIndex]
      exact hpos
    obtain ⟨k, rfl⟩ := hmem
    exact ⟨k, hr⟩
  · rintro ⟨k, hk⟩
    exact ⟨rootIndex k, hk⟩

/-- The local root-sum exchange identity on the actual Geck curves.
This proposition is a proof obligation, not a normal-form assumption. -/
def SumExchange (P : Parameters) : Prop :=
  ∀ (i j k : Fin 12),
    (typeDRootPairing 2).root (rootIndex k) =
      (typeDRootPairing 2).root (rootIndex i) +
        (typeDRootPairing 2).root (rootIndex j) →
    ∀ a b : ExtensionField P,
      curve P i a * curve P j b =
        curve P j b * curve P i a * curve P k (a * b)

/-- Distinct positive curves commute when their root sum is absent.
This is the complementary matrix proof obligation to `SumExchange`. -/
def NonsumCommute (P : Parameters) : Prop :=
  ∀ (i j : Fin 12), i ≠ j →
    (¬ ∃ k : Fin 12, (typeDRootPairing 2).root (rootIndex k) =
      (typeDRootPairing 2).root (rootIndex i) +
        (typeDRootPairing 2).root (rootIndex j)) →
    ∀ a b : ExtensionField P, Commute (curve P i a) (curve P j b)

end Triality.Standard.PositiveCoordinates
