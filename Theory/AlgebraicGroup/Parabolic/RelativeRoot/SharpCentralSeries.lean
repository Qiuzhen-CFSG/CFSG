module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.ExactCommutatorLayers
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.UpperCommutatorDetection

/-!
# Sharp central series for parabolic unipotent radicals

This module identifies the relative-root filtration of a standard parabolic
unipotent radical with both of its central series in nonsingular
characteristic.  It packages the two sharp conclusions needed by the
structural theorem for parabolic subgroups without depending on that numbered
theorem.

The lower-series formula follows from exact commutator layers.  Their reverse
inclusion is obtained by splitting each root of relative height at least two
and using the nonzero `(1, 1)` Chevalley coefficient.  Above the maximal
relative height, antitonicity and termination extend the commutator equality
to every index, so the filtration satisfies the recursion defining the lower
central series.

For the upper series, the filtration is reversed and extended by the whole
unipotent radical after its terminal index.  Adjacent-quotient coordinates
and the same nonsingular Chevalley coefficient detect every element outside
the next reversed layer by a commutator.  The generic commutator-detection
criterion then identifies the mapped upper central series with this reversed
filtration.

This is the sharp central-series conclusion of GLS3, Chapter 1, Theorem
1.13.5(c), with the root decomposition supplied by Lemma 1.13.6.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open scoped commutatorElement

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- In nonsingular characteristic, the positive relative-root layers are the
lower central series of the unipotent radical, and their reverse is its mapped
upper central series. -/
public theorem ParabolicRelativeRootSetup.sharp_central_series_of_nonsingular
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K)
    (classification : RootClassification)
    (hType : HasDynkinType S.rootPairing classification)
    (hNonsingular : ¬ IsUSingular classification (ringChar k)) :
    (∀ i, 0 < i →
      S.layer i = S.U.toSubgroup.lowerCentralSeries (i - 1)) ∧
    (∀ i, i ≤ S.maxRelativeHeight →
      Subgroup.map S.U.toSubgroup.subtype
        (Subgroup.upperCentralSeries S.U.toSubgroup i) =
        S.layer (S.maxRelativeHeight + 1 - i)) := by
  letI := Fintype.ofFinite S.ι
  have hFirst : S.layer 1 = S.U.toSubgroup :=
    S.unipotent_eq_first_layer.symm
  have hTerminal : S.layer (S.maxRelativeHeight + 1) = ⊥ := by
    rw [ParabolicRelativeRootSetup.layer, ← S.rootBase_support]
    apply relativeRootSeries_eq_bot_of_height_lt
    intro α
    have hα := S.relativeHeight_le α
    omega
  have hAntitone : Antitone S.layer := by
    intro i j hij
    exact relativeRootSeries_antitone S.D S.rootEquiv S.base.support
      S.coeff S.J hij
  have hLayerLe : ∀ i, 0 < i → S.layer i ≤ S.U.toSubgroup := by
    intro i hi
    rw [← hFirst]
    exact hAntitone (by omega)
  have hLayerBot : ∀ i, S.maxRelativeHeight + 1 ≤ i → S.layer i = ⊥ := by
    intro i hi
    apply le_bot_iff.mp
    rw [← hTerminal]
    exact hAntitone hi
  have hExact := S.exact_commutator_layers classification hType hNonsingular
  have hCommAll : ∀ n : ℕ,
      ⁅S.layer (n + 1), S.U.toSubgroup⁆ = S.layer (n + 2) := by
    intro n
    by_cases hn : n + 1 ≤ S.maxRelativeHeight
    · simpa [Nat.add_assoc] using hExact (n + 1) (by omega) hn
    · have hn' : S.maxRelativeHeight + 1 ≤ n + 1 := by omega
      rw [hLayerBot (n + 1) hn', Subgroup.commutator_bot_left,
        hLayerBot (n + 2) (by omega)]
  have hLower : ∀ n : ℕ,
      S.layer (n + 1) = S.U.toSubgroup.lowerCentralSeries n :=
    subgroupSeries_eq_lowerCentralSeries_of_commutator_eq
      S.U.toSubgroup S.layer hFirst hCommAll
  constructor
  · intro i hi
    have hi' : i - 1 + 1 = i := by omega
    simpa [hi'] using hLower (i - 1)
  · let A : ℕ → Subgroup (Variety.Point K) := fun n =>
      if _ : n ≤ S.maxRelativeHeight then
        S.layer (S.maxRelativeHeight + 1 - n)
      else S.U.toSubgroup
    have hAZero : A 0 = ⊥ := by
      simpa [A] using hTerminal
    have hATop : A (S.maxRelativeHeight + 1) = S.U.toSubgroup := by
      simp [A]
    have hALe : ∀ n, A n ≤ S.U.toSubgroup := by
      intro n
      dsimp [A]
      split_ifs with hn
      · exact hLayerLe _ (by omega)
      · exact le_rfl
    have hComm : ∀ n, ⁅A (n + 1), S.U.toSubgroup⁆ ≤ A n := by
      intro n
      by_cases hn : n < S.maxRelativeHeight
      · have hnext : n + 1 ≤ S.maxRelativeHeight := by omega
        have hcurr : n ≤ S.maxRelativeHeight := by omega
        rw [show A (n + 1) =
            S.layer (S.maxRelativeHeight - n) by simp [A, hnext],
          show A n = S.layer (S.maxRelativeHeight + 1 - n) by
            simp [A, hcurr]]
        simpa [Nat.sub_add_comm (show n ≤ S.maxRelativeHeight by omega)] using
          (hExact (S.maxRelativeHeight - n) (by omega) (by omega)).le
      · by_cases hEq : n = S.maxRelativeHeight
        · subst n
          rw [show A (S.maxRelativeHeight + 1) = S.U.toSubgroup by simp [A],
            show A S.maxRelativeHeight = S.U.toSubgroup by simp [A, hFirst]]
          exact Subgroup.commutator_le_self S.U.toSubgroup
        · have hAnext : A (n + 1) = S.U.toSubgroup := by
            simp [A]
            omega
          have hAn : A n = S.U.toSubgroup := by
            simp [A]
            omega
          rw [hAnext, hAn]
          exact Subgroup.commutator_le_self S.U.toSubgroup
    have hDetectA : ∀ n, n < S.maxRelativeHeight →
        ∀ x : S.U.toSubgroup, x ∉ (A (n + 1)).subgroupOf S.U.toSubgroup →
          ∃ y : S.U.toSubgroup,
            ⁅(x : Variety.Point K), (y : Variety.Point K)⁆ ∉ A n := by
      intro n hn x hx
      have hAnext : A (n + 1) = S.layer (S.maxRelativeHeight - n) := by
        simp [A]
        omega
      have hAn : A n = S.layer (S.maxRelativeHeight + 1 - n) := by
        simp [A]
        omega
      rw [hAnext] at hx
      rw [hAn]
      exact S.upper_commutator_detection classification hType hNonsingular
        n hn x hx
    have hUpper := upperCentralSeries_map_eq_of_commutator_detection
      S.U.toSubgroup A S.maxRelativeHeight hAZero hATop hALe hComm hDetectA
    intro i hi
    rw [hUpper i (by omega)]
    simp [A, hi]

end Theory.AlgebraicGroup
