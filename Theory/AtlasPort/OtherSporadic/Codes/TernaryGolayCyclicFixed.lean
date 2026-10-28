/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernaryGolayCyclicFixed.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.TernaryGolayQuotient
public import Theory.AtlasPort.OtherSporadic.RepresentationTheory.PrimeOrderIrreducibility

/-!
# TernaryGolayCyclicFixed

An eleven-coordinate cycle has only constant fixed codewords and no nonzero fixed phase.
Self-orthogonality gives the final coordinate; a coprime-order lifting lemma handles the quotient.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernaryGolayCyclicFixed.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed computational definitions.
-/

@[expose] public section


namespace Atlas.Codes

/-- A ternary Golay word constant off one coordinate is constant everywhere.
Self-orthogonality with the all-one word gives the missing coordinate. -/
theorem ternaryGolay_constant_of_constant_off_one
    (w : ternaryGolay) (a : Fin 12) (c : ZMod 3)
    (hc : ∀ i, i ≠ a → w.val i = c) : ∀ i, w.val i = c := by
  have hsum : ∑ i, w.val i = 0 := by
    have h := ternaryGolay_selfOrthogonal w.property
      (fun _ => (1 : ZMod 3)) ternaryGolay_one
    simpa [ternaryDot, dotProductBilin, dotProduct] using h
  have he : w.val = (fun _ => c) + Pi.single a (w.val a - c) := by
    funext i
    by_cases hi : i = a
    · subst i; simp
    · simp [hi, hc i hi]
  rw [he] at hsum
  have hsub : w.val a - c = 0 := by
    simpa [Finset.sum_add_distrib, show (12 : ZMod 3) = 0 by decide] using hsum
  intro i
  by_cases hi : i = a
  · subst i; exact sub_eq_zero.mp hsub
  · exact hc i hi

/-- Under a permutation transitive on the complement of one coordinate,
a fixed ternary Golay word is constant. -/
theorem ternaryGolay_fixed_eq_constant
    (σ : Equiv.Perm (Fin 12)) (a : Fin 12)
    (htrans : ∀ i, i ≠ a → ∀ j, j ≠ a → ∃ k : ℕ, (σ ^ k) i = j)
    (w : ternaryGolay) (hw : ∀ i, w.val (σ i) = w.val i) :
    ∃ c : ZMod 3, ∀ i, w.val i = c := by
  obtain ⟨b, hb⟩ := exists_ne a
  have hit : ∀ k : ℕ, ∀ i, w.val ((σ ^ k) i) = w.val i := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro i
      rw [pow_succ', Equiv.Perm.mul_apply, hw, ih]
  refine ⟨w.val b, ternaryGolay_constant_of_constant_off_one w a (w.val b) ?_⟩
  intro i hi
  obtain ⟨k, hk⟩ := htrans b hb i hi
  rw [← hk]
  exact hit k b

/-- Constant codewords are precisely the scalar multiples of the distinguished
all-one codeword, hence lie in the constant submodule. -/
theorem ternaryGolay_mem_constants_of_constant
    (w : ternaryGolay) (c : ZMod 3) (hc : ∀ i, w.val i = c) :
    w ∈ ternaryConstants := by
  have he : w = c • ternaryOne := by
    apply Subtype.ext
    funext i
    simpa [ternaryOne] using hc i
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-- A fixed codeword under the specified eleven-coordinate orbit lies in the
one-dimensional constant submodule. -/
theorem ternaryGolay_fixed_mem_constants
    (σ : Equiv.Perm (Fin 12)) (a : Fin 12)
    (htrans : ∀ i, i ≠ a → ∀ j, j ≠ a → ∃ k : ℕ, (σ ^ k) i = j)
    (w : ternaryGolay) (hw : ∀ i, w.val (σ i) = w.val i) :
    w ∈ ternaryConstants := by
  obtain ⟨c, hc⟩ := ternaryGolay_fixed_eq_constant σ a htrans w hw
  exact ternaryGolay_mem_constants_of_constant w c hc

/-- For a code-preserving coordinate operator of eleventh power one, a fixed
class modulo constants is the zero class. The proof first lifts fixedness,
then uses the eleven-coordinate orbit. -/
theorem ternaryGolay_fixed_mod_constants_mem_constants
    (σ : Equiv.Perm (Fin 12)) (a : Fin 12)
    (htrans : ∀ i, i ≠ a → ∀ j, j ≠ a → ∃ k : ℕ, (σ ^ k) i = j)
    (s : Module.End (ZMod 3) ternaryGolay)
    (hscoord : ∀ w i, (s w).val i = w.val (σ i))
    (hs : s ^ 11 = 1) (w : ternaryGolay)
    (hw : s w - w ∈ ternaryConstants) : w ∈ ternaryConstants := by
  have hone : s ternaryOne = ternaryOne := by
    apply Subtype.ext
    funext i
    simpa [ternaryOne] using hscoord ternaryOne i
  have hconst : ∀ v ∈ ternaryConstants, s v = v := by
    intro v hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    rw [← hc, map_smul, hone]
  have hfixed := Atlas.RepresentationTheory.fixed_of_difference_mem_fixed_submodule
    s ternaryConstants hconst (n := 11) (by decide) hs hw
  apply ternaryGolay_fixed_mem_constants σ a htrans w
  intro i
  rw [← hscoord w i, hfixed]

/-- The induced endomorphism of the actual phase quotient has no nonzero
fixed vector under the stated coordinate-orbit and order hypotheses. -/
theorem ternaryPhase_fixed_eq_zero
    (σ : Equiv.Perm (Fin 12)) (a : Fin 12)
    (htrans : ∀ i, i ≠ a → ∀ j, j ≠ a → ∃ k : ℕ, (σ ^ k) i = j)
    (s : Module.End (ZMod 3) ternaryGolay)
    (hscoord : ∀ w i, (s w).val i = w.val (σ i))
    (hs : s ^ 11 = 1)
    (hpres : ternaryConstants ≤ ternaryConstants.comap s)
    (v : TernaryPhaseModule)
    (hv : ternaryConstants.mapQ ternaryConstants s hpres v = v) : v = 0 := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective ternaryConstants v
  apply (Submodule.Quotient.mk_eq_zero ternaryConstants).mpr
  apply ternaryGolay_fixed_mod_constants_mem_constants σ a htrans s hscoord hs w
  apply (Submodule.Quotient.mk_eq_zero ternaryConstants).mp
  change ternaryConstants.mkQ (s w - w) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr hv

end Atlas.Codes
