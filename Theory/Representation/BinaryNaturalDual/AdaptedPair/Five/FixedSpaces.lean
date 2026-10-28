module

public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Five.Basic

/-!
# The standard fixed line in binary natural-plus-dual five-space

Elementary upper transvections force a fixed vector onto the natural e₁-line
and the dual e₅*-line. The reversal-twisted graph involution equates the two
coefficients. For the stabilizer of (e₃,e₃*), the same argument takes place
inside ker(e₃*) × ann(e₃): the missing coordinate equations are precisely
membership in that moving space. Finally I + E₂₁ fixes the pair and moves
z = (e₁,e₅*), witnessing noncentralization by its inner point stabilizer.

These proofs use the actual coordinate action and generated standard subgroup;
they require no Sylow, cardinality or fixed-space premise.

Source: corrected H.9.1(4), Aschbacher–Smith, printed p.390; the fixed-line
calculation supplies the marked uses in 12.1.1 and 12.1.3.
-/

public section

namespace BinaryNaturalDual.AdaptedPair.Five

private theorem mem_fixedLine_of_coordinates (d : CoordinateAction 5) (v : CoordinateSpace 5)
    (hx : ∀ i : Fin 5, i ≠ 0 → v.1 i = 0)
    (hf : ∀ i : Fin 5, i ≠ 4 → v.2 (axis i) = 0)
    (ht : linearAction d (tau 5) v = v) :
    v ∈ Submodule.span (ZMod 2) {fixedVector 5} := by
  have hab : v.2 (axis 4) = v.1 0 := by
    have h := congrArg (fun w : CoordinateSpace 5 => w.1 0) ht
    simpa only [tau_fst, show (0 : Fin 5).rev = 4 by decide] using h
  apply Submodule.mem_span_singleton.mpr
  refine ⟨v.1 0, ?_⟩
  apply Prod.ext
  · ext i
    by_cases hi : i = 0
    · subst i
      simp [fixedVector, axis]
    · simp [fixedVector, axis, Ne.symm hi, hx i hi]
  · apply (Pi.basisFun (ZMod 2) (Fin 5)).ext
    intro i
    simp only [Pi.basisFun_apply]
    change v.1 0 * (axis i) 4 = v.2 (axis i)
    by_cases hi : i = 4
    · subst i
      simpa [axis] using hab.symm
    · rw [hf i hi]
      simp [axis, hi]

theorem standard_fixedVectors (d : CoordinateAction 5) :
    fixedVectors (linearAction d) (standardGroup 5) =
      Submodule.span (ZMod 2) {fixedVector 5} := by
  apply le_antisymm
  · intro v hv
    apply mem_fixedLine_of_coordinates d v
    · intro i hi
      have h0i : (0 : Fin 5) < i := by change 0 < i.val; have := i.isLt; omega
      exact (root_fixed_coordinates d 0 i h0i.ne v
        (hv _ (inner_root_mem_standard h0i))).1
    · intro i hi
      have hi4 : i < (4 : Fin 5) := by have := i.isLt; change i.val < 4; omega
      exact (root_fixed_coordinates d i 4 hi4.ne v
        (hv _ (inner_root_mem_standard hi4))).2
    · exact hv _ tau_mem_standard
  · apply Submodule.span_le.mpr
    intro v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact fixedVector_mem_fixedVectors d

theorem moving_fixedVectors (d : CoordinateAction 5) :
    movingSpace vectorFive ⊓ fixedVectors (linearAction d)
      (standardGroup 5 ⊓ pointStabilizer (linearAction d) vectorFive) =
        Submodule.span (ZMod 2) {fixedVector 5} := by
  apply le_antisymm
  · rintro v ⟨hw, hv⟩
    have hm := mem_movingSpace vectorFive v |>.mp hw
    change v.1 2 = 0 ∧ v.2 (axis 2) = 0 at hm
    apply mem_fixedLine_of_coordinates d v
    · intro i hi
      by_cases hi2 : i = 2
      · simpa only [hi2] using hm.1
      · have h0i : (0 : Fin 5) < i := by change 0 < i.val; have := i.isLt; omega
        exact (root_fixed_coordinates d 0 i h0i.ne v
          (hv _ ⟨inner_root_mem_standard h0i,
            root_fixes_vectorFive d 0 i h0i.ne (by decide) hi2⟩)).1
    · intro i hi
      by_cases hi2 : i = 2
      · simpa only [hi2] using hm.2
      · have hi4 : i < (4 : Fin 5) := by have := i.isLt; change i.val < 4; omega
        exact (root_fixed_coordinates d i 4 hi4.ne v
          (hv _ ⟨inner_root_mem_standard hi4,
            root_fixes_vectorFive d i 4 hi4.ne hi2 (by decide)⟩)).2
    · exact hv _ ⟨tau_mem_standard, tau_fixes_vectorFive d⟩
  · apply Submodule.span_le.mpr
    intro v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    refine ⟨fixedVector_mem_movingSpace_five, ?_⟩
    exact fun g hg => fixedVector_mem_fixedVectors d g hg.1

theorem fixed_space_equality (d : CoordinateAction 5) :
    movingSpace vectorFive ⊓ fixedVectors (linearAction d)
      (standardGroup 5 ⊓ pointStabilizer (linearAction d) vectorFive) =
        fixedVectors (linearAction d) (standardGroup 5) := by
  rw [moving_fixedVectors, standard_fixedVectors]

theorem fixed_space_finrank (d : CoordinateAction 5) :
    Module.finrank (ZMod 2) (fixedVectors (linearAction d) (standardGroup 5)) = 1 := by
  rw [standard_fixedVectors]
  exact finrank_fixedVector_span 5

theorem inner_stabilizer_moves (d : CoordinateAction 5) :
    ∃ a ∈ innerGroup 5, linearAction d a vectorFive = vectorFive ∧
      ∃ z ∈ fixedVectors (linearAction d) (standardGroup 5), linearAction d a z ≠ z := by
  refine ⟨MulAut.conj (root 1 0 (by decide)), ⟨root 1 0 (by decide), rfl⟩,
    root_fixes_vectorFive d 1 0 (by decide) (by decide) (by decide),
    fixedVector 5, fixedVector_mem_fixedVectors d, ?_⟩
  intro h
  rw [linearAction_inner] at h
  have hh := congrArg (fun w : CoordinateSpace 5 => w.1 1) h
  simp [BinaryLinear.NaturalDualFlag.action_fst,
    root_apply, fixedVector, axis] at hh

end BinaryNaturalDual.AdaptedPair.Five
