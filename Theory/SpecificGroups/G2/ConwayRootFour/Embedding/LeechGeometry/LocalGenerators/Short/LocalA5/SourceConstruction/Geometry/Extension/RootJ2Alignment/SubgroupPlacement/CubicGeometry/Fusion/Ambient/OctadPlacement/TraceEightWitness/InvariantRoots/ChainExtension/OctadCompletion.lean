module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.InvariantRoots.ChainExtension.Geometry
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechShortShellCounts

/-!
# Octad completion of the normalized third orbit

The frame pairings force a coordinate of `v` to be `4` and a coordinate of
`w` to be `-2`. The even minimal-shell classification therefore puts `v`
in shape `4²` and `w` in shape `2⁸`. Removing the four frame positions and
the two nonzero positions of `v` from the eight-position support of `w`
leaves at least two positions. The vector with entries `±4` there, with
signs matching `w`, has raw squared norm `32`, is orthogonal to the frame
and `v`, and has integral pairing `2` with `w`.

This proves the exact `NormalizedThirdOrbitCompletion` contract. In fact,
the construction does not need its additional pairing condition on `v,w`.
Its cubic-chain application is in `OctadCompletion.Chain`; the independent
marked D₄-placement problem remains with its own branch.

Source context: Aschbacher, *Sporadic Groups* (1994), 22.13 and 25.1–25.5.
The completion is an additional coordinate argument, not an assertion
quoted from those passages. The imported ATLAS coordinate and short-shell
results retain their attribution and license in their source modules.
-/

open Atlas.Lattices Atlas.Codes Atlas.Conway
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness.ChainExtension

public noncomputable section

private theorem dot_sub (x y z : IntegerCoordinates) :
    integerDot x (y - z) = integerDot x y - integerDot x z := by
  simp [integerDot, mul_sub, Finset.sum_sub_distrib]

private theorem frame_equations (x : leech) :
    2 * leechIntegralPairing (standardD4 0) x =
      x.val (frameCoordinate 0) + x.val (frameCoordinate 1) ∧
    2 * leechIntegralPairing (standardD4 1) x =
      x.val (frameCoordinate 0) - x.val (frameCoordinate 1) ∧
    2 * leechIntegralPairing (standardD4 2) x =
      x.val (frameCoordinate 2) - x.val (frameCoordinate 1) ∧
    2 * leechIntegralPairing (standardD4 3) x =
      x.val (frameCoordinate 3) - x.val (frameCoordinate 0) := by
  have h0 := leechIntegralPairing_mul (standardD4 0) x
  have h1 := leechIntegralPairing_mul (standardD4 1) x
  have h2 := leechIntegralPairing_mul (standardD4 2) x
  have h3 := leechIntegralPairing_mul (standardD4 3) x
  rw [integerDot_comm] at h0 h1 h2 h3
  simp only [standardD4, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, minimumPairPlus, minimumPairMinus,
    integerDot_add_right, dot_sub, integerDot_coordinateVector] at h0 h1 h2 h3 ⊢
  omega

private theorem even_of_even_coordinate (x : leech) (i : Omega)
    (hi : x.val i % 2 = 0) : ∀ j, x.val j % 2 = 0 := by
  rcases leech_coordinate_parity x.val x.prop with h | h
  · exact h
  · have h' := h i
    omega

private theorem shape_v (v : leech) (hv : integerDot v.val v.val = 32)
    (hvp : ∀ i, leechIntegralPairing (standardD4 i) v = if i = 3 then 2 else 0) :
    TwoFourShape v.val 0 2 := by
  have he := frame_equations v
  simp only [hvp] at he
  norm_num at he
  have hd : v.val (frameCoordinate 3) = 4 := by omega
  have hp := even_of_even_coordinate v (frameCoordinate 3) (by simp [hd])
  rcases Finset.mem_union.mp ((even_minimal_shell_iff v.val).mp ⟨v.prop, hp, hv⟩) with h | h
  · exact twoFourFamily_shape 0 2 v.val h
  · have hs := twoFourFamily_shape 8 0 v.val h
    have hm : frameCoordinate 3 ∈ evenMagnitudeSupport v.val 4 := by
      simp [evenMagnitudeSupport, hd]
    rw [Finset.card_eq_zero.mp hs.2.2] at hm
    exact (Finset.notMem_empty _ hm).elim

private theorem shape_w (w : leech) (hw : integerDot w.val w.val = 32)
    (hwp : ∀ i, leechIntegralPairing (standardD4 i) w = if i = 1 then -2 else 0) :
    TwoFourShape w.val 8 0 := by
  have he := frame_equations w
  simp only [hwp] at he
  norm_num at he
  have ha : w.val (frameCoordinate 0) = -2 := by omega
  have hp := even_of_even_coordinate w (frameCoordinate 0) (by simp [ha])
  rcases Finset.mem_union.mp ((even_minimal_shell_iff w.val).mp ⟨w.prop, hp, hw⟩) with h | h
  · have hs := twoFourFamily_shape 0 2 w.val h
    have hm : frameCoordinate 0 ∈ evenMagnitudeSupport w.val 2 := by
      simp [evenMagnitudeSupport, ha]
    rw [Finset.card_eq_zero.mp hs.2.1] at hm
    exact (Finset.notMem_empty _ hm).elim
  · exact twoFourFamily_shape 8 0 w.val h

private theorem signed_pair_mem (p q : Omega) (r s : ℤ)
    (hr : r = 2 ∨ r = -2) (hs : s = 2 ∨ s = -2) :
    coordinateVector p (2 * r) + coordinateVector q (2 * s) ∈ leech := by
  have hneg (i : Omega) : coordinateVector i (-4) = -coordinateVector i 4 := by
    funext j
    by_cases h : j = i <;> simp [coordinateVector, h]
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
  · exact coordinate_pair_mem p q
  · simpa only [show (2 : ℤ) * 2 = 4 from rfl,
      show (2 : ℤ) * -2 = -4 from rfl, hneg, ← sub_eq_add_neg]
      using difference_mem p q
  · simpa only [show (2 : ℤ) * 2 = 4 from rfl,
      show (2 : ℤ) * -2 = -4 from rfl, hneg, sub_eq_add_neg,
      add_comm] using difference_mem q p
  · simpa only [show (2 : ℤ) * -2 = -4 from rfl, hneg, neg_add]
      using leech.neg_mem (coordinate_pair_mem p q)

private theorem choose_positions (v w : leech)
    (hv : TwoFourShape v.val 0 2) (hw : TwoFourShape w.val 8 0) :
    ∃ p q : Omega, p ≠ q ∧
      (∀ i, p ≠ frameCoordinate i ∧ q ≠ frameCoordinate i) ∧
      v.val p = 0 ∧ v.val q = 0 ∧
      (w.val p = 2 ∨ w.val p = -2) ∧ (w.val q = 2 ∨ w.val q = -2) := by
  classical
  let F := Finset.univ.image frameCoordinate
  let V := evenMagnitudeSupport v.val 4
  let W := evenMagnitudeSupport w.val 2
  have hF : F.card ≤ 4 := (Finset.card_image_le).trans (by decide)
  have hV : V.card = 2 := hv.2.2
  have hW : W.card = 8 := hw.2.1
  have hlarge : 1 < (W \ (F ∪ V)).card := by
    have hb := Finset.card_union_le F V
    have hs := Finset.le_card_sdiff (F ∪ V) W
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hlarge
  obtain ⟨hpW, hpout⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hqW, hqout⟩ := Finset.mem_sdiff.mp hq
  have outside_zero (i : Omega) (hi : i ∉ V) : v.val i = 0 := by
    have h4 : v.val i * v.val i ≠ 16 := by simpa [V, evenMagnitudeSupport] using hi
    have h2 : v.val i * v.val i ≠ 4 := by
      intro h
      have hm : i ∈ evenMagnitudeSupport v.val 2 := by simp [evenMagnitudeSupport, h]
      rw [Finset.card_eq_zero.mp hv.2.1] at hm
      exact Finset.notMem_empty _ hm
    rcases hv.1 i with h | h | h | h | h <;> simp [h] at h2 h4 ⊢
  refine ⟨p, q, hpq, ?_, outside_zero p ?_, outside_zero q ?_,
    mul_self_eq_mul_self_iff.mp (Finset.mem_filter.mp hpW).2,
    mul_self_eq_mul_self_iff.mp (Finset.mem_filter.mp hqW).2⟩
  · intro i
    constructor
    · intro h
      apply hpout
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩
    · intro h
      apply hqout
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩
  · exact fun h => hpout (Finset.mem_union_right _ h)
  · exact fun h => hqout (Finset.mem_union_right _ h)

/-- The signed pair in the unused part of the octad completes the configuration. -/
theorem normalizedThirdOrbitCompletion : NormalizedThirdOrbitCompletion := by
  intro v w hv hw hvp hwp _hvw
  obtain ⟨p, q, hpq, hout, hvp0, hvq0, hwp2, hwq2⟩ :=
    choose_positions v w (shape_v v hv hvp) (shape_w w hw hwp)
  let y : leech := ⟨coordinateVector p (2 * w.val p) + coordinateVector q (2 * w.val q),
    signed_pair_mem p q (w.val p) (w.val q) hwp2 hwq2⟩
  have dot_y (z : IntegerCoordinates) :
      integerDot z y.val = z p * (2 * w.val p) + z q * (2 * w.val q) := by
    exact integerDot_add_right z _ _ |>.trans (by rw [integerDot_coordinateVector,
      integerDot_coordinateVector])
  have hyp : y.val p = 2 * w.val p := by
    simp [y, coordinateVector, hpq]
  have hyq : y.val q = 2 * w.val q := by
    simp [y, coordinateVector, Ne.symm hpq]
  have hyframe (i : Fin 4) : y.val (frameCoordinate i) = 0 := by
    simp [y, coordinateVector, Ne.symm (hout i).1, Ne.symm (hout i).2]
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · rw [dot_y, hyp, hyq]
    rcases hwp2 with h | h <;> rcases hwq2 with h' | h' <;> norm_num [h, h']
  · intro i
    change integerDot (standardD4 i).val y.val / 8 = 0
    rw [integerDot_comm]
    fin_cases i <;>
      norm_num [standardD4, minimumPairPlus, minimumPairMinus, integerDot_add_right,
        dot_sub, integerDot_coordinateVector, hyframe]
  · change integerDot v.val y.val / 8 = 0
    rw [dot_y, hvp0, hvq0]
    norm_num
  · change integerDot w.val y.val / 8 = 2
    rw [dot_y]
    rcases hwp2 with h | h <;> rcases hwq2 with h' | h' <;> norm_num [h, h']

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness.ChainExtension
