module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityFourCoordinates

/-!
# Generation of the eight rank-four Ree two parity carriers

If a subgroup has one of the eight stated coordinate carriers, it is the
corresponding displayed generator closure. The forward inclusion checks the
original generators. For the reverse inclusion, powers of the second basis
lift remove the cyclic-four coordinate. The remaining core element has the
ordered root normal form from Core.normal_form. The necessary roots are
recovered by cancelling displayed generators; row 3 uses the paired root
word root 3 * root 5 and its central correction.

This argument assumes only that the carrier is a subgroup. In particular,
it does not use coordinate multiplicativity, Frattini calculations, or an
external subgroup-order computation.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified root
multiplication in Core and Sylow. The exact generator sets and carrier
equations are those of SmallParityRepresentatives and
SmallParityFourCoordinates.
-/

namespace ReeTwo.SylowModel
set_option maxRecDepth 32768

private theorem candidate_le (i : Fin 8) (D : Subgroup SylowModel)
    (hD : ∀ x, x ∈ D ↔ smallParityFourCarrier i x) :
    smallParityTwoCandidate (smallParityFourIndex i) ≤ D := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  apply (hD x).mpr
  fin_cases i
  all_goals rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp [smallParityFourCarrier]; decide +kernel

private theorem root8_mem (i : Fin 8) :
    root 8 ∈ smallParityTwoCandidate (smallParityFourIndex i) := by
  fin_cases i
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

private theorem root9_mem (i : Fin 8) :
    root 9 ∈ smallParityTwoCandidate (smallParityFourIndex i) := by
  fin_cases i
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))

private theorem root7_mem (i : Fin 8) :
    root 7 ∈ smallParityTwoCandidate (smallParityFourIndex i) := by
  have h8 := root8_mem i
  have h9 := root9_mem i
  fin_cases i
  · apply (Subgroup.mul_mem_cancel_right _ h8).mp
    apply (Subgroup.mul_mem_cancel_right _ h9).mp
    exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · apply (Subgroup.mul_mem_cancel_right _ h8).mp
    apply (Subgroup.mul_mem_cancel_right _ h9).mp
    exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · apply (Subgroup.mul_mem_cancel_right _ h8).mp
    apply (Subgroup.mul_mem_cancel_right _ h9).mp
    exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · apply (Subgroup.mul_mem_cancel_right _ h8).mp
    apply (Subgroup.mul_mem_cancel_right _ h9).mp
    exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · apply (Subgroup.mul_mem_cancel_right _ h8).mp
    apply (Subgroup.mul_mem_cancel_right _ h9).mp
    exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

private theorem root4_mem (i : Fin 8) :
    root 4 ∈ smallParityTwoCandidate (smallParityFourIndex i) := by
  have h9 := root9_mem i
  fin_cases i
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · apply (Subgroup.mul_mem_cancel_right _ h9).mp
    exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · apply (Subgroup.mul_mem_cancel_right _ h9).mp
    exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

private theorem root6_mem (i : Fin 8) (hi : i < 6) :
    root 6 ∈ smallParityTwoCandidate (smallParityFourIndex i) := by
  apply (Subgroup.mul_mem_cancel_right _ (root7_mem i)).mp
  apply (Subgroup.mul_mem_cancel_right _ (root8_mem i)).mp
  fin_cases i
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · contradiction
  · contradiction

private theorem root3_mem (i : Fin 8) (hi : i = 0 ∨ i = 1 ∨ i = 6) :
    root 3 ∈ smallParityTwoCandidate (smallParityFourIndex i) := by
  rcases hi with rfl | rfl | rfl
  all_goals exact Subgroup.subset_closure (Or.inl rfl)

private theorem root2_mem (i : Fin 8) (hi : i ≠ 6) :
    root 2 ∈ smallParityTwoCandidate (smallParityFourIndex i) := by
  have h4 := root4_mem i
  have h7 := root7_mem i
  have h8 := root8_mem i
  fin_cases i
  · apply (Subgroup.mul_mem_cancel_right _ (root3_mem _ (by decide))).mp
    apply (Subgroup.mul_mem_cancel_right _ h4).mp
    apply (Subgroup.mul_mem_cancel_right _ h7).mp
    exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · apply (Subgroup.mul_mem_cancel_right _ (root3_mem _ (by decide))).mp
    apply (Subgroup.mul_mem_cancel_right _ h4).mp
    apply (Subgroup.mul_mem_cancel_right _ h7).mp
    exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  · apply (Subgroup.mul_mem_cancel_right _ h4).mp
    apply (Subgroup.mul_mem_cancel_right _ h8).mp
    exact Subgroup.subset_closure (Or.inl rfl)
  · apply (Subgroup.mul_mem_cancel_right _ h4).mp
    apply (Subgroup.mul_mem_cancel_right _ h8).mp
    exact Subgroup.subset_closure (Or.inl rfl)
  · apply (Subgroup.mul_mem_cancel_right _ h4).mp
    apply (Subgroup.mul_mem_cancel_right _ h8).mp
    exact Subgroup.subset_closure (Or.inl rfl)
  · apply (Subgroup.mul_mem_cancel_right _ h4).mp
    apply (Subgroup.mul_mem_cancel_right _ h8).mp
    exact Subgroup.subset_closure (Or.inl rfl)
  · contradiction
  · apply (Subgroup.mul_mem_cancel_right _ h4).mp
    apply (Subgroup.mul_mem_cancel_right _ h8).mp
    exact Subgroup.subset_closure (Or.inl rfl)

private theorem root5_mem : root 5 ∈ smallParityTwoCandidate (smallParityFourIndex 2) := by
  apply (Subgroup.mul_mem_cancel_right _ (root8_mem 2)).mp
  exact Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))

private theorem root35_mem :
    root 3 * root 5 ∈ smallParityTwoCandidate (smallParityFourIndex 3) := by
  have h : root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9 ∈
      smallParityTwoCandidate (smallParityFourIndex 3) :=
    Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
  have he : root 3 * root 5 = (root 2)⁻¹ *
      (root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9) *
      (root 7 * root 8 * root 9)⁻¹ * (root 4)⁻¹ * root 9 := by decide +kernel
  rw [he]
  repeat apply Subgroup.mul_mem
  · exact Subgroup.inv_mem _ (root2_mem 3 (by decide))
  · exact h
  · apply Subgroup.inv_mem
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (root7_mem 3) (root8_mem 3)) (root9_mem 3)
  · exact Subgroup.inv_mem _ (root4_mem 3)
  · exact root9_mem 3

private theorem root345_mem (a b : ZMod 2) :
    root 3 ^ a.val * root 4 ^ b.val * root 5 ^ a.val ∈
      smallParityTwoCandidate (smallParityFourIndex 3) := by
  have he : ∀ a b : ZMod 2,
      root 3 ^ a.val * root 4 ^ b.val * root 5 ^ a.val =
        (root 3 * root 5) ^ a.val * root 4 ^ b.val * root 9 ^ (a * b).val := by
    decide +kernel
  rw [he]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.pow_mem _ root35_mem _) (Subgroup.pow_mem _ (root4_mem 3) _))
    (Subgroup.pow_mem _ (root9_mem 3) _)

private theorem core_mem (i : Fin 8) (b : Core)
    (hb : smallParityFourCarrier i (SemidirectProduct.inl b)) :
    (SemidirectProduct.inl b : SylowModel) ∈
      smallParityTwoCandidate (smallParityFourIndex i) := by
  have hn := congrArg (SemidirectProduct.inl : Core → SylowModel) (Core.normal_form b)
  simp only [map_mul, map_pow] at hn
  change root 0 ^ b.b0.val * root 1 ^ b.b1.val * root 2 ^ b.b2.val *
    root 3 ^ b.b3.val * root 4 ^ b.b4.val * root 5 ^ b.b5.val *
    root 6 ^ b.b6.val * root 7 ^ b.b7.val * root 8 ^ b.b8.val *
    root 9 ^ b.b9.val = _ at hn
  rcases b with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩
  rcases hb with ⟨rfl, rfl, hb⟩
  fin_cases i
  · change b5 = 0 at hb
    rcases hb with rfl
    simp only [ZMod.val_zero, pow_zero, one_mul, mul_one] at hn
    rw [← hn]
    repeat apply Subgroup.mul_mem
    · exact Subgroup.pow_mem _ (root2_mem 0 (by decide)) _
    · exact Subgroup.pow_mem _ (root3_mem 0 (by decide)) _
    · exact Subgroup.pow_mem _ (root4_mem 0) _
    · exact Subgroup.pow_mem _ (root6_mem 0 (by decide)) _
    · exact Subgroup.pow_mem _ (root7_mem 0) _
    · exact Subgroup.pow_mem _ (root8_mem 0) _
    · exact Subgroup.pow_mem _ (root9_mem 0) _
  · change b5 = 0 at hb
    rcases hb with rfl
    simp only [ZMod.val_zero, pow_zero, one_mul, mul_one] at hn
    rw [← hn]
    repeat apply Subgroup.mul_mem
    · exact Subgroup.pow_mem _ (root2_mem 1 (by decide)) _
    · exact Subgroup.pow_mem _ (root3_mem 1 (by decide)) _
    · exact Subgroup.pow_mem _ (root4_mem 1) _
    · exact Subgroup.pow_mem _ (root6_mem 1 (by decide)) _
    · exact Subgroup.pow_mem _ (root7_mem 1) _
    · exact Subgroup.pow_mem _ (root8_mem 1) _
    · exact Subgroup.pow_mem _ (root9_mem 1) _
  · change b3 = 0 at hb
    rcases hb with rfl
    simp only [ZMod.val_zero, pow_zero, one_mul, mul_one] at hn
    rw [← hn]
    repeat apply Subgroup.mul_mem
    · exact Subgroup.pow_mem _ (root2_mem 2 (by decide)) _
    · exact Subgroup.pow_mem _ (root4_mem 2) _
    · exact Subgroup.pow_mem _ (root5_mem) _
    · exact Subgroup.pow_mem _ (root6_mem 2 (by decide)) _
    · exact Subgroup.pow_mem _ (root7_mem 2) _
    · exact Subgroup.pow_mem _ (root8_mem 2) _
    · exact Subgroup.pow_mem _ (root9_mem 2) _
  · change b3 = b5 at hb
    subst b3
    simp only [ZMod.val_zero, pow_zero, one_mul, mul_one] at hn
    rw [mul_assoc (root 2 ^ b2.val) (root 3 ^ b5.val),
      mul_assoc (root 2 ^ b2.val) (root 3 ^ b5.val * root 4 ^ b4.val)] at hn
    rw [← hn]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ (root345_mem b5 b4)) ?_) ?_) ?_) ?_
    · exact Subgroup.pow_mem _ (root2_mem 3 (by decide)) _
    · exact Subgroup.pow_mem _ (root6_mem 3 (by decide)) _
    · exact Subgroup.pow_mem _ (root7_mem 3) _
    · exact Subgroup.pow_mem _ (root8_mem 3) _
    · exact Subgroup.pow_mem _ (root9_mem 3) _
  · change b3 = 0 ∧ b5 = 0 at hb
    rcases hb with ⟨rfl, rfl⟩
    simp only [ZMod.val_zero, pow_zero, one_mul, mul_one] at hn
    rw [← hn]
    repeat apply Subgroup.mul_mem
    · exact Subgroup.pow_mem _ (root2_mem 4 (by decide)) _
    · exact Subgroup.pow_mem _ (root4_mem 4) _
    · exact Subgroup.pow_mem _ (root6_mem 4 (by decide)) _
    · exact Subgroup.pow_mem _ (root7_mem 4) _
    · exact Subgroup.pow_mem _ (root8_mem 4) _
    · exact Subgroup.pow_mem _ (root9_mem 4) _
  · change b3 = 0 ∧ b5 = 0 at hb
    rcases hb with ⟨rfl, rfl⟩
    simp only [ZMod.val_zero, pow_zero, one_mul, mul_one] at hn
    rw [← hn]
    repeat apply Subgroup.mul_mem
    · exact Subgroup.pow_mem _ (root2_mem 5 (by decide)) _
    · exact Subgroup.pow_mem _ (root4_mem 5) _
    · exact Subgroup.pow_mem _ (root6_mem 5 (by decide)) _
    · exact Subgroup.pow_mem _ (root7_mem 5) _
    · exact Subgroup.pow_mem _ (root8_mem 5) _
    · exact Subgroup.pow_mem _ (root9_mem 5) _
  · change b2 = 0 ∧ b5 = 0 ∧ b6 = 0 at hb
    rcases hb with ⟨rfl, rfl, rfl⟩
    simp only [ZMod.val_zero, pow_zero, one_mul, mul_one] at hn
    rw [← hn]
    repeat apply Subgroup.mul_mem
    · exact Subgroup.pow_mem _ (root3_mem 6 (by decide)) _
    · exact Subgroup.pow_mem _ (root4_mem 6) _
    · exact Subgroup.pow_mem _ (root7_mem 6) _
    · exact Subgroup.pow_mem _ (root8_mem 6) _
    · exact Subgroup.pow_mem _ (root9_mem 6) _
  · rcases hb with ⟨h3, h5, h6⟩
    change b3 = 0 at h3
    change b5 = 0 at h5
    subst b3
    subst b5
    have : b6 = 0 := by simpa using h6
    subst b6
    simp only [ZMod.val_zero, pow_zero, one_mul, mul_one] at hn
    rw [← hn]
    repeat apply Subgroup.mul_mem
    · exact Subgroup.pow_mem _ (root2_mem 7 (by decide)) _
    · exact Subgroup.pow_mem _ (root4_mem 7) _
    · exact Subgroup.pow_mem _ (root7_mem 7) _
    · exact Subgroup.pow_mem _ (root8_mem 7) _
    · exact Subgroup.pow_mem _ (root9_mem 7) _

private theorem cyclic_lift_right : ∀ (i : Fin 8) (t : FiveFour.Cyclic 4),
    (smallParityFourBasis i 1 ^ t.toAdd.val).right = t := by decide +kernel

/-- Any subgroup with the stated carrier is exactly the displayed generator closure. -/
public theorem smallParityFourCandidate_eq_of_carrier (i : Fin 8) (D : Subgroup SylowModel)
    (hD : ∀ x, x ∈ D ↔ smallParityFourCarrier i x) :
    smallParityTwoCandidate (smallParityFourIndex i) = D := by
  apply le_antisymm (candidate_le i D hD)
  intro x hx
  let g := smallParityFourBasis i 1 ^ x.right.toAdd.val
  have hg : g ∈ smallParityTwoCandidate (smallParityFourIndex i) :=
    Subgroup.pow_mem _ (smallParityFourBasis_mem i 1) _
  have hgD : g ∈ D := candidate_le i D hD hg
  have hyD : x * g⁻¹ ∈ D := D.mul_mem hx (D.inv_mem hgD)
  have hr : (x * g⁻¹).right = 1 := by
    rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right, cyclic_lift_right]
    exact mul_inv_cancel _
  have he : (SemidirectProduct.inl (x * g⁻¹).left : SylowModel) = x * g⁻¹ :=
    SemidirectProduct.ext rfl hr.symm
  have hy : x * g⁻¹ ∈ smallParityTwoCandidate (smallParityFourIndex i) := by
    rw [← he]
    apply core_mem
    rw [he]
    exact (hD _).mp hyD
  have hxy := Subgroup.mul_mem _ hy hg
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hxy

end ReeTwo.SylowModel
