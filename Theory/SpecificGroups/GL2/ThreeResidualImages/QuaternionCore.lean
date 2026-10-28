module

public import Theory.SpecificGroups.GL2.ThreeResidualImages.Basic

/-!
# The quaternion two-core of ternary linear overgroups

For every H containing the determinant kernel, the ambient image of its
intrinsic two-core is the concrete Q₈. A normal two-subgroup has exponent
dividing eight. For any matrix of such order outside Q₈, a checked cubic
conjugate makes the product with that conjugate a nonidentity element of
order three. Relative normality in H rules this out. Conversely Q₈ is
normal in GL₂(3), so its restriction to H lies in the intrinsic core.

Source application: Aschbacher–Smith, F.6.16, printed pp.308–309.
-/

public section
open Matrix Subgroup
namespace Matrix.GeneralLinearGroup
private abbrev M := Matrix (Fin 2) (Fin 2) (ZMod 3)

private theorem matrix_two_normal_test : ∀ A : M, A ^ 8 = 1 →
    (A = 1 ∨ A = -1 ∨ A ^ 2 = -1) ∨
    ∃ B : M, B.det = 1 ∧ B ^ 3 = 1 ∧
      (A * B * A * B ^ 2) ^ 3 = 1 ∧ A * B * A * B ^ 2 ≠ 1 := by
  decide +kernel

/-- Normality is inside H; the conclusion retains the inclusion H → GL₂(3). -/
theorem three_normal_two_le_quaternion (H : Subgroup (GL (Fin 2) (ZMod 3)))
    (hS : threeSpecialLinear ≤ H) (N : Subgroup H) [N.Normal]
    (hN : IsPGroup 2 N) : N.map H.subtype ≤ threeQuaternion := by
  rintro x ⟨a, ha, rfl⟩
  let n : N := ⟨a,ha⟩
  have hn24 : n ^ 24 = 1 := Subtype.ext (Subtype.ext (three_pow_twentyFour a.val))
  have hn8 : n ^ 8 = 1 := by
    apply (hN.powEquiv (by decide : Nat.Coprime 2 3)).injective
    change (n ^ 8) ^ 3 = (1 : N) ^ 3
    simpa only [← pow_mul, one_pow] using hn24
  have ha8 : a.val.val ^ 8 = 1 :=
    congrArg (fun z : N => z.val.val.val) hn8
  rcases matrix_two_normal_test a.val.val ha8 with hq | ⟨B, hBd, hB3, hc3, hc1⟩
  · exact (three_mem_quaternion a.val).mpr hq
  · let bG : (GL (Fin 2) (ZMod 3)) := mkOfDetNeZero B (by rw [hBd]; decide)
    have hbS : bG ∈ threeSpecialLinear := (three_mem_specialLinear bG).mpr hBd
    let b : H := ⟨bG, hS hbS⟩
    have hb3 : b ^ 3 = 1 := Subtype.ext (Units.ext hB3)
    have hbi : b⁻¹ = b ^ 2 := by
      apply inv_eq_of_mul_eq_one_right
      simpa only [← pow_succ'] using hb3
    let c : N := ⟨a * b * a * b⁻¹, by
      simpa only [mul_assoc] using N.mul_mem ha ((inferInstance : N.Normal).conj_mem a ha b)⟩
    have hcp : c ^ 3 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      change (a * b * a * b⁻¹).val.val ^ 3 = 1
      rw [hbi]
      exact hc3
    have hc : c = 1 := by
      apply (hN.powEquiv (by decide : Nat.Coprime 2 3)).injective
      change c ^ 3 = (1 : N) ^ 3
      simpa only [one_pow] using hcp
    apply (hc1 ?_).elim
    have h := congrArg (fun z : N => z.val.val.val) hc
    change (a * b * a * b⁻¹).val.val = 1 at h
    rw [hbi] at h
    exact h

/-- The ambient image of the intrinsic two-core is the concrete quaternion subgroup. -/
theorem three_twoCore_image (H : Subgroup (GL (Fin 2) (ZMod 3))) (hS : threeSpecialLinear ≤ H) :
    (pCore 2 H).map H.subtype = threeQuaternion := by
  apply le_antisymm (three_normal_two_le_quaternion H hS _ pCore_isPGroup)
  have hQH := threeQuaternion_le_specialLinear.trans hS
  have hcore : threeQuaternion.subgroupOf H ≤ pCore 2 H :=
    le_sSup ⟨inferInstance, threeQuaternion_isPGroup.comap_subtype⟩
  intro x hx
  exact ⟨⟨x, hQH hx⟩, hcore hx, rfl⟩

/-- The intrinsic core is genuinely isomorphic to Q₈, through its ambient image. -/
noncomputable def threeTwoCoreEquivQuaternion (H : Subgroup (GL (Fin 2) (ZMod 3)))
    (hS : threeSpecialLinear ≤ H) : pCore 2 H ≃* QuaternionGroup 2 :=
  ((pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
    ((MulEquiv.subgroupCongr (three_twoCore_image H hS)).trans threeQuaternionEquiv)

/-- Every overgroup of SL₂(3) in GL₂(3) has two-core of order eight. -/
theorem three_twoCore_card (H : Subgroup (GL (Fin 2) (ZMod 3))) (hS : threeSpecialLinear ≤ H) :
    Nat.card (pCore 2 H) = 8 := by
  rw [Nat.card_congr (threeTwoCoreEquivQuaternion H hS).toEquiv,
    Nat.card_eq_fintype_card, QuaternionGroup.card]
end Matrix.GeneralLinearGroup
