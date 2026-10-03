module

public import Theory.SpecificGroups.ReeTwo.Characters
public import Theory.GroupTheory.PGroup.Omega
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The intrinsic kernel of the Ree two core character

The kernel of the binary character on the order-1024 core is exactly `Ω₁(Core)`.
The square equations in the five leading coordinates kill the character on
involutions. Explicit involutions generate the root pairs needed for the reverse
inclusion, as seen by applying the root normal form in the omega quotient.
Consequently the kernel is characteristic. Both alternative Sylow characters
restrict to this character on the canonical core, since parity vanishes there.

Source: Shinoda (1975), (2.3), pp. 81–82, for the verified coordinate
multiplication and root normal form. The omega-kernel argument here is direct;
no automorphism census or external computation is assumed.
-/

namespace ReeTwo.Core

private theorem square_coordinate_test : ∀ a b c d e : ZMod 2,
    c * a + d * a + b * b = 0 → d * a + e * a + c * b = 0 →
    e * a + e * b + d * c = 0 → e * b + e * c + d * d = 0 →
    b + c + d = 0 ∨ (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 0 ∧ e = 0) := by decide +kernel

/-- Every involution in the core is killed by its binary character. -/
public theorem binaryCharacter_eq_one_of_square_eq_one (x : Core) (hx : x ^ 2 = 1) :
    binaryCharacter x = 1 := by
  rw [pow_two] at hx
  have h5 : x.b2 * x.b0 + x.b3 * x.b0 + x.b1 * x.b1 = 0 := by
    calc
      _ = (mul x x).b5 := by simp only [mul]; ring_nf; reduce_mod_char
      _ = 0 := congrArg Core.b5 hx
  have h6 : x.b3 * x.b0 + x.b4 * x.b0 + x.b2 * x.b1 = 0 := by
    calc
      _ = (mul x x).b6 := by simp only [mul]; ring_nf; reduce_mod_char
      _ = 0 := congrArg Core.b6 hx
  have h7 : x.b4 * x.b0 + x.b4 * x.b1 + x.b3 * x.b2 = 0 := by
    calc
      _ = (mul x x).b7 := by simp only [mul]; ring_nf; reduce_mod_char
      _ = 0 := congrArg Core.b7 hx
  have h8 : x.b4 * x.b1 + x.b4 * x.b2 + x.b3 * x.b3 = 0 := by
    calc
      _ = (mul x x).b8 := by simp only [mul]; ring_nf; reduce_mod_char
      _ = 0 := congrArg Core.b8 hx
  rcases square_coordinate_test _ _ _ _ _ h5 h6 h7 h8 with h | ⟨ha, hb, hc, hd, he⟩
  · exact congrArg Multiplicative.ofAdd h
  · have h9 : (mul x x).b9 = 0 := congrArg Core.b9 hx
    simp only [mul, ha, hb, hc, hd, he, mul_zero, mul_one, add_zero] at h9
    have hcancel : x.b9 + x.b9 = 0 := by ring_nf; reduce_mod_char
    have hfalse : (1 : ZMod 2) = 0 := by
      calc
        _ = (x.b9 + x.b9) + 1 := by rw [hcancel, zero_add]
        _ = x.b9 + 1 + x.b9 := by ring
        _ = 0 := h9
    exact (by decide : (1 : ZMod 2) ≠ 0) hfalse |>.elim

private theorem involution_mem_omega (x : Core) (hx : x ^ 2 = 1) :
    x ∈ omega₁ Core (p := 2) :=
  Subgroup.subset_closure (by simpa only [Set.mem_ofPred_eq, pow_one] using hx)

private theorem root_mem_omega (i : CoreRoot) (hi : i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3) :
    root i ∈ omega₁ Core (p := 2) := by
  apply involution_mem_omega
  exact (by decide +kernel : ∀ i : CoreRoot, i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3 → root i ^ 2 = 1) i hi

private theorem root_pair_mem_omega :
    root 1 * root 3 ∈ omega₁ Core (p := 2) ∧
      root 2 * root 3 ∈ omega₁ Core (p := 2) := by
  let W := omega₁ Core (p := 2)
  have h0 : root 0 ∈ W := root_mem_omega 0 (by decide)
  have h4 : root 4 ∈ W := root_mem_omega 4 (by decide)
  have h5 : root 5 ∈ W := root_mem_omega 5 (by decide)
  have ha : root 0 * (root 1 * root 3) * root 4 * root 5 ∈ W :=
    involution_mem_omega _ (by decide +kernel)
  have hb : root 0 * (root 2 * root 3) * root 4 ∈ W :=
    involution_mem_omega _ (by decide +kernel)
  constructor
  · exact (W.mul_mem_cancel_left h0).mp
      ((W.mul_mem_cancel_right h4).mp ((W.mul_mem_cancel_right h5).mp ha))
  · exact (W.mul_mem_cancel_left h0).mp ((W.mul_mem_cancel_right h4).mp hb)

/-- The binary core character has precisely the first two-omega subgroup as kernel. -/
public theorem binaryCharacter_ker_eq_omega :
    binaryCharacter.ker = omega₁ Core (p := 2) := by
  apply le_antisymm
  · let W := omega₁ Core (p := 2)
    have : W.Characteristic := omega₁_characteristic Core
    let q := QuotientGroup.mk' W
    have hq (i : CoreRoot) (hi : i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3) : q (root i) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (root_mem_omega i hi)
    have h13 : q (root 1) * q (root 3) = 1 := by
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr root_pair_mem_omega.1
    have h23 : q (root 2) * q (root 3) = 1 := by
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr root_pair_mem_omega.2
    have h33 : q (root 3) * q (root 3) = 1 := by
      rw [← map_mul]
      have he : root 3 * root 3 = root 8 := by decide +kernel
      rw [he]
      exact hq 8 (by decide)
    have h1 : q (root 1) = q (root 3) := mul_right_cancel (h13.trans h33.symm)
    have h2 : q (root 2) = q (root 3) := mul_right_cancel (h23.trans h33.symm)
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    have hn := congrArg q (normal_form x)
    simp only [map_mul, map_pow, hq 0 (by decide), hq 4 (by decide),
      hq 5 (by decide), hq 6 (by decide), hq 7 (by decide), hq 8 (by decide),
      hq 9 (by decide), one_pow, _root_.one_mul, mul_one, h1, h2] at hn
    have hx' : x.b1 + x.b2 + x.b3 = 0 := congrArg Multiplicative.toAdd hx
    have hb : ∀ a b c : ZMod 2, a + b + c = 0 →
        q (root 3) ^ a.val * q (root 3) ^ b.val * q (root 3) ^ c.val = 1 := by
      intro a b c
      rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) a with rfl | rfl <;>
        rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) b with rfl | rfl <;>
        rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) c with rfl | rfl <;>
        simp only [show (0 : ZMod 2).val = 0 from rfl,
          show (1 : ZMod 2).val = 1 from rfl, pow_zero, pow_one,
          _root_.one_mul, mul_one, h33]
      all_goals first | trivial | intro h; exact absurd h (by decide)
    exact hn.symm.trans (hb _ _ _ hx')
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    exact binaryCharacter_eq_one_of_square_eq_one x (by simpa only [Set.mem_ofPred_eq, pow_one] using hx)

/-- The kernel of the binary core character is intrinsic to the core group. -/
public theorem binaryCharacter_ker_characteristic : binaryCharacter.ker.Characteristic := by
  rw [binaryCharacter_ker_eq_omega]
  exact omega₁_characteristic Core

/-- The characteristic core kernel transports through any group isomorphism. -/
public theorem binaryCharacter_comp_ker_characteristic {H : Type*} [Group H]
    (e : H ≃* Core) : (binaryCharacter.comp e.toMonoidHom).ker.Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro f x hx
  have h := Subgroup.characteristic_iff_le_comap.mp binaryCharacter_ker_characteristic
    ((e.symm.trans f).trans e) hx
  change binaryCharacter (e (f x)) = 1
  change binaryCharacter (e (f (e.symm (e x)))) = 1 at h
  simpa only [e.symm_apply_apply] using h

end ReeTwo.Core

namespace ReeTwo.SylowModel

/-- The canonical ten-root core inside the Sylow semidirect product. -/
@[expose] public def coreSubgroup : Subgroup SylowModel :=
  (SemidirectProduct.inl : Core →* SylowModel).range

/-- The specified core identified with its canonical embedded copy. -/
@[expose] public noncomputable def coreEquiv : Core ≃* coreSubgroup :=
  MonoidHom.ofInjective SemidirectProduct.inl_injective

/-- The canonical core subgroup has order 1024. -/
public theorem coreSubgroup_card : Nat.card coreSubgroup = 1024 :=
  (Nat.card_congr coreEquiv.symm.toEquiv).trans Core.card

/-- Both alternative characters have characteristic kernel on the canonical core. -/
public theorem alternativeCharacter_core_ker_characteristic
    (χ : SylowModel →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    (χ.comp coreSubgroup.subtype).ker.Characteristic := by
  have heq : χ.comp coreSubgroup.subtype =
      Core.binaryCharacter.comp coreEquiv.symm.toMonoidHom := by
    ext x
    obtain ⟨c, rfl⟩ := coreEquiv.surjective x
    change χ (SemidirectProduct.inl c) = Core.binaryCharacter (coreEquiv.symm (coreEquiv c))
    rw [coreEquiv.symm_apply_apply]
    rcases hχ with rfl | rfl
    · rfl
    · change Core.binaryCharacter c * parity 1 = Core.binaryCharacter c
      rw [map_one, mul_one]
  rw [heq]
  exact Core.binaryCharacter_comp_ker_characteristic coreEquiv.symm

end ReeTwo.SylowModel
