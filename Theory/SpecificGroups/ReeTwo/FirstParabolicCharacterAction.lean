module

public import Theory.SpecificGroups.ReeTwo.FirstParabolicCoordinates

/-!
# The four-character action of the first Ree two parabolic core

Every automorphism preserves the characteristic binary quotient and its unique
fiber consisting entirely of elements of order four. The four linear forms
nonzero on the corresponding distinguished vector are therefore permuted.
Pullback by inverse automorphisms gives a left action; its first two points
represent the restricted core and mixed characters.

The core acts trivially on this quotient. Conjugation by root 3, outside the
core, sends `(t,u,v)` to `(t,u+t,v+t)` and swaps just the last two forms. A
kernel-checked calculation in the verified Sylow model certifies this formula.
Thus the specified Sylow action has precisely the required transposition image.

Source: Shinoda (1975), (2.3), pp. 81–83, via `FirstParabolicCoordinates` and
the verified root model. The parabolic terminology follows van Beek (2024),
Proposition 3.1, p. 10; no external automorphism census is assumed.
-/

namespace ReeTwo.SylowModel

private abbrev V := Multiplicative (Fin 3 → ZMod 2)

private def detectingForm : Fin 4 → (Fin 3 → ZMod 2) → ZMod 2 := ![
  fun v => v 1 + v 2,
  fun v => v 0 + v 1 + v 2,
  fun v => v 2,
  fun v => v 0 + v 2]

private theorem detectingForm_complete (l : (Fin 3 → ZMod 2) → ZMod 2)
    (hadd : ∀ v w, l (v + w) = l v + l w)
    (hd : l firstParabolicDistinguished = 1) : ∃ i, ∀ v, l v = detectingForm i v := by
  have hz : l 0 = 0 := by
    have h := hadd 0 0
    simpa using (add_left_cancel (show l 0 + l 0 = l 0 + 0 by simpa using h.symm))
  have hscale (z : ZMod 2) (v : Fin 3 → ZMod 2) : l (z • v) = z * l v := by
    fin_cases z
    · change l ((0 : ZMod 2) • v) = (0 : ZMod 2) * l v
      simp [hz]
    · change l ((1 : ZMod 2) • v) = (1 : ZMod 2) * l v
      simp
  have hexp (v : Fin 3 → ZMod 2) :
      v = v 0 • ![1, 0, 0] + v 1 • ![0, 1, 0] + v 2 • ![0, 0, 1] := by
    ext i
    fin_cases i <;> simp
  have hc : ∀ a b : ZMod 2, ∃ i, ∀ v : Fin 3 → ZMod 2,
      v 0 * a + v 1 * b + v 2 = detectingForm i v := by decide +kernel
  obtain ⟨i, hi⟩ := hc (l ![1, 0, 0]) (l ![0, 1, 0])
  refine ⟨i, fun v => ?_⟩
  calc
    l v = l (v 0 • ![1, 0, 0] + v 1 • ![0, 1, 0] + v 2 • ![0, 0, 1]) := congrArg l (hexp v)
    _ = v 0 * l ![1, 0, 0] + v 1 * l ![0, 1, 0] + v 2 := by
      rw [hadd, hadd, hscale, hscale, hscale]
      change _ + v 2 * l firstParabolicDistinguished = _
      rw [hd, mul_one]
    _ = detectingForm i v := hi v

private theorem detectingForm_injective : Function.Injective detectingForm := by decide +kernel

private theorem detectingForm_add :
    ∀ i v w, detectingForm i (v + w) = detectingForm i v + detectingForm i w := by
  decide +kernel

private theorem detectingForm_perm_exists (e : V ≃* V)
    (hd : (e (Multiplicative.ofAdd firstParabolicDistinguished)).toAdd =
      firstParabolicDistinguished) :
    ∃ p : Equiv.Perm (Fin 4), ∀ i v,
      detectingForm i (e (Multiplicative.ofAdd v)).toAdd = detectingForm (p i) v := by
  classical
  have hc (i : Fin 4) :
      ∃ j, ∀ v, detectingForm i (e (Multiplicative.ofAdd v)).toAdd = detectingForm j v := by
    apply detectingForm_complete
    · intro v w
      change detectingForm i (e (Multiplicative.ofAdd v * Multiplicative.ofAdd w)).toAdd = _
      rw [map_mul]
      exact detectingForm_add _ _ _
    · rw [hd]
      exact (by decide : ∀ i, detectingForm i firstParabolicDistinguished = 1) i
  choose f hf using hc
  have hinj : Function.Injective f := by
    intro i j hij
    apply detectingForm_injective
    funext v
    obtain ⟨w, hw⟩ := e.surjective (Multiplicative.ofAdd v)
    have hi := hf i w.toAdd
    have hj := hf j w.toAdd
    rw [hij] at hi
    have heq := hi.trans hj.symm
    change detectingForm i (e w).toAdd = detectingForm j (e w).toAdd at heq
    simpa only [hw, toAdd_ofAdd] using heq
  exact ⟨Equiv.ofBijective f ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩,
    fun i v => hf i v⟩

private theorem detectingForm_perm_ext (p q : Equiv.Perm (Fin 4))
    (h : ∀ i v, detectingForm (p i) v = detectingForm (q i) v) : p = q := by
  apply Equiv.ext
  intro i
  exact detectingForm_injective (funext (h i))

private theorem quotient_kernel_map (a : MulAut firstParabolicCore) :
    firstParabolicQuotient.ker ≤ (firstParabolicQuotient.comp a).ker := by
  intro x hx
  apply MonoidHom.mem_ker.mpr
  exact ((Subgroup.characteristic_iff_le_comap.mp
    firstParabolicQuotient_ker_characteristic) a) hx

private noncomputable def quotientMap (a : MulAut firstParabolicCore) : V →* V :=
  firstParabolicQuotient.liftOfSurjective firstParabolicQuotient_surjective
    ⟨firstParabolicQuotient.comp a, quotient_kernel_map a⟩

private theorem quotientMap_comp (a : MulAut firstParabolicCore) (x : firstParabolicCore) :
    quotientMap a (firstParabolicQuotient x) = firstParabolicQuotient (a x) := by
  exact MonoidHom.liftOfRightInverse_comp_apply firstParabolicQuotient
    (Function.surjInv firstParabolicQuotient_surjective)
    (Function.rightInverse_surjInv firstParabolicQuotient_surjective)
    ⟨firstParabolicQuotient.comp a, quotient_kernel_map a⟩ x

private theorem quotientMap_inv (a : MulAut firstParabolicCore) :
    Function.LeftInverse (quotientMap a⁻¹) (quotientMap a) := by
  intro v
  obtain ⟨x, rfl⟩ := firstParabolicQuotient_surjective v
  rw [quotientMap_comp, quotientMap_comp]
  simp

private theorem quotientMap_bijective (a : MulAut firstParabolicCore) :
    Function.Bijective (quotientMap a) := by
  have hi := quotientMap_inv a
  refine ⟨fun x y h => hi.injective h, fun y => ?_⟩
  exact ⟨quotientMap a⁻¹ y, by simpa using (quotientMap_inv a⁻¹ y)⟩

private noncomputable def quotientEquiv (a : MulAut firstParabolicCore) : V ≃* V :=
  MulEquiv.ofBijective (quotientMap a) (quotientMap_bijective a)

private theorem quotientEquiv_apply (a : MulAut firstParabolicCore) (x : firstParabolicCore) :
    quotientEquiv a (firstParabolicQuotient x) = firstParabolicQuotient (a x) :=
  quotientMap_comp a x

private theorem quotientEquiv_fix_distinguished (a : MulAut firstParabolicCore) :
    (quotientEquiv a (Multiplicative.ofAdd firstParabolicDistinguished)).toAdd =
      firstParabolicDistinguished := by
  apply (firstParabolicQuotient_fiber_order_four_iff _).mp
  intro y hy
  obtain ⟨x, rfl⟩ := a.surjective y
  have hq : firstParabolicQuotient x =
      Multiplicative.ofAdd firstParabolicDistinguished := by
    apply (quotientEquiv a).injective
    rw [quotientEquiv_apply]
    simpa only [ofAdd_toAdd] using hy
  have hx : orderOf x = 4 :=
    (firstParabolicQuotient_fiber_order_four_iff _).mpr rfl x hq
  exact (a.orderOf_eq x).trans hx

private noncomputable def detectingPerm (a : MulAut firstParabolicCore) : Equiv.Perm (Fin 4) :=
  Classical.choose (detectingForm_perm_exists (quotientEquiv a)
    (quotientEquiv_fix_distinguished a))

private theorem detectingPerm_spec (a : MulAut firstParabolicCore) (i : Fin 4)
    (v : Fin 3 → ZMod 2) :
    detectingForm i (quotientEquiv a (Multiplicative.ofAdd v)).toAdd =
      detectingForm (detectingPerm a i) v :=
  Classical.choose_spec (detectingForm_perm_exists (quotientEquiv a)
    (quotientEquiv_fix_distinguished a)) i v

private theorem quotientEquiv_mul (a b : MulAut firstParabolicCore) :
    quotientEquiv (a * b) = quotientEquiv a * quotientEquiv b := by
  apply MulEquiv.ext
  intro v
  obtain ⟨x, rfl⟩ := firstParabolicQuotient_surjective v
  rw [MulAut.mul_apply, quotientEquiv_apply, quotientEquiv_apply, quotientEquiv_apply]
  rfl

private theorem quotientEquiv_one : quotientEquiv (1 : MulAut firstParabolicCore) = 1 := by
  apply MulEquiv.ext
  intro v
  obtain ⟨x, rfl⟩ := firstParabolicQuotient_surjective v
  rw [quotientEquiv_apply]
  rfl

private theorem detectingPerm_one : detectingPerm (1 : MulAut firstParabolicCore) = 1 := by
  apply detectingForm_perm_ext
  intro i v
  rw [← detectingPerm_spec, quotientEquiv_one]
  rfl

private theorem detectingPerm_mul (a b : MulAut firstParabolicCore) :
    detectingPerm (a * b) = detectingPerm b * detectingPerm a := by
  apply detectingForm_perm_ext
  intro i v
  rw [← detectingPerm_spec, quotientEquiv_mul, MulAut.mul_apply]
  calc
    _ = detectingForm (detectingPerm a i) ((quotientEquiv b) (Multiplicative.ofAdd v)).toAdd := by
      simpa only [ofAdd_toAdd] using
        detectingPerm_spec a i ((quotientEquiv b) (Multiplicative.ofAdd v)).toAdd
    _ = _ := detectingPerm_spec b (detectingPerm a i) v

/-- Inverse pullback on the four forms detecting the distinguished quotient vector. -/
public noncomputable def firstParabolicCharacterAction :
    MulAut firstParabolicCore →* Equiv.Perm (Fin 4) where
  toFun a := detectingPerm a⁻¹
  map_one' := by simpa using detectingPerm_one
  map_mul' a b := by
    rw [mul_inv_rev, detectingPerm_mul]

private theorem firstParabolicCharacterAction_spec (a : MulAut firstParabolicCore)
    (i : Fin 4) (v : Fin 3 → ZMod 2) :
    detectingForm i (quotientEquiv a⁻¹ (Multiplicative.ofAdd v)).toAdd =
      detectingForm (firstParabolicCharacterAction a i) v :=
  detectingPerm_spec a⁻¹ i v

private theorem quotientEquiv_inner (s : firstParabolicCore) :
    quotientEquiv (firstParabolicAction s) = 1 := by
  apply MulEquiv.ext
  intro v
  obtain ⟨x, rfl⟩ := firstParabolicQuotient_surjective v
  rw [quotientEquiv_apply]
  change firstParabolicQuotient (s * x * s⁻¹) = firstParabolicQuotient x
  simp [map_mul, map_inv]

private theorem action_inner (s : firstParabolicCore) :
    firstParabolicCharacterAction (firstParabolicAction s) = 1 := by
  apply detectingForm_perm_ext
  intro i v
  rw [← firstParabolicCharacterAction_spec]
  have he : (firstParabolicAction (s : SylowModel))⁻¹ =
      firstParabolicAction (s⁻¹ : firstParabolicCore) := by simp
  rw [he, quotientEquiv_inner]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem coordinates_conj_root : ∀ x : SylowModel,
    firstParabolicCoordinates ((root 0) * x * (root 0)⁻¹) =
      ![firstParabolicCoordinates x 0,
        firstParabolicCoordinates x 1 + firstParabolicCoordinates x 0,
        firstParabolicCoordinates x 2 + firstParabolicCoordinates x 0] := by
  decide +kernel

private theorem action_root :
    firstParabolicCharacterAction (firstParabolicAction (root 0)) =
      Equiv.swap (2 : Fin 4) 3 := by
  apply detectingForm_perm_ext
  intro i v
  rw [← firstParabolicCharacterAction_spec]
  have hi : (firstParabolicAction (root 0))⁻¹ = firstParabolicAction (root 0) := by
    rw [← map_inv]
    congr 1
  rw [hi]
  obtain ⟨x, hx⟩ := firstParabolicQuotient_surjective (Multiplicative.ofAdd v)
  have hc : firstParabolicCoordinates x = v := congrArg Multiplicative.toAdd hx
  rw [← hx, quotientEquiv_apply]
  change detectingForm i (firstParabolicCoordinates ((root 0) * x * (root 0)⁻¹)) = _
  rw [coordinates_conj_root, hc]
  exact (by decide : ∀ i v, detectingForm i ![v 0, v 1 + v 0, v 2 + v 0] =
    detectingForm (Equiv.swap (2 : Fin 4) 3 i) v) i v

private theorem firstParabolicCharacterAction_on_action (s : SylowModel) :
    firstParabolicCharacterAction (firstParabolicAction s) =
      if s.left.b0 = 0 then 1 else Equiv.swap (2 : Fin 4) 3 := by
  by_cases hs : s.left.b0 = 0
  · rw [if_pos hs]
    exact action_inner ⟨s, (mem_firstParabolicCore_iff s).mpr hs⟩
  · rw [if_neg hs]
    have hmem : (root 0)⁻¹ * s ∈ firstParabolicCore := by
      rw [mem_firstParabolicCore_iff]
      change 1 + s.left.b0 = 0
      exact (by decide : ∀ z : ZMod 2, z ≠ 0 → 1 + z = 0) _ hs
    have he : s = root 0 * ((root 0)⁻¹ * s) := by simp
    calc
      _ = firstParabolicCharacterAction (firstParabolicAction (root 0)) *
          firstParabolicCharacterAction (firstParabolicAction ((root 0)⁻¹ * s)) := by
        rw [← map_mul, ← map_mul, ← he]
      _ = _ := by rw [action_root, action_inner ⟨_, hmem⟩, mul_one]

/-- The prescribed Sylow action swaps the last two forms and fixes the first two. -/
public theorem firstParabolicCharacterAction_range_map :
    firstParabolicAction.range.map firstParabolicCharacterAction =
      Subgroup.zpowers (Equiv.swap (2 : Fin 4) 3) := by
  apply le_antisymm
  · rintro y ⟨a, ⟨s, rfl⟩, rfl⟩
    rw [firstParabolicCharacterAction_on_action]
    split_ifs
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · apply Subgroup.zpowers_le.mpr
    exact ⟨_, ⟨root 0, rfl⟩, action_root⟩

private theorem coreCharacter_detectingForm (x : firstParabolicCore) :
    coreCharacter (x : SylowModel) =
      Multiplicative.ofAdd (detectingForm 0 (firstParabolicQuotient x).toAdd) := by
  change Multiplicative.ofAdd ((x : SylowModel).left.b1 + (x : SylowModel).left.b2 +
    (x : SylowModel).left.b3) = Multiplicative.ofAdd ((x : SylowModel).left.b1 +
      ((x : SylowModel).left.b2 + (x : SylowModel).left.b3))
  rw [add_assoc]

private theorem mixedCharacter_detectingForm (x : firstParabolicCore) :
    mixedCharacter (x : SylowModel) =
      Multiplicative.ofAdd (detectingForm 1 (firstParabolicQuotient x).toAdd) := by
  rw [mixedCharacter, MonoidHom.mul_apply, coreCharacter_detectingForm]
  change Multiplicative.ofAdd ((x : SylowModel).left.b1 +
    ((x : SylowModel).left.b2 + (x : SylowModel).left.b3)) *
      parity (x : SylowModel).right = Multiplicative.ofAdd
      ((parity (x : SylowModel).right).toAdd + (x : SylowModel).left.b1 +
        ((x : SylowModel).left.b2 + (x : SylowModel).left.b3))
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_ofAdd]
  abel

private theorem character_action_of_fixed_zero
    (a : MulAut firstParabolicCore)
    (ha : firstParabolicCharacterAction a 0 = 0) :
    ∀ x : firstParabolicCore,
      coreCharacter (a x : SylowModel) = coreCharacter x := by
  have hai : firstParabolicCharacterAction a⁻¹ 0 = 0 := by
    rw [map_inv]
    apply (firstParabolicCharacterAction a).injective
    simpa using ha.symm
  intro x
  have h := firstParabolicCharacterAction_spec a⁻¹ 0
    (firstParabolicQuotient x).toAdd
  rw [inv_inv, ofAdd_toAdd, quotientEquiv_apply, hai] at h
  rw [coreCharacter_detectingForm, coreCharacter_detectingForm]
  exact congrArg Multiplicative.ofAdd h

private theorem character_action_of_fixed_one
    (a : MulAut firstParabolicCore)
    (ha : firstParabolicCharacterAction a 1 = 1) :
    ∀ x : firstParabolicCore,
      mixedCharacter (a x : SylowModel) = mixedCharacter x := by
  have hai : firstParabolicCharacterAction a⁻¹ 1 = 1 := by
    rw [map_inv]
    apply (firstParabolicCharacterAction a).injective
    simpa using ha.symm
  intro x
  have h := firstParabolicCharacterAction_spec a⁻¹ 1
    (firstParabolicQuotient x).toAdd
  rw [inv_inv, ofAdd_toAdd, quotientEquiv_apply, hai] at h
  rw [mixedCharacter_detectingForm, mixedCharacter_detectingForm]
  exact congrArg Multiplicative.ofAdd h

/-- Fixing the first form means preserving the restricted core character. -/
public theorem firstParabolicCharacterAction_core_fixed
    (a : MulAut firstParabolicCore)
    (ha : firstParabolicCharacterAction a 0 = 0) :
    ∀ x : firstParabolicCore,
      coreCharacter (a x : SylowModel) = coreCharacter x :=
  character_action_of_fixed_zero a ha

/-- Fixing the second form means preserving the restricted mixed character. -/
public theorem firstParabolicCharacterAction_mixed_fixed
    (a : MulAut firstParabolicCore)
    (ha : firstParabolicCharacterAction a 1 = 1) :
    ∀ x : firstParabolicCore,
      mixedCharacter (a x : SylowModel) = mixedCharacter x :=
  character_action_of_fixed_one a ha

end ReeTwo.SylowModel
