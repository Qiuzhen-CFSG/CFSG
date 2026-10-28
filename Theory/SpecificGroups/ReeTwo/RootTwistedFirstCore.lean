module

public import Theory.SpecificGroups.ReeTwo.RootTwistedCoordinates

/-!
# The marked involution of the root-twisted first core

The first core is the subgroup with zero initial root coordinate. Its center
has order four. Square-root centralizers distinguish the last root from the
other two central involutions, making it invariant under every automorphism.

Source: direct calculations in the Shinoda (1975), pp.81–83 coordinates
implemented in `Core`, `CoreRootTwist`, and `RootTwistedSylow`.
-/

open scoped commutatorElement
namespace ReeTwo.RootTwistedSylow

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem center_test : ∀ g : RootTwistedSylow,
    g * root 0 = root 0 * g → g * root 2 = root 2 * g →
    g * actor = actor * g → g = 1 ∨ g = root 9 := by
  decide +kernel

private theorem center_cases (g : RootTwistedSylow)
    (hg : g ∈ Subgroup.center RootTwistedSylow) : g = 1 ∨ g = root 9 :=
  center_test g (Subgroup.mem_center_iff.mp hg _).symm
    (Subgroup.mem_center_iff.mp hg _).symm (Subgroup.mem_center_iff.mp hg _).symm

private def commuteModLast (x y : RootTwistedSylow) : Prop :=
  x * y = y * x ∨ x * y = root 9 * (y * x)
private instance (x y : RootTwistedSylow) : Decidable (commuteModLast x y) := by
  unfold commuteModLast
  infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem second_center_test : ∀ g : RootTwistedSylow,
    commuteModLast g (root 0) → commuteModLast g (root 2) →
    commuteModLast g actor →
    g = 1 ∨ g = root 8 ∨ g = root 9 ∨ g = root 8 * root 9 := by
  decide +kernel

private theorem commuteModLast_of_mem_second_center (g : RootTwistedSylow)
    (hg : g ∈ Subgroup.upperCentralSeries RootTwistedSylow 2) (y : RootTwistedSylow) :
    commuteModLast g y := by
  have h := Subgroup.mem_upperCentralSeries_succ_iff.mp hg y
  rw [Subgroup.upperCentralSeries_one] at h
  rcases center_cases _ h with h | h
  · left
    have he := congrArg (fun t => t * y * g) h
    simpa [commutatorElement_def, mul_assoc] using he
  · right
    have he := congrArg (fun t => t * y * g) h
    simpa [commutatorElement_def, mul_assoc] using he

/-- Elements of the second center are products of roots 11 and 12. -/
public theorem second_center_cases (g : RootTwistedSylow)
    (hg : g ∈ Subgroup.upperCentralSeries RootTwistedSylow 2) :
    g = 1 ∨ g = root 8 ∨ g = root 9 ∨ g = root 8 * root 9 :=
  second_center_test g (commuteModLast_of_mem_second_center g hg _)
    (commuteModLast_of_mem_second_center g hg _)
    (commuteModLast_of_mem_second_center g hg _)

private theorem action_last (t : FiveFour.Cyclic 4) (i : CoreRoot)
    (hi : i = 8 ∨ i = 9) :
    rootTwistedAction t (Core.root i) = Core.root i := by
  exact (by decide +kernel : ∀ t : FiveFour.Cyclic 4, ∀ i : CoreRoot,
    i = 8 ∨ i = 9 → rootTwistedAction t (Core.root i) =
      Core.root i) t i hi

private theorem core_mul_eq (x y : Core) : x * y = Core.mul x y := rfl

private theorem root_nine_commute (g : RootTwistedSylow) : root 9 * g = g * root 9 := by
  apply SemidirectProduct.ext
  · change Core.root 9 * rootTwistedAction 1 g.left =
      g.left * rootTwistedAction g.right (Core.root 9)
    rw [map_one, MulAut.one_apply, action_last _ _ (Or.inr rfl)]
    apply Core.ext <;> simp [core_mul_eq, Core.mul, Core.root, Core.ofCoords]
    ring
  · simp [root]

private theorem root_nine_mem_center : root 9 ∈ Subgroup.center RootTwistedSylow := by
  exact Subgroup.mem_center_iff.mpr (fun g => (root_nine_commute g).symm)

private theorem root_eight_commute_iff (g : RootTwistedSylow) :
    g * root 8 = root 8 * g ↔ g.left.b0 = 0 := by
  have hl : (g * root 8).left = g.left * Core.root 8 := by
    change g.left * rootTwistedAction g.right (Core.root 8) = _
    rw [action_last _ _ (Or.inl rfl)]
  have hr : (root 8 * g).left = Core.root 8 * g.left := by
    change Core.root 8 * rootTwistedAction 1 g.left = _
    rw [map_one, MulAut.one_apply]
  constructor
  · intro h
    have he := congrArg (fun x : RootTwistedSylow => x.left.b9) h
    change (g * root 8).left.b9 = (root 8 * g).left.b9 at he
    rw [hl, hr] at he
    simpa [core_mul_eq, Core.mul, Core.root, Core.ofCoords, eq_comm] using he
  · intro h
    apply SemidirectProduct.ext
    · rw [hl, hr]
      apply Core.ext <;> simp [core_mul_eq, Core.mul, Core.root, Core.ofCoords, h]
      ring
    · simp [root]

private theorem root_eight_commuteModLast (g : RootTwistedSylow) : commuteModLast (root 8) g := by
  rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) g.left.b0 with h | h
  · exact Or.inl ((root_eight_commute_iff g).mpr h).symm
  · right
    apply SemidirectProduct.ext
    · change Core.root 8 * rootTwistedAction 1 g.left =
        Core.root 9 * rootTwistedAction 1
          (g.left * rootTwistedAction g.right (Core.root 8))
      rw [map_one, MulAut.one_apply, MulAut.one_apply,
        action_last _ _ (Or.inl rfl)]
      apply Core.ext <;> simp [core_mul_eq, Core.mul, Core.root, Core.ofCoords, h]
      ring
    · simp [root]

private theorem root_eight_mem_second_center :
    root 8 ∈ Subgroup.upperCentralSeries RootTwistedSylow 2 := by
  apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
  intro g
  rw [Subgroup.upperCentralSeries_one]
  rcases root_eight_commuteModLast g with h | h
  · have he : ⁅root 8, g⁆ = 1 := by rw [commutatorElement_def, h]; simp [mul_assoc]
    rw [he]
    exact (Subgroup.center RootTwistedSylow).one_mem
  · have he : ⁅root 8, g⁆ = root 9 := by rw [commutatorElement_def, h]; simp [mul_assoc]
    rw [he]
    exact root_nine_mem_center

/-- Membership in the intrinsic first core is the vanishing of `b0`. -/
@[simp] public theorem mem_firstCore_iff (g : RootTwistedSylow) :
    g ∈ firstCore ↔ g.left.b0 = 0 := by
  constructor
  · intro h
    apply (root_eight_commute_iff g).mp
    exact (Subgroup.mem_centralizer_iff.mp h _ root_eight_mem_second_center).symm
  · intro h
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    rcases second_center_cases x hx with rfl | rfl | rfl | rfl
    · simp
    · exact ((root_eight_commute_iff g).mpr h).symm
    · exact root_nine_commute g
    · rw [mul_assoc, root_nine_commute, ← mul_assoc,
        ((root_eight_commute_iff g).mpr h).symm, mul_assoc]


private abbrev Bits := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private abbrev Params := Bits × FiveFour.Cyclic 4
private def elt (p : Params) : RootTwistedSylow :=
  ⟨⟨0, p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2.1,
    p.1.2.2.2.2.2.1, p.1.2.2.2.2.2.2.1, p.1.2.2.2.2.2.2.2.1, p.1.2.2.2.2.2.2.2.2⟩,p.2⟩
private def count (x : RootTwistedSylow) : ℕ := Fintype.card {p : Params // coordinateMul (elt p) x = coordinateMul x (elt p)}

private def parameterEquiv : firstCore ≃ Params where
  toFun x := ((x.val.left.b1, x.val.left.b2, x.val.left.b3, x.val.left.b4,
    x.val.left.b5, x.val.left.b6, x.val.left.b7, x.val.left.b8, x.val.left.b9), x.val.right)
  invFun p := ⟨elt p, (mem_firstCore_iff _).mpr rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact Core.ext ((mem_firstCore_iff _).mp x.property).symm rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · rfl
  right_inv p := rfl

/-- The intrinsic first core has order 2048. -/
public theorem firstCore_card : Nat.card firstCore = 2048 := by
  rw [Nat.card_congr parameterEquiv, Nat.card_eq_fintype_card]
  decide +kernel

private noncomputable def centralizerSize (x : firstCore) : ℕ := Nat.card {y : firstCore // y * x = x * y}

private theorem centralizerSize_eq (x : firstCore) : centralizerSize x = count x.val := by
  unfold centralizerSize count
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine parameterEquiv.subtypeEquiv ?_
  intro y
  simp only [coordinateMul_eq_mul]
  have he : elt (parameterEquiv y) = y.val := congrArg Subtype.val (parameterEquiv.symm_apply_apply y)
  rw [he]
  exact Subtype.ext_iff

private theorem centralizerSize_aut (a : MulAut firstCore) (x : firstCore) :
    centralizerSize (a x) = centralizerSize x := by
  symm
  apply Nat.card_congr
  refine a.toEquiv.subtypeEquiv ?_
  intro y
  change y * x = x * y ↔ a y * a x = a x * a y
  rw [← map_mul, ← map_mul, a.injective.eq_iff]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
private theorem firstCore_center_test : ∀ p : Params,
    coordinateMul (elt p) (root 1) = coordinateMul (root 1) (elt p) →
    coordinateMul (elt p) (root 2) = coordinateMul (root 2) (elt p) →
    coordinateMul (elt p) (root 3) = coordinateMul (root 3) (elt p) →
    coordinateMul (elt p) (root 4) = coordinateMul (root 4) (elt p) →
    coordinateMul (elt p) actor = coordinateMul actor (elt p) →
    elt p = 1 ∨ elt p = root 8 ∨ elt p = root 9 ∨ elt p = root 8 * root 9 := by
  decide +kernel

private abbrev ReducedBits := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
private abbrev ReducedParams := ReducedBits × FiveFour.Cyclic 4

private def reducedElt (p : ReducedParams) : RootTwistedSylow :=
  ⟨⟨0, p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1,
    p.1.2.2.2.2.1, p.1.2.2.2.2.2.1, p.1.2.2.2.2.2.2, 0, 0⟩, p.2⟩

private def reduceParam (p : Params) : ReducedParams :=
  ((p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2.1,
    p.1.2.2.2.2.2.1, p.1.2.2.2.2.2.2.1), p.2)

private def inside (g : RootTwistedSylow) (h : g.left.b0 = 0) : firstCore :=
  ⟨g, (mem_firstCore_iff _).mpr h⟩

private def centerWord (u v : ZMod 2) : firstCore :=
  inside (root 8) rfl ^ u.val * centralInvolution ^ v.val

private theorem centerWord_mem_center (u v : ZMod 2) : centerWord u v ∈ Subgroup.center firstCore := by
  apply (Subgroup.center firstCore).mul_mem
  · apply (Subgroup.center firstCore).pow_mem
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact (root_eight_commute_iff x.val).mpr ((mem_firstCore_iff _).mp x.property)
  · apply (Subgroup.center firstCore).pow_mem
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact (root_nine_commute x.val).symm

private theorem centerWord_square (u v : ZMod 2) : centerWord u v ^ 2 = 1 := by
  apply Subtype.ext
  exact (by decide +kernel : ∀ u v : ZMod 2,
    ((centerWord u v : firstCore) : RootTwistedSylow) ^ 2 = 1) u v

private theorem centerWord_val (u v : ZMod 2) :
    (centerWord u v : RootTwistedSylow) =
      SemidirectProduct.inl (Core.root 8 ^ u.val * Core.root 9 ^ v.val) := by
  change (SemidirectProduct.inl (Core.root 8)) ^ u.val *
    (SemidirectProduct.inl (Core.root 9)) ^ v.val = _
  rw [map_mul, map_pow, map_pow]

private theorem decomposition (p : Params) :
    elt p = coordinateMul (reducedElt (reduceParam p))
      (centerWord p.1.2.2.2.2.2.2.2.1 p.1.2.2.2.2.2.2.2.2 : RootTwistedSylow) := by
  rw [coordinateMul_eq_mul, centerWord_val]
  apply SemidirectProduct.ext
  · change (elt p).left = Core.mul (reducedElt (reduceParam p)).left
      (rootTwistedAction p.2 (Core.root 8 ^ p.1.2.2.2.2.2.2.2.1.val *
        Core.root 9 ^ p.1.2.2.2.2.2.2.2.2.val))
    rw [map_mul, map_pow, map_pow, action_last _ _ (Or.inl rfl),
      action_last _ _ (Or.inr rfl), Core.root_pow, Core.root_pow]
    change (elt p).left = Core.mul _ (Core.mul _ _)
    apply Core.ext <;> simp [Core.mul, Core.ofCoords, elt, reducedElt, reduceParam]
  · change p.2 = p.2 * 1
    exact (mul_one _).symm

private theorem centralizerSize_mul_center (x c : firstCore) (hc : c ∈ Subgroup.center firstCore) :
    centralizerSize (x * c) = centralizerSize x := by
  apply Nat.card_congr
  refine (Equiv.refl firstCore).subtypeEquiv ?_
  intro y
  change y * (x * c) = (x * c) * y ↔ y * x = x * y
  rw [← mul_assoc y x c, mul_assoc x c y,
    ← Subgroup.mem_center_iff.mp hc y, ← mul_assoc x y c, mul_right_cancel_iff]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
private theorem witness_counts : count (root 3) = 256 ∧ count (root 3 * root 4 * root 5) = 256 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
private theorem reduced_square_count : ∀ p : ReducedParams,
    coordinateMul (reducedElt p) (reducedElt p) = root 9 → count (reducedElt p) = 128 := by
  decide +kernel

private theorem square_root_centralizerSize (x : firstCore) (hx : x ^ 2 = centralInvolution) :
    centralizerSize x = 128 := by
  let p := parameterEquiv x
  let r : firstCore := inside (reducedElt (reduceParam p)) rfl
  let c := centerWord p.1.2.2.2.2.2.2.2.1 p.1.2.2.2.2.2.2.2.2
  have he : elt p = x.val := congrArg Subtype.val (parameterEquiv.symm_apply_apply x)
  have hd : x = r * c := by
    apply Subtype.ext
    change x.val = reducedElt (reduceParam p) * (c : RootTwistedSylow)
    simpa only [coordinateMul_eq_mul, he] using decomposition p
  have hc : c ∈ Subgroup.center firstCore := centerWord_mem_center _ _
  have hsq : r ^ 2 = centralInvolution := by
    rw [hd, (show Commute r c from Subgroup.mem_center_iff.mp hc r).mul_pow,
      centerWord_square, mul_one] at hx
    exact hx
  rw [hd, centralizerSize_mul_center r c hc, centralizerSize_eq]
  apply reduced_square_count
  rw [coordinateMul_eq_mul]
  have hv := congrArg firstCore.subtype hsq
  rw [map_pow] at hv
  change reducedElt (reduceParam p) ^ 2 = root 9 at hv
  simpa only [pow_two] using hv
/-- The center of the first core is contained in the last two root coordinates. -/
public theorem firstCore_center_cases (x : firstCore) (hx : x ∈ Subgroup.center firstCore) :
    x.val = 1 ∨ x.val = root 8 ∨ x.val = root 9 ∨ x.val = root 8 * root 9 := by
  have h (y : RootTwistedSylow) (hy : y.left.b0 = 0) :
      x.val * y = y * x.val :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hx (inside y hy)).symm
  have he : elt (parameterEquiv x) = x.val := congrArg Subtype.val (parameterEquiv.symm_apply_apply x)
  have ht := firstCore_center_test (parameterEquiv x)
  simp only [coordinateMul_eq_mul, he] at ht
  exact ht (h (root 1) rfl) (h (root 2) rfl) (h (root 3) rfl)
    (h (root 4) rfl) (h actor rfl)

/-- The marked involution is central in the first core. -/
public theorem centralInvolution_mem_center : centralInvolution ∈ Subgroup.center firstCore := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact (root_nine_commute x.val).symm

/-- Every automorphism of the twisted first core fixes its marked involution. -/
public theorem centralInvolution_fixed (a : MulAut firstCore) : a centralInvolution = centralInvolution := by
  have hc : a centralInvolution ∈ Subgroup.center firstCore := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := a.surjective y
    simpa only [map_mul] using congrArg a
      (Subgroup.mem_center_iff.mp centralInvolution_mem_center x)
  rcases firstCore_center_cases (a centralInvolution) hc with h | h | h | h
  · have he : centralInvolution = 1 := a.injective (by
      rw [map_one]
      exact Subtype.ext h)
    have hn : (root 9 : RootTwistedSylow) ≠ 1 := by decide +kernel
    exact False.elim (hn (congrArg Subtype.val he))
  · let y : firstCore := inside (root 3) rfl
    have hs : y ^ 2 = a centralInvolution := by
      apply Subtype.ext
      change (root 3 : RootTwistedSylow) ^ 2 = (a centralInvolution).val
      rw [h]
      decide +kernel
    have hp : (a.symm y) ^ 2 = centralInvolution := by
      rw [← map_pow, hs, a.symm_apply_apply]
    have he := square_root_centralizerSize (a.symm y) hp
    rw [centralizerSize_aut, centralizerSize_eq] at he
    have hw := witness_counts.1
    change count (root 3) = 128 at he
    omega
  · exact Subtype.ext h
  · let y : firstCore := inside (root 3 * root 4 * root 5) rfl
    have hs : y ^ 2 = a centralInvolution := by
      apply Subtype.ext
      change (root 3 * root 4 * root 5 : RootTwistedSylow) ^ 2 = (a centralInvolution).val
      rw [h]
      decide +kernel
    have hp : (a.symm y) ^ 2 = centralInvolution := by
      rw [← map_pow, hs, a.symm_apply_apply]
    have he := square_root_centralizerSize (a.symm y) hp
    rw [centralizerSize_aut, centralizerSize_eq] at he
    have hw := witness_counts.2
    change count (root 3 * root 4 * root 5) = 128 at he
    omega

end ReeTwo.RootTwistedSylow
