module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.FirstParabolic.NonsplitStructure.Counts

/-!
# The actual nonsplit core modulo the marked involution

The original quaternion embeddings descend through quaternionQuotient to two
commuting E4 factors. The actual nonsplit lift becomes an involution modulo z,
interchanging those factors. These maps give a surjection from E4 wr C2 to the
concrete quotient; both groups have order 32, so it is an equivalence.

The resulting map preserves the original z and both quaternion embeddings,
agrees on the quaternion core with splitQuaternionCoreEquiv, and takes that
core's image exactly to the wreath base. No intrinsic two-core identification
or first-parabolic normality is used.

Source: Aschbacher--Smith, 14.2.21, printed p.988, refs/quasithin.pdf.
-/

public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic
open QuaternionSwapModel (C2 E4 W turn quaternionQuotient)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] z nonsplitSwap leftI leftJ rightI rightJ

abbrev OuterQuotient := outerCore ⧸ distinguished.subgroupOf outerCore

@[expose] def outerProjection : outerCore →* OuterQuotient :=
  QuotientGroup.mk' (distinguished.subgroupOf outerCore)

private def qLeft : QuaternionGroup 2 →* OuterQuotient := outerProjection.comp outerLeft
private def qRight : QuaternionGroup 2 →* OuterQuotient := outerProjection.comp outerRight

private theorem outerProjection_neg_left : qLeft (QuaternionGroup.a 2) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  change leftLift (QuaternionGroup.a 2) ∈ distinguished
  rw [leftLift_neg]
  exact Subgroup.mem_zpowers _
private theorem outerProjection_neg_right : qRight (QuaternionGroup.a 2) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  change rightLift (QuaternionGroup.a 2) ∈ distinguished
  rw [rightLift_neg]
  exact Subgroup.mem_zpowers _

private theorem quaternionQuotient_surjective : Function.Surjective quaternionQuotient := by
  decide +kernel
private theorem quaternionQuotient_kernel (q : QuaternionGroup 2)
    (hq : quaternionQuotient q = 1) : q = 1 ∨ q = QuaternionGroup.a 2 := by
  have h : ∀ q : QuaternionGroup 2, quaternionQuotient q = 1 →
      q = 1 ∨ q = QuaternionGroup.a 2 := by decide +kernel
  exact h q hq

noncomputable def quotientLeft : E4 →* OuterQuotient :=
  quaternionQuotient.liftOfSurjective quaternionQuotient_surjective
    ⟨qLeft, by
      intro q hq
      rcases quaternionQuotient_kernel q hq with rfl | rfl
      · exact qLeft.map_one
      · exact outerProjection_neg_left⟩
noncomputable def quotientRight : E4 →* OuterQuotient :=
  quaternionQuotient.liftOfSurjective quaternionQuotient_surjective
    ⟨qRight, by
      intro q hq
      rcases quaternionQuotient_kernel q hq with rfl | rfl
      · exact qRight.map_one
      · exact outerProjection_neg_right⟩

theorem quotientLeft_quaternion (q : QuaternionGroup 2) :
    quotientLeft (quaternionQuotient q) = outerProjection (outerLeft q) := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ q

theorem quotientRight_quaternion (q : QuaternionGroup 2) :
    quotientRight (quaternionQuotient q) = outerProjection (outerRight q) := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ q

@[expose] def quotientSwap : OuterQuotient := outerProjection outerSwap

theorem quotientSwap_square : quotientSwap ^ 2 = 1 := by
  rw [quotientSwap, ← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  change nonsplitSwap^2 ∈ distinguished
  rw [nonsplitSwap_square]
  exact Subgroup.mem_zpowers _

private theorem left_right_commute (m : InnerModel) (q r : QuaternionGroup 2) :
    Commute (outerLeft q) (outerRight r) := by
  apply Subtype.ext
  change leftLift q * rightLift r = rightLift r * leftLift q
  rw [← map_leftLift m, ← map_rightLift m, ← map_mul, ← map_mul]
  exact congrArg m.embedding (M12SmallPair.factors_commute _ ⟨q,rfl⟩ _ ⟨r,rfl⟩)

theorem quotientLeft_commute_right (m : InnerModel) (a b : E4) :
    Commute (quotientLeft a) (quotientRight b) := by
  obtain ⟨q,rfl⟩ := quaternionQuotient_surjective a
  obtain ⟨r,rfl⟩ := quaternionQuotient_surjective b
  rw [quotientLeft_quaternion, quotientRight_quaternion]
  exact (left_right_commute m q r).map outerProjection

theorem quotientSwap_left (a : E4) :
    quotientSwap * quotientLeft a * quotientSwap⁻¹ = quotientRight a := by
  obtain ⟨q,rfl⟩ := quaternionQuotient_surjective a
  rw [quotientLeft_quaternion, quotientRight_quaternion]
  change outerProjection outerSwap * outerProjection (outerLeft q) *
    (outerProjection outerSwap)⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (nonsplitSwap_left q)

theorem quotientSwap_right (a : E4) :
    quotientSwap * quotientRight a * quotientSwap⁻¹ = quotientLeft a := by
  obtain ⟨q,rfl⟩ := quaternionQuotient_surjective a
  rw [quotientLeft_quaternion, quotientRight_quaternion]
  change outerProjection outerSwap * outerProjection (outerRight q) *
    (outerProjection outerSwap)⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (nonsplitSwap_right q)

private theorem c2_cases (c : C2) : c = 1 ∨ c = turn := by
  have h : ∀ c : C2, c = 1 ∨ c = turn := by decide +kernel
  exact h c
private theorem turn_ne_one : turn ≠ 1 := by decide +kernel

@[expose] noncomputable def quotientTurn : C2 →* OuterQuotient where
  toFun c := if c = 1 then 1 else quotientSwap
  map_one' := by simp
  map_mul' c d := by
    rcases c2_cases c with rfl | rfl <;> rcases c2_cases d with rfl | rfl
    · simp
    · simp
    · simp
    · rw [show turn * turn = 1 by decide +kernel]
      simpa [turn_ne_one, ← pow_two] using quotientSwap_square.symm

@[simp] theorem quotientTurn_turn : quotientTurn turn = quotientSwap := by
  change (if turn = 1 then 1 else quotientSwap) = quotientSwap
  exact if_neg turn_ne_one

@[expose] noncomputable def quotientBase (m : InnerModel) : (C2 → E4) →* OuterQuotient where
  toFun f := quotientLeft (f 1) * quotientRight (f turn)
  map_one' := by simp
  map_mul' f g := by
    change quotientLeft (f 1 * g 1) * quotientRight (f turn * g turn) = _
    rw [map_mul, map_mul]
    exact (quotientLeft_commute_right m (g 1) (f turn)).mul_mul_mul_comm _ _

private theorem quotientBase_conj (m : InnerModel) (c : C2) (f : C2 → E4) :
    quotientTurn c * quotientBase m f * (quotientTurn c)⁻¹ =
      quotientBase m (fun t => f (c⁻¹ * t)) := by
  rcases c2_cases c with rfl | rfl
  · simp
  · rw [quotientTurn_turn]
    change quotientSwap * (quotientLeft (f 1) * quotientRight (f turn)) * quotientSwap⁻¹ =
      quotientLeft (f (turn⁻¹ * 1)) * quotientRight (f (turn⁻¹ * turn))
    rw [show turn⁻¹ * 1 = turn by decide +kernel, inv_mul_cancel]
    calc
      _ = (quotientSwap * quotientLeft (f 1) * quotientSwap⁻¹) *
          (quotientSwap * quotientRight (f turn) * quotientSwap⁻¹) := by group
      _ = quotientRight (f 1) * quotientLeft (f turn) := by
        rw [quotientSwap_left, quotientSwap_right]
      _ = _ := (quotientLeft_commute_right m _ _).eq.symm

/-- The wreath generators act in the actual quotient by the original z. -/
@[expose] noncomputable def wreathToOuterQuotient (m : InnerModel) : W →* OuterQuotient where
  toFun w := quotientBase m w.left * quotientTurn w.right
  map_one' := by
    change quotientBase m 1 * quotientTurn 1 = 1
    simp
  map_mul' v w := by
    change quotientBase m (v.left * fun t => w.left (v.right⁻¹ * t)) *
      quotientTurn (v.right * w.right) =
      (quotientBase m v.left * quotientTurn v.right) *
      (quotientBase m w.left * quotientTurn w.right)
    rw [map_mul, map_mul, ← quotientBase_conj]
    group

@[expose] def wreathCoordinate (q r : QuaternionGroup 2) (b : Bool) : W :=
  ⟨fun t => if t = 1 then quaternionQuotient q else quaternionQuotient r,
    if b then turn else 1⟩

theorem wreathToOuterQuotient_coordinate (m : InnerModel)
    (q r : QuaternionGroup 2) (b : Bool) :
    wreathToOuterQuotient m (wreathCoordinate q r b) = outerProjection (coordinate q r b) := by
  change (quotientLeft _ * quotientRight _) * quotientTurn _ = _
  simp only [wreathCoordinate, if_neg turn_ne_one, quotientRight_quaternion]
  cases b <;> simp [coordinate, map_mul, quotientSwap, quotientLeft_quaternion]

theorem wreathToOuterQuotient_surjective (m : InnerModel) :
    Function.Surjective (wreathToOuterQuotient m) := by
  intro x
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (distinguished.subgroupOf outerCore) x
  obtain ⟨q,r,b,rfl⟩ := coordinate_surjective m x
  exact ⟨wreathCoordinate q r b,wreathToOuterQuotient_coordinate m q r b⟩

theorem card_outerQuotient (m : InnerModel) : Nat.card OuterQuotient = 32 := by
  have h := (distinguished.subgroupOf outerCore).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe distinguished_le_outerCore).toEquiv,
    card_distinguished, Subgroup.index_eq_card, card_outerCore m] at h
  change 2 * Nat.card OuterQuotient = 64 at h
  omega

/-- An actual multiplicative equivalence, obtained from the marked quotient generators. -/
@[expose] noncomputable def outerQuotientEquiv (m : InnerModel) : OuterQuotient ≃* W :=
  (MulEquiv.ofBijective (wreathToOuterQuotient m)
    ((Nat.bijective_iff_surjective_and_card _).mpr ⟨wreathToOuterQuotient_surjective m,
      (QuaternionSwapModel.card_W).trans (card_outerQuotient m).symm⟩)).symm

theorem outerQuotientEquiv_coordinate (m : InnerModel)
    (q r : QuaternionGroup 2) (b : Bool) :
    outerQuotientEquiv m (outerProjection (coordinate q r b)) = wreathCoordinate q r b := by
  apply (outerQuotientEquiv m).symm.injective
  rw [MulEquiv.symm_apply_apply]
  exact (wreathToOuterQuotient_coordinate m q r b).symm


/-- The quotient map to the wreath group, on the actual order-64 subgroup. -/
@[expose] noncomputable def outerWreathMap (m : InnerModel) : outerCore →* W :=
  (outerQuotientEquiv m).toMonoidHom.comp outerProjection

theorem outerWreathMap_coordinate (m : InnerModel)
    (q r : QuaternionGroup 2) (b : Bool) :
    outerWreathMap m (coordinate q r b) = wreathCoordinate q r b :=
  outerQuotientEquiv_coordinate m q r b

theorem outerWreathMap_surjective (m : InnerModel) : Function.Surjective (outerWreathMap m) :=
  (outerQuotientEquiv m).surjective.comp (QuotientGroup.mk'_surjective _)

theorem outerWreathMap_left (m : InnerModel) (q : QuaternionGroup 2) :
    outerWreathMap m (outerLeft q) =
      QuaternionSwapModel.wreathMap (QuaternionSwapModel.leftEmbedding q) := by
  have h : coordinate q 1 false = outerLeft q := by simp [coordinate]
  rw [← h, outerWreathMap_coordinate]
  have he : ∀ q : QuaternionGroup 2, wreathCoordinate q 1 false =
      QuaternionSwapModel.rawWreathMap (QuaternionSwapModel.leftRaw q) := by decide +kernel
  exact he q

theorem outerWreathMap_right (m : InnerModel) (q : QuaternionGroup 2) :
    outerWreathMap m (outerRight q) =
      QuaternionSwapModel.wreathMap (QuaternionSwapModel.rightEmbedding q) := by
  have h : coordinate 1 q false = outerRight q := by simp [coordinate]
  rw [← h, outerWreathMap_coordinate]
  have he : ∀ q : QuaternionGroup 2, wreathCoordinate 1 q false =
      QuaternionSwapModel.rawWreathMap (QuaternionSwapModel.rightRaw q) := by decide +kernel
  exact he q

theorem outerWreathMap_swap (m : InnerModel) :
    outerWreathMap m outerSwap = QuaternionSwapModel.rawWreathMap QuaternionSwapModel.swapRaw := by
  have h : coordinate 1 1 true = outerSwap := by simp [coordinate]
  rw [← h, outerWreathMap_coordinate]
  decide +kernel

@[expose] def outerMarked : outerCore := ⟨z,distinguished_le_outerCore (Subgroup.mem_zpowers _)⟩

theorem outerWreathMap_marked (m : InnerModel) : outerWreathMap m outerMarked = 1 := by
  change outerQuotientEquiv m (outerProjection outerMarked) = 1
  have h : outerProjection outerMarked = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers z)
  rw [h, map_one]

/-- On the original quaternion core this is exactly the previously checked split-core map. -/
@[expose] noncomputable def splitCoreToOuter (m : InnerModel) : QuaternionSwapModel.QK →* outerCore :=
  (Subgroup.inclusion (show quaternionCore ≤ outerCore from le_sup_left)).comp
    (splitQuaternionCoreEquiv m).toMonoidHom

theorem outerWreathMap_splitCore (m : InnerModel) (x : QuaternionSwapModel.QK) :
    outerWreathMap m (splitCoreToOuter m x) = QuaternionSwapModel.wreathMap x := by
  have hprod : ∃ q r, QuaternionSwapModel.leftEmbedding q *
      QuaternionSwapModel.rightEmbedding r = x.val := by
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective QuaternionSwapModel.diagonalCenter x.val
    have hr : a.right = 1 := by
      have hx := x.property
      simp only [QuaternionSwapModel.QK_eq_comap_base] at hx
      rw [← ha] at hx
      exact hx
    have hf : ∀ a : QuaternionSwapModel.Raw, a.right = 1 → a =
        QuaternionSwapModel.leftRaw (a.left 1) * QuaternionSwapModel.rightRaw (a.left turn) := by
      decide +kernel
    exact ⟨a.left 1,a.left turn, by
      change QuaternionSwapModel.projection _ * QuaternionSwapModel.projection _ = _
      rw [← map_mul, ← hf a hr]
      exact ha⟩
  obtain ⟨q,r,hqr⟩ := hprod
  let l : QuaternionSwapModel.QK := ⟨QuaternionSwapModel.leftEmbedding q,
    (show QuaternionSwapModel.leftFactor ≤ QuaternionSwapModel.QK from le_sup_left) ⟨q,rfl⟩⟩
  let r' : QuaternionSwapModel.QK := ⟨QuaternionSwapModel.rightEmbedding r,
    (show QuaternionSwapModel.rightFactor ≤ QuaternionSwapModel.QK from le_sup_right) ⟨r,rfl⟩⟩
  have hx : x = l * r' := Subtype.ext hqr.symm
  have hl : splitCoreToOuter m l = outerLeft q := Subtype.ext (splitQuaternionCoreEquiv_left m q)
  have hr : splitCoreToOuter m r' = outerRight r := Subtype.ext (splitQuaternionCoreEquiv_right m r)
  rw [hx, map_mul, map_mul, hl, hr, outerWreathMap_left, outerWreathMap_right]
  exact (map_mul QuaternionSwapModel.wreathMap l.val r'.val).symm

theorem outerWreathMap_mem_base (m : InnerModel) (x : outerCore) :
    outerWreathMap m x ∈ QuaternionSwapModel.base ↔ x.val ∈ quaternionCore := by
  constructor
  · intro hx
    obtain ⟨q,r,b,rfl⟩ := coordinate_surjective m x
    rw [outerWreathMap_coordinate] at hx
    cases b
    · change leftLift q * rightLift r * 1 ∈ quaternionCore
      simpa only [mul_one] using quaternionCore.mul_mem
        (leftLift_mem_quaternionCore q) (rightLift_mem_quaternionCore r)
    · exact False.elim (turn_ne_one hx)
  · intro hx
    obtain ⟨q,r,hqr⟩ := (mem_quaternionCore m x.val).mp hx
    have he : coordinate q r false = x := Subtype.ext (by simpa [coordinate, outerLeft, outerRight] using hqr)
    rw [← he, outerWreathMap_coordinate]
    rfl

theorem outerWreathMap_base (m : InnerModel) :
    (quaternionCore.subgroupOf outerCore).map (outerWreathMap m) = QuaternionSwapModel.base := by
  ext w
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (outerWreathMap_mem_base m x).mpr hx
  · intro hw
    obtain ⟨x,rfl⟩ := outerWreathMap_surjective m w
    exact ⟨x,(outerWreathMap_mem_base m x).mp hw,rfl⟩

/-- The original quaternion-core image corresponds to the base of E4 wr C2. -/
theorem outerQuotientEquiv_base (m : InnerModel) :
    ((quaternionCore.subgroupOf outerCore).map outerProjection).map
      (outerQuotientEquiv m).toMonoidHom = QuaternionSwapModel.base := by
  rw [Subgroup.map_map]
  exact outerWreathMap_base m

end Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic
