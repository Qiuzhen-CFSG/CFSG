module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.Quotients
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.GroupTheory.CyclicCentralProductEquivalence
import Mathlib.Tactic.FinCases

/-!
# The marked central product `C₄ * Q₈ * Q₈`

The four sign-zero monomials on the adjacent pairs in the two three-letter
blocks give actual embeddings of `QuaternionGroup 2`. Their generators square
to the common central sign and conjugate each other to their inverses. Disjoint
supports prove the exact intersection; the generators commute across blocks.

Parity on the first block separates volume from the quaternion join. The
intersection and cardinality formulas then prove that adjoining volume generates
the entire coordinate group. The quaternion join has center of order two, so the
full center is precisely the cyclic-four volume subgroup. Finally, constant
vectors identify this center with the kernel of the original natural projection.
Both the quaternion and cyclic equivalences retain their marked generators.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.2.2(6),
printed pp.410 and 412 (PDF pp.421 and 423). This proves the intrinsic model's
central-product structure; recognition of an ambient covering radical is separate.
The quaternion homomorphism uses the two-normal-form argument of
`Theory.GroupTheory.QuaternionPresentation`, specialized to the marked generators.
-/

@[expose] public section

namespace EvenCliffordSix.Structure

/-- First left generator, integer mask `000011` (coordinate zero is the low bit). -/
def leftA : Model := ⟨0, ⟨![1, 1, 0, 0, 0, 0], by decide⟩⟩
/-- Second left generator, integer mask `000110`. -/
def leftB : Model := ⟨0, ⟨![0, 1, 1, 0, 0, 0], by decide⟩⟩
/-- First right generator, integer mask `011000`. -/
def rightA : Model := ⟨0, ⟨![0, 0, 0, 1, 1, 0], by decide⟩⟩
/-- Second right generator, integer mask `110000`. -/
def rightB : Model := ⟨0, ⟨![0, 0, 0, 0, 1, 1], by decide⟩⟩

def quaternionWord (a b : Model) : QuaternionGroup 2 → Model
  | .a k => a ^ k.val
  | .xa k => b * a ^ k.val

private theorem cocycle_coords (v w : Fin 6 → F) :
    cocycle v w =
      (v 1 * w 0 + v 2 * w 0 + v 3 * w 0 + v 4 * w 0 + v 5 * w 0) +
      (v 2 * w 1 + v 3 * w 1 + v 4 * w 1 + v 5 * w 1) +
      (v 3 * w 2 + v 4 * w 2 + v 5 * w 2) +
      (v 4 * w 3 + v 5 * w 3) + v 5 * w 4 := by
  have h (i : Fin 6) : Finset.Ioi i = Finset.univ.filter (i < ·) := by
    ext j
    simp
  simp only [cocycle, h, Finset.sum_filter]
  simp [Fin.sum_univ_succ]
  ring

/-- First generator of the left (`false`) or right (`true`) quaternion factor. -/
def factorI (side : Bool) : Model := if side then rightA else leftA
/-- Second generator of the indicated quaternion factor. -/
def factorJ (side : Bool) : Model := if side then rightB else leftB

theorem factorI_sq (side : Bool) : (factorI side) ^ 2 = involution := by
  rw [square]
  apply congrArg centralSign
  cases side <;> norm_num [factorI, factorJ, leftA, leftB, rightA, rightB,
    cocycle_coords, Fin.reduceFinMk, Matrix.cons_val_succ', Matrix.cons_val_zero']
  all_goals decide

theorem factorJ_sq (side : Bool) : (factorJ side) ^ 2 = involution := by
  rw [square]
  apply congrArg centralSign
  cases side <;> norm_num [factorI, factorJ, leftA, leftB, rightA, rightB,
    cocycle_coords, Fin.reduceFinMk, Matrix.cons_val_succ', Matrix.cons_val_zero']
  all_goals decide

private theorem inv_sign (x : Model) : x⁻¹.sign = x.sign + cocycle x.vector.val x.vector.val := rfl

theorem factor_conjugation (side : Bool) : factorJ side * factorI side * (factorJ side)⁻¹ =
    (factorI side)⁻¹ := by
  cases side <;> apply Model.ext
  all_goals norm_num [mul_sign, inv_sign, mul_vector, inv_vector, factorI, factorJ,
    leftA, leftB, rightA, rightB, cocycle_coords, Subtype.ext_iff,
    funext_iff, Fin.forall_fin_succ, Fin.reduceFinMk, Matrix.cons_val_succ', Matrix.cons_val_zero']
  all_goals decide

private theorem cocycle_volume (v : V) :
    cocycle v.val volumeVector.val = cocycle volumeVector.val v.val := by
  have h := (BinaryPermutation.mem_core _ _).mp v.property
  rw [← CharTwo.add_eq_zero]
  have he : cocycle v.val volumeVector.val + cocycle volumeVector.val v.val =
      ∑ i, v.val i := by
    simp [cocycle_coords, volumeVector, Fin.sum_univ_succ]
    ring_nf
    simp only [show (5 : F) = 1 by decide, mul_one]
  exact he.trans h


private theorem order_four_of_square {x : Model} (hx : x ^ 2 = involution) :
    orderOf x = 4 := by
  have hfour : x ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hx, involution_sq]
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) hfour
  intro p hp hd
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hd))
  subst p
  simpa only [Nat.reduceDiv, hx] using involution_ne_one

theorem factorI_order (side : Bool) : orderOf (factorI side) = 4 :=
  order_four_of_square (factorI_sq side)

theorem factorJ_order (side : Bool) : orderOf (factorJ side) = 4 :=
  order_four_of_square (factorJ_sq side)

private theorem rotation_add (c : Model) (hc : orderOf c = 4) (i j : ZMod 4) :
    c ^ (i + j).val = c ^ i.val * c ^ j.val := by
  rw [ZMod.val_add, ← pow_add]
  simpa only [hc] using pow_mod_orderOf c (i.val + j.val)

private theorem rotation_neg (c : Model) (hc : orderOf c = 4) (i : ZMod 4) :
    c ^ (-i).val = (c ^ i.val)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← rotation_add c hc, neg_add_cancel]
  simp

private theorem rotation_sub (c : Model) (hc : orderOf c = 4) (i j : ZMod 4) :
    c ^ (i - j).val = c ^ i.val * (c ^ j.val)⁻¹ := by
  rw [sub_eq_add_neg, rotation_add c hc, rotation_neg c hc]

private theorem pow_mul_twist (c d : Model) (hinv : d * c * d⁻¹ = c⁻¹) (k : ℕ) :
    c ^ k * d = d * (c ^ k)⁻¹ := by
  have h : c * d = d * c⁻¹ := by
    have h' := congrArg Inv.inv hinv
    simp only [mul_inv_rev, inv_inv] at h'
    calc
      c * d = (d * c⁻¹ * d⁻¹) * d := by
        simpa only [mul_assoc] using congrArg (· * d) h'.symm
      _ = d * c⁻¹ := by group
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_assoc, h, ← mul_assoc, ih]
    group

/-- The marked quaternion homomorphism: `a 1` and `xa 0` go to the specified
sign-zero two-letter monomials. -/
def quaternionEmbedding (side : Bool) : QuaternionGroup 2 →* Model where
  toFun := quaternionWord (factorI side) (factorJ side)
  map_one' := by change factorI side ^ 0 = 1; exact pow_zero _
  map_mul' := by
    let c := factorI side
    let d := factorJ side
    have hc : orderOf c = 4 := factorI_order side
    have hsq : d ^ 2 = c ^ 2 := (factorJ_sq side).trans (factorI_sq side).symm
    have ht (i : ZMod 4) : c ^ i.val * d = d * (c ^ i.val)⁻¹ :=
      pow_mul_twist c d (factor_conjugation side) i.val
    rintro (i | i) (j | j)
    · exact rotation_add c hc i j
    · change d * c ^ (j - i).val = c ^ i.val * (d * c ^ j.val)
      rw [rotation_sub c hc, ← mul_assoc (c ^ i.val), ht]
      have hcomm := Commute.pow_pow (Commute.refl c) i.val j.val
      rw [mul_assoc, ← hcomm.inv_left.eq]
    · change d * c ^ (i + j).val = (d * c ^ i.val) * c ^ j.val
      rw [rotation_add c hc, mul_assoc]
    · change c ^ ((2 : ZMod 4) + j - i).val = (d * c ^ i.val) * (d * c ^ j.val)
      rw [rotation_sub c hc, rotation_add c hc]
      change c ^ 2 * c ^ j.val * (c ^ i.val)⁻¹ = _
      calc
        c ^ 2 * c ^ j.val * (c ^ i.val)⁻¹ = c ^ 2 * (c ^ i.val)⁻¹ * c ^ j.val := by
          have hcomm := Commute.pow_pow (Commute.refl c) i.val j.val
          rw [mul_assoc, ← hcomm.inv_left.eq, ← mul_assoc]
        _ = (d * c ^ i.val) * (d * c ^ j.val) := by
          rw [← hsq, pow_two]
          calc
            d * d * (c ^ i.val)⁻¹ * c ^ j.val = d * (c ^ i.val * d) * c ^ j.val := by
              rw [ht]; simp only [mul_assoc]
            _ = _ := by group

@[simp] theorem quaternionEmbedding_a_one (side : Bool) :
    quaternionEmbedding side (.a 1) = factorI side := by
  change factorI side ^ 1 = factorI side
  exact pow_one _

@[simp] theorem quaternionEmbedding_xa_zero (side : Bool) :
    quaternionEmbedding side (.xa 0) = factorJ side := by
  change factorJ side * factorI side ^ 0 = factorJ side
  simp

@[simp] theorem quaternionEmbedding_a_two (side : Bool) :
    quaternionEmbedding side (.a 2) = involution := by
  change factorI side ^ 2 = involution
  exact factorI_sq side

@[simp] theorem pow_vector (x : Model) (n : ℕ) : (x ^ n).vector = n • x.vector := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, add_nsmul]

theorem quaternionEmbedding_injective (side : Bool) :
    Function.Injective (quaternionEmbedding side) := by
  apply (quaternionEmbedding side).ker_eq_bot_iff.mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro q hq
  have h : quaternionEmbedding side q = 1 := hq
  have hs := congrArg Model.sign h
  have hi := congrArg (fun x : Model => x.vector.val (if side then 3 else 0)) h
  have hj := congrArg (fun x : Model => x.vector.val (if side then 5 else 2)) h
  cases side <;> cases q with
  | a k =>
    fin_cases k <;>
      norm_num [quaternionEmbedding, quaternionWord, factorI, factorJ, leftA, leftB,
        rightA, rightB, pow_succ, cocycle_coords,
        Fin.reduceFinMk, Matrix.cons_val_succ', Matrix.cons_val_zero'] at hs hi hj ⊢
    all_goals first | rfl | exact absurd hi (by decide) | exact absurd hs (by decide)
  | xa k =>
    fin_cases k <;>
      norm_num [quaternionEmbedding, quaternionWord, factorI, factorJ, leftA, leftB,
        rightA, rightB, pow_succ, cocycle_coords,
        Fin.reduceFinMk, Matrix.cons_val_succ', Matrix.cons_val_zero'] at hs hi hj ⊢
    all_goals first
      | rfl
      | exact absurd hi (by decide)
      | exact absurd hs (by decide)
      | exact absurd hj (by decide)

/-- The two literal quaternion subgroups of the coordinate group. -/
def quaternionFactor (side : Bool) : Subgroup Model := (quaternionEmbedding side).range
abbrev leftFactor := quaternionFactor false
abbrev rightFactor := quaternionFactor true

noncomputable def quaternionEquiv (side : Bool) : quaternionFactor side ≃* QuaternionGroup 2 :=
  (MonoidHom.ofInjective (quaternionEmbedding_injective side)).symm

@[simp] theorem quaternionEquiv_symm_coe (side : Bool) (q : QuaternionGroup 2) :
    (quaternionEquiv side |>.symm q : Model) = quaternionEmbedding side q := rfl

theorem factorI_mem (side : Bool) : factorI side ∈ quaternionFactor side :=
  ⟨.a 1, quaternionEmbedding_a_one side⟩

theorem factorJ_mem (side : Bool) : factorJ side ∈ quaternionFactor side :=
  ⟨.xa 0, quaternionEmbedding_xa_zero side⟩

theorem involution_mem_factor (side : Bool) : involution ∈ quaternionFactor side :=
  ⟨.a 2, quaternionEmbedding_a_two side⟩

/-- The chosen equivalence remembers the first specified generator. -/
@[simp] theorem quaternionEquiv_factorI (side : Bool) :
    quaternionEquiv side ⟨factorI side, factorI_mem side⟩ = QuaternionGroup.a 1 := by
  apply (quaternionEquiv side).symm.injective
  simp only [MulEquiv.symm_apply_apply]
  exact Subtype.ext (quaternionEmbedding_a_one side).symm

/-- The chosen equivalence remembers the second specified generator. -/
@[simp] theorem quaternionEquiv_factorJ (side : Bool) :
    quaternionEquiv side ⟨factorJ side, factorJ_mem side⟩ = QuaternionGroup.xa 0 := by
  apply (quaternionEquiv side).symm.injective
  simp only [MulEquiv.symm_apply_apply]
  exact Subtype.ext (quaternionEmbedding_xa_zero side).symm

theorem quaternionFactor_eq_closure (side : Bool) :
    quaternionFactor side = Subgroup.closure ({factorI side, factorJ side} : Set Model) := by
  apply le_antisymm
  · rintro x ⟨q, rfl⟩
    cases q with
    | a k => exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) k.val
    | xa k =>
      change factorJ side * factorI side ^ k.val ∈ _
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) k.val)
  · apply (Subgroup.closure_le _).mpr
    rintro x (rfl | rfl)
    · exact factorI_mem side
    · exact factorJ_mem side

theorem leftFactor_support (x : Model) (hx : x ∈ leftFactor) :
    x.vector.val 3 = 0 ∧ x.vector.val 4 = 0 ∧ x.vector.val 5 = 0 := by
  obtain ⟨q, rfl⟩ := hx
  cases q <;> simp [quaternionEmbedding, quaternionWord, pow_vector, factorI, factorJ,
    leftA, leftB]

theorem rightFactor_support (x : Model) (hx : x ∈ rightFactor) :
    x.vector.val 0 = 0 ∧ x.vector.val 1 = 0 ∧ x.vector.val 2 = 0 := by
  obtain ⟨q, rfl⟩ := hx
  cases q <;> simp [quaternionEmbedding, quaternionWord, pow_vector, factorI, factorJ,
    rightA, rightB]

theorem signKernel_le_factor (side : Bool) : signKernel ≤ quaternionFactor side := by
  rw [signKernel_eq_zpowers]
  exact Subgroup.zpowers_le.mpr (involution_mem_factor side)

theorem factor_intersection : leftFactor ⊓ rightFactor = signKernel := by
  apply le_antisymm
  · intro x hx
    have hl := leftFactor_support x hx.1
    have hr := rightFactor_support x hx.2
    apply (mem_signKernel x).mpr
    apply Subtype.ext
    funext i
    fin_cases i
    · exact hr.1
    · exact hr.2.1
    · exact hr.2.2
    · exact hl.1
    · exact hl.2.1
    · exact hl.2.2
  · exact le_inf (signKernel_le_factor false) (signKernel_le_factor true)

theorem factor_intersection_card : Nat.card (leftFactor ⊓ rightFactor : Subgroup Model) = 2 := by
  rw [factor_intersection, signKernel_card]

private theorem generator_commutations :
    Commute leftA rightA ∧ Commute leftA rightB ∧
      Commute leftB rightA ∧ Commute leftB rightB := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals apply Model.ext
  all_goals norm_num [mul_sign, mul_vector, leftA, leftB, rightA, rightB,
    cocycle_coords, Subtype.ext_iff, funext_iff, Fin.forall_fin_succ,
    Fin.reduceFinMk, Matrix.cons_val_succ', Matrix.cons_val_zero']
  all_goals decide

theorem factors_commute (x : Model) (hx : x ∈ leftFactor)
    (y : Model) (hy : y ∈ rightFactor) : x * y = y * x := by
  obtain ⟨p, rfl⟩ := hx
  obtain ⟨q, rfl⟩ := hy
  obtain ⟨hii, hij, hji, hjj⟩ := generator_commutations
  change Commute (quaternionWord leftA leftB p) (quaternionWord rightA rightB q)
  cases p with
  | a i =>
    cases q with
    | a j => exact hii.pow_pow i.val j.val
    | xa j => exact (hij.pow_left i.val).mul_right (hii.pow_pow i.val j.val)
  | xa i =>
    cases q with
    | a j => exact (hji.pow_right j.val).mul_left (hii.pow_pow i.val j.val)
    | xa j =>
      exact (hjj.mul_right (hji.pow_right j.val)).mul_left
        ((hij.pow_left i.val).mul_right (hii.pow_pow i.val j.val))

/-- The extraspecial factor `Q₈ * Q₈` inside the original group. -/
def quaternionJoin : Subgroup Model := leftFactor ⊔ rightFactor

/-- The actual quaternion factors inside their join form the intrinsic central-product
presentation; no abstract group is substituted for that join. -/
noncomputable def quaternionData : Subgroup.QuaternionCentralProductData quaternionJoin where
  left := leftFactor.subgroupOf quaternionJoin
  right := rightFactor.subgroupOf quaternionJoin
  left_model := ⟨(Subgroup.subgroupOfEquivOfLe
    (show leftFactor ≤ quaternionJoin from le_sup_left)).trans (quaternionEquiv false)⟩
  right_model := ⟨(Subgroup.subgroupOfEquivOfLe
    (show rightFactor ≤ quaternionJoin from le_sup_right)).trans (quaternionEquiv true)⟩
  intersection_card := by
    change Nat.card ((leftFactor ⊓ rightFactor).subgroupOf quaternionJoin) = 2
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show leftFactor ⊓ rightFactor ≤ quaternionJoin from inf_le_left.trans le_sup_left)).toEquiv]
    exact factor_intersection_card
  commute := by
    intro b hb c hc
    exact Subtype.ext (factors_commute b hb c hc)
  span := by
    rw [← Subgroup.subgroupOf_sup
      (show leftFactor ≤ quaternionJoin from le_sup_left)
      (show rightFactor ≤ quaternionJoin from le_sup_right)]
    exact Subgroup.subgroupOf_self quaternionJoin

theorem quaternionJoin_card : Nat.card quaternionJoin = 32 := quaternionData.card

theorem quaternionJoin_center_card : Nat.card (Subgroup.center quaternionJoin) = 2 :=
  quaternionData.center_card

/-- Parity on the first coordinate block distinguishes volume from the
quaternion-factor join. -/
def blockParity : Model →* Multiplicative F where
  toFun x := Multiplicative.ofAdd (x.vector.val 0 + x.vector.val 1 + x.vector.val 2)
  map_one' := rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    change (x.vector.val 0 + y.vector.val 0) + (x.vector.val 1 + y.vector.val 1) +
      (x.vector.val 2 + y.vector.val 2) =
        (x.vector.val 0 + x.vector.val 1 + x.vector.val 2) +
        (y.vector.val 0 + y.vector.val 1 + y.vector.val 2)
    abel

theorem quaternionJoin_le_blockParity_ker : quaternionJoin ≤ blockParity.ker := by
  change quaternionFactor false ⊔ quaternionFactor true ≤ blockParity.ker
  apply sup_le
  all_goals rw [quaternionFactor_eq_closure]
  all_goals apply (Subgroup.closure_le _).mpr
  all_goals rintro x (rfl | rfl)
  all_goals apply Multiplicative.toAdd.injective
  all_goals norm_num [blockParity, factorI, factorJ, leftA, leftB, rightA, rightB,
    Fin.reduceFinMk, Matrix.cons_val_succ', Matrix.cons_val_zero']
  all_goals decide

theorem volume_not_mem_quaternionJoin : volume ∉ quaternionJoin := by
  intro h
  have h0 : blockParity volume = 1 := quaternionJoin_le_blockParity_ker h
  have h1 : blockParity volume ≠ 1 := by decide
  exact h1 h0

/-- The volume commutes with every even monomial. -/
theorem volume_mem_center : volume ∈ Subgroup.center Model := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Model.ext
  · change x.sign + 0 + cocycle x.vector.val volumeVector.val =
      0 + x.sign + cocycle volumeVector.val x.vector.val
    rw [cocycle_volume]
    simp
  · exact add_comm x.vector volumeVector

abbrev cyclicFactor : Subgroup Model := Subgroup.zpowers volume

theorem cyclicFactor_le_center : cyclicFactor ≤ Subgroup.center Model :=
  Subgroup.zpowers_le.mpr volume_mem_center

theorem cyclicFactor_card : Nat.card cyclicFactor = 4 := by
  rw [Nat.card_zpowers, volume_order]

/-- The distinguished generator is retained in the cyclic-four coordinates. -/
def cyclicGenerator : cyclicFactor := ⟨volume, Subgroup.mem_zpowers _⟩

private theorem cyclicGenerator_generates (x : cyclicFactor) :
    x ∈ Subgroup.zpowers cyclicGenerator := by
  obtain ⟨n, hn⟩ := x.property
  exact ⟨n, Subtype.ext hn⟩

noncomputable def cyclicFourEquiv : cyclicFactor ≃* Multiplicative (ZMod 4) :=
  (zmodMulEquivOfGenerator (g := cyclicGenerator)
    (by exact cyclicGenerator_generates) cyclicFactor_card).symm

@[simp] theorem cyclicFourEquiv_generator :
    cyclicFourEquiv cyclicGenerator = Multiplicative.ofAdd 1 :=
  zmodMulEquivOfGenerator_symm_apply_generator _ _

theorem signKernel_le_cyclicFactor : signKernel ≤ cyclicFactor := by
  rw [signKernel_eq_zpowers]
  apply Subgroup.zpowers_le.mpr
  rw [← volume_sq]
  exact cyclicFactor.pow_mem (Subgroup.mem_zpowers _) 2

private theorem volumeVector_eq_allOne : volumeVector.val = BinaryPermutation.allOne (Fin 6) := by
  funext i
  fin_cases i <;> rfl

private theorem constant_vector_of_natural_kernel (x : Model) (hx : x ∈ naturalProjection.ker) :
    ∃ a : F, x.vector.val = fun _ => a := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp ((mem_naturalProjection_ker x).mp hx)
  refine ⟨a, ?_⟩
  funext i
  simpa [BinaryPermutation.allOne] using (congrFun ha i).symm

theorem cyclicFactor_le_naturalProjection_ker : cyclicFactor ≤ naturalProjection.ker := by
  apply Subgroup.zpowers_le.mpr
  rw [mem_naturalProjection_ker]
  change volumeVector.val ∈ BinaryPermutation.constants (Fin 6)
  rw [volumeVector_eq_allOne]
  exact Submodule.subset_span (Set.mem_singleton _)

theorem naturalProjection_ker_eq_cyclicFactor : naturalProjection.ker = cyclicFactor := by
  apply le_antisymm ?_ cyclicFactor_le_naturalProjection_ker
  intro x hx
  obtain ⟨a, ha⟩ := constant_vector_of_natural_kernel x hx
  have htwo : ∀ a : F, a = 0 ∨ a = 1 := by decide
  rcases htwo a with rfl | rfl
  · apply signKernel_le_cyclicFactor
    exact (mem_signKernel x).mpr (Subtype.ext ha)
  · have hv : (x * volume⁻¹).vector = 0 := by
      apply Subtype.ext
      funext i
      change x.vector.val i + volumeVector.val i = 0
      rw [ha, volumeVector_eq_allOne]
      exact CharTwo.add_self_eq_zero (1 : F)
    have hm := cyclicFactor.mul_mem (signKernel_le_cyclicFactor ((mem_signKernel _).mpr hv))
      (Subgroup.mem_zpowers volume)
    simpa only [inv_mul_cancel_right] using hm

/-- The cyclic factor and the quaternion join have exactly the original sign overlap. -/
theorem cyclicFactor_intersection : cyclicFactor ⊓ quaternionJoin = signKernel := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha⟩ := constant_vector_of_natural_kernel x
      (cyclicFactor_le_naturalProjection_ker hx.1)
    have hp : x.vector.val 0 + x.vector.val 1 + x.vector.val 2 = 0 :=
      quaternionJoin_le_blockParity_ker hx.2
    rw [ha] at hp
    simp only [CharTwo.add_self_eq_zero, zero_add] at hp
    apply (mem_signKernel x).mpr
    apply Subtype.ext
    change x.vector.val = fun _ => 0
    simpa only [hp] using ha
  · exact le_inf signKernel_le_cyclicFactor ((signKernel_le_factor false).trans le_sup_left)

theorem cyclicFactor_intersection_card :
    Nat.card (cyclicFactor ⊓ quaternionJoin : Subgroup Model) = 2 := by
  rw [cyclicFactor_intersection, signKernel_card]

/-- The three specified factors generate all 64 elements. -/
theorem factors_generate : cyclicFactor ⊔ quaternionJoin = ⊤ := by
  have hn : quaternionJoin ≤ Subgroup.normalizer (cyclicFactor : Set Model) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro y _ x hx
    exact (Subgroup.mem_center_iff.mp (cyclicFactor_le_center hx) y).symm
  have h := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes cyclicFactor quaternionJoin hn
  rw [cyclicFactor_card, quaternionJoin_card, cyclicFactor_intersection_card] at h
  apply Subgroup.eq_top_of_card_eq
  rw [card]
  omega

/-- The center is the cyclic subgroup generated by the specified volume. -/
theorem center_eq_cyclicFactor : Subgroup.center Model = cyclicFactor := by
  apply le_antisymm ?_ cyclicFactor_le_center
  intro x hx
  have hgen : x ∈ cyclicFactor ⊔ quaternionJoin := factors_generate ▸ Subgroup.mem_top x
  change x ∈ (↑(cyclicFactor ⊔ quaternionJoin) : Set Model) at hgen
  rw [Subgroup.coe_mul_of_left_le_normalizer_right cyclicFactor quaternionJoin
    (cyclicFactor_le_center.trans (Subgroup.center_le_normalizer _))] at hgen
  obtain ⟨c, hc, q, hq, he⟩ := hgen
  have hqc : q ∈ Subgroup.center Model := by
    have hm := (Subgroup.center Model).mul_mem
      ((Subgroup.center Model).inv_mem (cyclicFactor_le_center hc)) hx
    simpa only [← he, inv_mul_cancel_left] using hm
  have hqr : (⟨q, hq⟩ : quaternionJoin) ∈ Subgroup.center quaternionJoin := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hqc y)
  have hover := Subgroup.overlap_center cyclicFactor quaternionJoin cyclicFactor_le_center
    quaternionJoin_center_card cyclicFactor_intersection_card
  have hqC : q ∈ cyclicFactor := by
    change (⟨q, hq⟩ : quaternionJoin) ∈ cyclicFactor.subgroupOf quaternionJoin
    rw [hover]
    exact hqr
  exact he ▸ cyclicFactor.mul_mem hc hqC

theorem center_eq_zpowers_volume : Subgroup.center Model = Subgroup.zpowers volume :=
  center_eq_cyclicFactor

theorem center_card : Nat.card (Subgroup.center Model) = 4 := by
  rw [center_eq_cyclicFactor, cyclicFactor_card]

noncomputable def centerFourEquiv : Subgroup.center Model ≃* Multiplicative (ZMod 4) :=
  (MulEquiv.subgroupCongr center_eq_cyclicFactor).trans cyclicFourEquiv

@[simp] theorem centerFourEquiv_volume :
    centerFourEquiv ⟨volume, volume_mem_center⟩ = Multiplicative.ofAdd 1 :=
  cyclicFourEquiv_generator

/-- The kernel of the original deleted permutation map is the full center. -/
theorem naturalProjection_ker_eq_center : naturalProjection.ker = Subgroup.center Model :=
  naturalProjection_ker_eq_cyclicFactor.trans center_eq_cyclicFactor.symm

/-- Full-center quotient coordinates, with the original natural projection. -/
noncomputable def centerQuotientEquiv :
    (Model ⧸ Subgroup.center Model) ≃* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
  (QuotientGroup.quotientMulEquivOfEq naturalProjection_ker_eq_center.symm).trans naturalQuotientEquiv

@[simp] theorem centerQuotientEquiv_mk (x : Model) :
    centerQuotientEquiv (QuotientGroup.mk' (Subgroup.center Model) x) = naturalProjection x := rfl

/-- The intrinsic model supplies every model-side premise for cyclic central-product
recognition, and the equivalence preserves the prescribed factor identifications. -/
theorem exists_equiv_of_cyclic_central_product
    {G : Type*} [Group G] [Finite G] (Z Q : Subgroup G) [IsCyclic Z]
    (hZ : Z ≤ Subgroup.center G) (hgen : Z ⊔ Q = ⊤)
    (hover : Nat.card (Z ⊓ Q : Subgroup G) = 2)
    (eZ : cyclicFactor ≃* Z) (eQ : quaternionJoin ≃* Q) :
    ∃ e : Model ≃* G, (∀ z : cyclicFactor, e z = (eZ z : G)) ∧
      ∀ q : quaternionJoin, e q = (eQ q : G) :=
  Subgroup.exists_mulEquiv_of_cyclic_central_products cyclicFactor quaternionJoin Z Q
    cyclicFactor_le_center hZ factors_generate hgen quaternionJoin_center_card
    cyclicFactor_intersection_card hover eZ eQ

end EvenCliffordSix.Structure
