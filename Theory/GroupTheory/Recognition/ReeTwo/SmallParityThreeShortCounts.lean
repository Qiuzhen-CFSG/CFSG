module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeShortCoordinates
/-!
# Intrinsic profile counts for candidates 458, 459, and 460

The exact subgroup parametrizations transport commuting-element counts to
finite coordinate sets. The last two core coordinates form a central tail;
removing it reduces each centralizer calculation to 32 choices for the tested
element. Kernel-checked tables compute the remaining centralizer sizes.

Order one, two, and four are expressed by power equations. The coordinate
fibers are then counted using these order tests and centralizer formulas,
including the centralizer of the square for row 458. The bijections transport
the counts back to the original subgroup types and quotient homomorphisms.

Source: Shinoda (1975), (2.3), pp. 81–82, through `CollectedOperations` and
`SmallParityThreeShortCoordinates`; profile conventions are from
`SmallParityProfiles`.
-/

@[expose] public section
namespace ReeTwo.SylowModel.SmallParityShort
set_option maxRecDepth 32768

def commutingCount (c : Fin 3) (x : SylowModel) : ℕ :=
  Fintype.card {p : Parameters // collectedMul (element c p) x = collectedMul x (element c p)}

theorem commutingCard_eq (c : Fin 3) (x : Candidate c) :
    MulAut.commutingCard x = commutingCount c x.val := by
  unfold commutingCount
  rw [← Nat.card_eq_fintype_card]
  apply (Nat.card_congr ((parameterEquiv c).subtypeEquiv ?_)).symm
  intro p
  simp only [collectedMul_eq]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩


private def trim (p : Parameters) : Parameters :=
  (p.1, ![p.2 0, p.2 1, p.2 2, 0, 0])

private def tail (a b : ZMod 2) : Parameters := (1, ![0, 0, 0, a, b])

set_option maxHeartbeats 8000000 in
private theorem trim_mul_tail : ∀ (c : Fin 3) (p : Parameters),
    collectedMul (element c (trim p)) (element c (tail (p.2 3) (p.2 4))) = element c p := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem tail_commute : ∀ (c : Fin 3) (p : Parameters) (a b : ZMod 2),
    collectedMul (element c p) (element c (tail a b)) =
      collectedMul (element c (tail a b)) (element c p) := by decide +kernel

private theorem commutingCount_trim (c : Fin 3) (p : Parameters) :
    commutingCount c (element c p) = commutingCount c (element c (trim p)) := by
  change commutingCount c (elementLift c p).val = commutingCount c (elementLift c (trim p)).val
  rw [← commutingCard_eq c (elementLift c p),
    ← commutingCard_eq c (elementLift c (trim p))]
  let z := elementLift c (tail (p.2 3) (p.2 4))
  let x := elementLift c (trim p)
  have he : elementLift c p = x * z := by
    apply Subtype.ext
    exact ((collectedMul_eq _ _).symm.trans (trim_mul_tail c p)).symm
  have hz (y : Candidate c) : y * z = z * y := by
    apply Subtype.ext
    change y.val * (element c (tail (p.2 3) (p.2 4))) =
      (element c (tail (p.2 3) (p.2 4))) * y.val
    rw [← candidate_carrier c y.val y.property, ← collectedMul_eq, ← collectedMul_eq]
    exact tail_commute c _ _ _
  unfold MulAut.commutingCard
  apply Nat.card_congr ((Equiv.refl (Candidate c)).subtypeEquiv ?_)
  intro y
  change y * elementLift c p = elementLift c p * y ↔ y * x = x * y
  rw [he]
  have hr : (x * z) * y = (x * y) * z := by
    rw [mul_assoc, ← hz y, ← mul_assoc]
  rw [hr, ← mul_assoc, mul_right_cancel_iff]

private def centralValue (c : Fin 3) (p : Parameters) : ℕ :=
  if p.1.toAdd.val % 2 = 1 then (if c = 0 then 32 else 16)
  else if p.2 0 ≠ 0 then 32
  else if p.1.toAdd.val = 0 then
    (if p.2 2 = 0 ∧ (c = 0 ∨ p.2 1 = 0) then 128 else 64)
  else if c = 0 then 64
  else if p.2 2 + (if c = 2 then p.2 1 else 0) = 0 then 32 else 64

set_option maxHeartbeats 8000000 in
private theorem centralValue_certificate : ∀ (c : Fin 3) (t : FiveFour.Cyclic 4)
    (a b d : ZMod 2),
    commutingCount c (element c (t, ![a,b,d,0,0])) =
      centralValue c (t, ![a,b,d,0,0]) := by decide +kernel

private theorem commutingCount_element (c : Fin 3) (p : Parameters) :
    commutingCount c (element c p) = centralValue c p := by
  rw [commutingCount_trim]
  exact centralValue_certificate c p.1 (p.2 0) (p.2 1) (p.2 2)

private theorem commutingCard_value (c : Fin 3) (x : Candidate c) :
    MulAut.commutingCard x = centralValue c (parameters x.val) := by
  rw [commutingCard_eq, ← candidate_carrier c x.val x.property, commutingCount_element,
    parameters_element]

private def orderTest (n : ℕ) (x : SylowModel) : Prop :=
  if n = 1 then x = 1 else if n = 2 then collectedPow x 2 = 1 ∧ x ≠ 1
    else collectedPow x 4 = 1 ∧ collectedPow x 2 ≠ 1

private instance (n : ℕ) (x : SylowModel) : Decidable (orderTest n x) := by
  unfold orderTest
  infer_instance

private theorem order_four_iff {G : Type*} [Group G] (x : G) :
    orderOf x = 4 ↔ x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
  constructor
  · intro h
    constructor
    · rw [← h]; exact pow_orderOf_eq_one x
    · intro h2
      have hd := orderOf_dvd_of_pow_eq_one h2
      rw [h] at hd
      norm_num at hd
  · rintro ⟨h4,h2⟩
    exact @orderOf_eq_prime_pow _ _ x 1 2 ⟨by decide⟩ h2 h4

private theorem orderTest_iff {c : Fin 3} (n : ℕ) (hn : n = 1 ∨ n = 2 ∨ n = 4)
    (x : Candidate c) : orderTest n x.val ↔ orderOf x = n := by
  have hp (m : ℕ) : x.val ^ m = 1 ↔ x ^ m = 1 :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have he : x.val = 1 ↔ x = 1 :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rcases hn with rfl | rfl | rfl
  · simp [orderTest, he, orderOf_eq_one_iff]
  · simp [orderTest, collectedPow_eq, hp, he, orderOf_eq_prime_iff]
  · simp [orderTest, collectedPow_eq, hp, order_four_iff]

private def test (c : Fin 3) (k : Fin 3) (x : SylowModel) : Prop :=
  let t := smallParityThreeTests (index c) k
  orderTest t.1 x ∧ centralValue c (parameters x) = t.2.1 ∧
    (t.2.2 = 0 ∨ centralValue c (parameters (collectedPow x 2)) = t.2.2)

private instance (c k : Fin 3) (x : SylowModel) : Decidable (test c k x) := by
  unfold test
  infer_instance

private theorem test_iff (c k : Fin 3) (x : Candidate c) :
    test c k x.val ↔ MulAut.orderCentralizerTest (smallParityThreeTests (index c) k) x := by
  unfold test MulAut.orderCentralizerTest
  dsimp only
  rw [orderTest_iff _ ?_ x, ← commutingCard_value c x]
  · have h := commutingCard_value c (x ^ 2)
    change MulAut.commutingCard (x ^ 2) = centralValue c (parameters (x.val ^ 2)) at h
    rw [collectedPow_eq, ← h]
  · exact (by decide +kernel : ∀ c k : Fin 3,
      (smallParityThreeTests (index c) k).1 = 1 ∨
        (smallParityThreeTests (index c) k).1 = 2 ∨
        (smallParityThreeTests (index c) k).1 = 4) c k

private def fiberCount (c k : Fin 3) (v : SmallParityThreeQuotient) : ℕ :=
  Fintype.card {p : Parameters // coordinates c (element c p) = v ∧ test c k (element c p)}

private theorem fiberCard_eq (c k : Fin 3) (v : SmallParityThreeQuotient) :
    (projection c).predicateFiberCard
      (MulAut.orderCentralizerTest (smallParityThreeTests (index c) k)) v = fiberCount c k v := by
  unfold MonoidHom.predicateFiberCard fiberCount
  rw [← Nat.card_eq_fintype_card]
  apply (Nat.card_congr ((parameterEquiv c).subtypeEquiv ?_)).symm
  intro p
  exact and_congr Iff.rfl (test_iff c k (elementLift c p))

set_option maxHeartbeats 8000000 in
private theorem count_certificate : ∀ (c : Fin 3) (v : SmallParityThreeQuotient),
    (fiberCount c 0 v, fiberCount c 1 v, fiberCount c 2 v) =
      smallParityThreeProfile (index c) v := by decide +kernel

theorem projection_profile (c : Fin 3) (v : SmallParityThreeQuotient) :
    ((projection c).predicateFiberCard (MulAut.orderCentralizerTest (smallParityThreeTests (index c) 0)) v,
     (projection c).predicateFiberCard (MulAut.orderCentralizerTest (smallParityThreeTests (index c) 1)) v,
     (projection c).predicateFiberCard (MulAut.orderCentralizerTest (smallParityThreeTests (index c) 2)) v) =
       smallParityThreeProfile (index c) v := by
  simp only [fiberCard_eq]
  exact count_certificate c v

end ReeTwo.SylowModel.SmallParityShort
