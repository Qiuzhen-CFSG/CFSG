module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeLongCoordinates

/-!
# Transport of the long rank-three coordinate certificates

An exact identification of the parametrized carrier with the original candidate
transports commuting counts and order tests to intrinsic subgroup predicates.
Together with a homomorphism having the prescribed coordinates and Frattini
kernel, the independent finite fiber-count certificate therefore gives the
required Frattini model. Surjectivity follows from the checked original basis
lifts, rather than from a candidate-order calculation.

Source: the coordinate and profile conventions of `SmallParityThreeLongCoordinates`
and `SmallParityProfiles`, based on Shinoda (1975), (2.3), pp. 81–82.
-/

namespace ReeTwo.SylowModel.SmallParityLong

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

private theorem orderTest_iff {c : Fin 3} (n : ℕ) (hn : n = 2 ∨ n = 4)
    (x : Candidate c) : orderTest n x.val ↔ orderOf x = n := by
  have hp (m : ℕ) : x.val ^ m = 1 ↔ x ^ m = 1 :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have he : x.val = 1 ↔ x = 1 :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rcases hn with rfl | rfl
  · simp [orderTest, collectedPow_eq, hp, he, orderOf_eq_prime_iff]
  · simp [orderTest, collectedPow_eq, hp, order_four_iff]

/-- Assemble one long-row Frattini model from independent structure and count certificates. -/
public theorem model_of_certificates (c : Fin 3)
    (hcarrier : ∀ x : Candidate c, carrier c x.val)
    (helement : ∀ p : Parameters c, element c p ∈ Candidate c)
    (π : Candidate c →* SmallParityThreeQuotient)
    (hπ : ∀ x : Candidate c, π x = coordinates c x.val)
    (hker : π.ker = frattini (Candidate c))
    (hcount : ∀ v : SmallParityThreeQuotient,
      (fiberCount c 0 v, fiberCount c 1 v, fiberCount c 2 v) =
        smallParityThreeProfile (index c) v) :
    SmallParityThreeFrattiniModel (index c) := by
  let e : Parameters c ≃ Candidate c := {
    toFun := fun p => ⟨element c p, helement p⟩
    invFun := fun x => parameters c x.val
    left_inv := parameters_element c
    right_inv := fun x => Subtype.ext (hcarrier x) }
  have hcentral (x : Candidate c) :
      MulAut.commutingCard x = commutingCount c x.val := by
    unfold commutingCount
    rw [← Nat.card_eq_fintype_card]
    apply (Nat.card_congr (e.subtypeEquiv ?_)).symm
    intro p
    simp only [collectedMul_eq]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have htest (k : Fin 3) (x : Candidate c) :
      test c k x.val ↔ MulAut.orderCentralizerTest (smallParityThreeTests (index c) k) x := by
    unfold test MulAut.orderCentralizerTest
    dsimp only
    rw [orderTest_iff _ (tests_spec c k).1 x, ← hcentral x]
    have h := hcentral (x ^ 2)
    change MulAut.commutingCard (x ^ 2) = commutingCount c (x.val ^ 2) at h
    rw [collectedPow_eq, ← h]
  have hfiber (k : Fin 3) (v : SmallParityThreeQuotient) :
      π.predicateFiberCard (MulAut.orderCentralizerTest (smallParityThreeTests (index c) k)) v =
        fiberCount c k v := by
    unfold MonoidHom.predicateFiberCard fiberCount
    rw [← Nat.card_eq_fintype_card]
    apply (Nat.card_congr (e.subtypeEquiv ?_)).symm
    intro p
    rw [hπ]
    exact and_congr Iff.rfl (htest k (e p))
  refine ⟨π, ?_, hker, ?_⟩
  · apply smallParityThree_surjective_of_basis
    intro j
    rw [hπ]
    exact coordinates_basis c j
  · intro v
    simpa only [hfiber] using hcount v

end ReeTwo.SylowModel.SmallParityLong
