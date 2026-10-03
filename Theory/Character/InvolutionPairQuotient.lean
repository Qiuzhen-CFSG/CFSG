module
public import Theory.Character.InvolutionRootPairing

/-!
# Counting involution products through a quotient

Suppose a homomorphism preserves involutions and the value of a function on
an involution product depends only on whether the quotient pair belongs to
a specified set. If there are m such quotient pairs and each factor has k
involution lifts, their contribution to the pairing is m k² times the common
value, divided by the group order.

Partition the sum over ordered involution pairs into fibers. Each fiber is
the product of the two factor fibers, so its cardinality is k². No
surjectivity or group-theoretic lifting theorem is assumed implicitly.

Source: the counting step in Alperin–Brauer–Gorenstein, III.7 equation (8),
article pp.103–104.
-/

noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
open scoped BigOperators

private theorem sum_pair_fibers {I J : Type*} [Fintype I] [Fintype J]
    (f : I → J) (F : J × J → ℂ) :
    (∑ p : I × I, F (f p.1, f p.2)) =
      ∑ q : J × J, (Nat.card {i : I // f i = q.1} : ℂ) *
        Nat.card {i : I // f i = q.2} * F q := by
  classical
  let ff : I × I → J × J := fun p => (f p.1, f p.2)
  have he (q : J × J) : {p : I × I // ff p = q} ≃
      {i : I // f i = q.1} × {i : I // f i = q.2} := {
    toFun := fun p => (⟨p.val.1, congrArg Prod.fst p.property⟩,
      ⟨p.val.2, congrArg Prod.snd p.property⟩)
    invFun := fun p => ⟨(p.1.val, p.2.val), Prod.ext p.1.property p.2.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  calc
    _ = ∑ q : J × J, ∑ _p : {p : I × I // ff p = q}, F q :=
      (Fintype.sum_fiberwise' ff F).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.card_eq_fintype_card, Nat.card_congr (he q), Nat.card_prod, Nat.cast_mul]

namespace Theory.Character

/-- Evaluate an involution-pair pairing from uniform factor fibers over the
quotient pairs on which the function is nonzero. -/
public theorem scalarProduct_involutionPairCount_eq_of_fibers
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (f : G →* H) (hf : ∀ u : G, orderOf u = 2 → orderOf (f u) = 2)
    (P : H × H → Prop) (k m : ℕ) (v : ℂ) (Φ : ClassFunction G)
    (hvalue : ∀ a b : G, orderOf a = 2 → orderOf b = 2 →
      Φ (a * b) = if P (f a, f b) then v else 0)
    (hfiber : ∀ a b : H, orderOf a = 2 → orderOf b = 2 → P (a, b) →
      Nat.card {u : {u : G // orderOf u = 2} // f u = a} = k ∧
      Nat.card {u : {u : G // orderOf u = 2} // f u = b} = k)
    (hcount : Nat.card
      {p : {a : H // orderOf a = 2} × {a : H // orderOf a = 2} //
        P (p.1, p.2)} = m) :
    scalarProduct G Φ (fun u => (involutionPairCount u : ℂ)) =
      (Nat.card G : ℂ)⁻¹ * ((m : ℂ) * k ^ 2 * v) := by
  classical
  let I := {u : G // orderOf u = 2}
  let J := {u : H // orderOf u = 2}
  let fi : I → J := fun u => ⟨f u, hf u u.property⟩
  have hfi (a : J) : Nat.card {u : I // fi u = a} =
      Nat.card {u : I // f u = a.val} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Subtype.ext_iff)
  rw [scalarProduct_involutionPairCount_eq_sum]
  congr 1
  calc
    _ = ∑ p : I × I, if P ((fi p.1).val, (fi p.2).val) then v else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      exact hvalue p.1 p.2 p.1.property p.2.property
    _ = ∑ q : J × J, (Nat.card {u : I // fi u = q.1} : ℂ) *
        Nat.card {u : I // fi u = q.2} *
          (if P (q.1.val, q.2.val) then v else 0) :=
      sum_pair_fibers fi (fun q => if P (q.1.val, q.2.val) then v else 0)
    _ = ∑ q : J × J, if P (q.1.val, q.2.val) then (k : ℂ)^2 * v else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      by_cases hq : P (q.1.val, q.2.val)
      · obtain ⟨h1, h2⟩ := hfiber q.1 q.2 q.1.property q.2.property hq
        rw [if_pos hq, if_pos hq, hfi, hfi, h1, h2, pow_two]
      · simp [hq]
    _ = _ := by
      have hc : (Finset.univ.filter fun q : J × J => P (q.1.val, q.2.val)).card = m := by
        simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hcount
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, hc, nsmul_eq_mul, mul_assoc]

end Theory.Character
