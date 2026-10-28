module

public import Theory.GroupTheory.TwoInvolutionClassOrder

/-!
# Thompson counting with support on one conjugacy class

Partition the mixed pairs by their canonical half-order power. If these powers
all lie in the second selected class, their uniform fibers show that the first
class has size `kappa z v v`. The class-size formula then gives the ambient
order. No completeness assertion about the ambient involution classes is used.

Source: the single-support case of Thompson's mixed-involution order formula,
used in GLS, Volume 4, Chapter 2, Lemma 12.8(a),
`refs/KGroup/GLS4/Chapter2.tex`.
-/

open scoped BigOperators
namespace Theory.GroupTheory.TwoInvolutionClassOrder
noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- A mixed-pair count supported on the second selected class. No exhaustion
of the ambient involution classes is required. -/
public theorem card_eq_of_halfOrder_support (z v : G)
    (hsupport : ∀ a b : G, IsConj z a → IsConj v b →
      IsConj v (halfOrder a b)) :
    Nat.card G = kappa z v v * Nat.card (Subgroup.centralizer ({z} : Set G)) := by
  classical
  let P := {p : G × G // IsConj z p.1 ∧ IsConj v p.2}
  let C := {u : G // IsConj v u}
  let e : (Σ u : C, Fiber z v u.val) ≃ P := {
    toFun p := ⟨p.2.val, p.2.property.1, p.2.property.2.1⟩
    invFun p := ⟨⟨halfOrder p.val.1 p.val.2,
      hsupport _ _ p.property.1 p.property.2⟩,
      ⟨p.val, p.property.1, p.property.2, rfl⟩⟩
    left_inv := by
      rintro ⟨⟨u, hu⟩, ⟨⟨a, b⟩, ha, hb, he⟩⟩
      dsimp at he
      subst u
      rfl
    right_inv := by intro p; rfl }
  let : Fintype C := Fintype.ofFinite _
  have hc : Nat.card P = Nat.card C * kappa z v v := by
    rw [← Nat.card_congr e, Nat.card_sigma]
    have hk (u : C) : Nat.card (Fiber z v u.val) = kappa z v v := by
      calc
        _ = kappa z v u.val := by simp only [kappa_def, Fiber, halfOrder_def]
        _ = _ := (kappa_eq_of_isConj z v u.property).symm
    simp only [hk, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card, Nat.cast_id]
  change Nat.card {p : G × G // IsConj z p.1 ∧ IsConj v p.2} = _ at hc
  rw [Nat.card_congr (Equiv.subtypeProdEquivProd
    (p := IsConj z) (q := IsConj v)), Nat.card_prod] at hc
  have : Nonempty C := ⟨⟨v, IsConj.refl v⟩⟩
  have he : Nat.card {a : G // IsConj z a} = kappa z v v := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := C))
    simpa only [mul_comm] using hc
  rw [← he]
  exact (ConjClasses.nat_card_carrier_mul_card_centralizer z).symm
end
end Theory.GroupTheory.TwoInvolutionClassOrder
