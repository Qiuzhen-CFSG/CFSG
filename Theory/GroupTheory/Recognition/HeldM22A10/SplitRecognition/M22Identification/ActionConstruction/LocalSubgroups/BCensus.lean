module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.Definitions
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalConfiguration

/-!
# The order census and characteristic kernel of EQ*

The actual common actor has order three and acts without nonidentity fixed
points on E. Its commutator map shows that each element outside E in EQ*
is conjugate to a nonidentity element of the complement. Thus EQ* has order
48 and its complete order census is one identity, fifteen involutions and
thirty-two elements of order three. In particular E is the square-one locus
inside EQ*, so every ambient normalizer of EQ* preserves E.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 8, Lemma 17, pp.16--17;
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer) (w : FusedNineIntersectionActor D k)

omit [Finite G] in
/-- The Frobenius subgroup EQ* has order 48. -/
public theorem B_card : Nat.card (B D k w) = 48 := by
  have hdis : Disjoint (CaseII.E D k) (zpowers w.actor) :=
    disjoint_of_coprime_natCard (by rw [CaseII.E_card, Nat.card_zpowers, w.actor_order]; decide)
  rw [B, card_sup_of_disjoint_of_normalizes _ _ hdis
    (zpowers_le.mpr w.normalizes_E), CaseII.E_card, Nat.card_zpowers, w.actor_order]

/-- Every element outside E in EQ* has order three. -/
public theorem B_order_outside (x : B D k w) (hx : (x : G) ∉ CaseII.E D k) :
    orderOf x = 3 := by
  rw [← orderOf_coe]
  exact orderOf_outside_cyclic_three_join (CaseII.E D k) w.actor w.normalizes_E
    w.actor_order w.fixed_point_free x x.property hx

/-- The elements of order three are precisely the elements outside E. -/
public theorem B_order_three_iff (x : B D k w) :
    orderOf x = 3 ↔ (x : G) ∉ CaseII.E D k := by
  constructor
  · intro hx he
    have h := (CaseII.E D k).orderOf_dvd_natCard he
    rw [orderOf_coe x, hx, CaseII.E_card] at h
    norm_num at h
  · exact B_order_outside D k w x

/-- The involutions of EQ* are precisely the nonidentity elements of E. -/
public theorem B_order_two_iff (x : B D k w) :
    orderOf x = 2 ↔ (x : G) ∈ CaseII.E D k ∧ x ≠ 1 := by
  constructor
  · intro hx
    refine ⟨?_, fun he => by simp [he] at hx⟩
    by_contra hn
    have := B_order_outside D k w x hn
    omega
  · rintro ⟨he, hx⟩
    let := CaseII.E_elementary D k
    apply orderOf_eq_prime
    · apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (x : G) he
    · exact hx

/-- There are fifteen involutions in EQ*. -/
public theorem B_count_two : Nat.card {x : B D k w // orderOf x = 2} = 15 := by
  classical
  let e : {x : B D k w // orderOf x = 2} ≃ {x : CaseII.E D k // x ≠ 1} :=
    { toFun := fun x => ⟨⟨x.val.val, ((B_order_two_iff D k w x.val).mp x.property).1⟩,
        fun h => ((B_order_two_iff D k w x.val).mp x.property).2
          (Subtype.ext (congrArg (fun a : CaseII.E D k => (a : G)) h))⟩
      invFun := fun x => ⟨⟨x.val.val, (show CaseII.E D k ≤ B D k w from le_sup_left) x.val.property⟩,
        (B_order_two_iff D k w _).mpr ⟨x.val.property,
          fun h => x.property (Subtype.ext (congrArg (fun a : B D k w => (a : G)) h))⟩⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [Nat.card_congr e]
  let := Fintype.ofFinite (CaseII.E D k)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_unique (α := {x : CaseII.E D k // x = 1}), ← Nat.card_eq_fintype_card, CaseII.E_card]

/-- There are thirty-two elements of order three in EQ*. -/
public theorem B_count_three : Nat.card {x : B D k w // orderOf x = 3} = 32 := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight (B_order_three_iff D k w))]
  let := Fintype.ofFinite (B D k w)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, B_card]
  change 48 - Nat.card ((CaseII.E D k).subgroupOf (B D k w)) = 32
  rw [Nat.card_congr (subgroupOfEquivOfLe (show CaseII.E D k ≤ B D k w from
    le_sup_left)).toEquiv, CaseII.E_card]

/-- The only element orders in EQ* are one, two and three. -/
public theorem B_orders (x : B D k w) : orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 3 := by
  by_cases hx : x = 1
  · exact Or.inl (hx ▸ orderOf_one)
  by_cases he : (x : G) ∈ CaseII.E D k
  · exact Or.inr (Or.inl ((B_order_two_iff D k w x).mpr ⟨he, hx⟩))
  · exact Or.inr (Or.inr (B_order_outside D k w x he))

/-- The complete element-order census of the actual subgroup EQ*. -/
public theorem B_count (n : ℕ) :
    Nat.card {x : B D k w // orderOf x = n} = localOrderCount 15 32 0 0 n := by
  classical
  by_cases hn1 : n = 1
  · subst n
    simp only [orderOf_eq_one_iff, localOrderCount, ↓reduceIte]
    exact Nat.card_unique
  by_cases hn2 : n = 2
  · subst n
    exact B_count_two D k w
  by_cases hn3 : n = 3
  · subst n
    exact B_count_three D k w
  have hnone : IsEmpty {x : B D k w // orderOf x = n} := ⟨by
    rintro ⟨x, hx⟩
    rcases B_orders D k w x with h | h | h
    · exact hn1 (hx.symm.trans h)
    · exact hn2 (hx.symm.trans h)
    · exact hn3 (hx.symm.trans h)⟩
  simp only [Nat.card_of_isEmpty, localOrderCount, hn1, hn2, hn3,
    ↓reduceIte, ite_self]
/-- E is characterized inside EQ* by the equation x² = 1. -/
public theorem mem_E_iff_mem_B_and_square (x : G) :
    x ∈ CaseII.E D k ↔ x ∈ B D k w ∧ x ^ 2 = 1 := by
  constructor
  · intro hx
    let := CaseII.E_elementary D k
    exact ⟨(show CaseII.E D k ≤ B D k w from le_sup_left) hx,
      elemPow_eq_one_of_isElementaryAbelian x hx⟩
  · rintro ⟨hxB, hx2⟩
    by_contra hxE
    have hx3 : orderOf x = 3 := by
      exact (orderOf_coe (⟨x, hxB⟩ : B D k w)).trans (B_order_outside D k w ⟨x, hxB⟩ hxE)
    have hd := orderOf_dvd_of_pow_eq_one hx2
    rw [hx3] at hd
    norm_num at hd

/-- The normalizer of EQ* preserves E, as required in the choice of Z*. -/
public theorem normalizer_B_le_normalizer_E :
    normalizer (B D k w : Set G) ≤ normalizer (CaseII.E D k : Set G) := by
  intro g hg
  apply mem_normalizer_iff.mpr
  intro x
  rw [mem_E_iff_mem_B_and_square D k w x,
    mem_E_iff_mem_B_and_square D k w (g * x * g⁻¹)]
  refine and_congr ((mem_normalizer_iff.mp hg) x) ?_
  change x ^ 2 = 1 ↔ ((MulAut.conj g) x) ^ 2 = 1
  rw [← map_pow, (MulAut.conj g).map_eq_one_iff]

/-- The intersection of EQ* with F is exactly E ∩ F. -/
public theorem B_inf_F : B D k w ⊓ CaseII.F D k = CaseII.E D k ⊓ CaseII.F D k := by
  apply le_antisymm
  · intro x hx
    refine ⟨(mem_E_iff_mem_B_and_square D k w x).mpr ⟨hx.1, ?_⟩, hx.2⟩
    let := CaseII.F_elementary D k
    exact elemPow_eq_one_of_isElementaryAbelian x hx.2
  · exact inf_le_inf (show CaseII.E D k ≤ B D k w from le_sup_left) le_rfl

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
