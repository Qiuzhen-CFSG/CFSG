module
public import Theory.GroupTheory.ElementaryTwoFactorInvolutions
public import Theory.ElementaryAbelian.Join
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.IntervalCases

/-!
# Two elementary four-planes in C₂ × D₈

Two normal elementary abelian subgroups of order four with a noncommutative
join intersect in order two. Their join consequently has order eight, and
its square-one elements lie in one of the two planes. When the whole group
is isomorphic to `Multiplicative (ZMod 2) × DihedralGroup 4`, there is also a
central involution outside this join which is not a square in the whole group.

Normality puts the inter-plane commutator in the intersection. An intersection
of order one would make the join elementary abelian; order four would identify
the planes. Relative-index multiplication therefore gives order eight, and
`involution_mem_union_of_elementary_factors_index_two` gives the covering.
For the final assertion, direct finite computation shows that every
noncommuting pair in the concrete model, together with the first-factor
involution, generates all sixteen elements: writing `z = [a,b]`, the eight
words `1,a,b,ab,z,az,bz,abz` and their translates cover the model. Thus the
first-factor involution lies outside the order-eight join. Its centrality,
order, and lack of square roots are checked in the same concrete model and
transported through the supplied isomorphism.

This intrinsic small-group geometry is used in the order-sixteen Sylow branch
of Kurzweil–Stellmacher, *The Theory of Finite Groups*, Chapter 12, Theorem 3,
pp. 365–366. It depends only on the stated finite-group hypotheses.
-/

namespace CyclicTwoDihedralFour

private abbrev Model := Multiplicative (ZMod 2) × DihedralGroup 4
private def centralPoint : Model := (Multiplicative.ofAdd 1, 1)

set_option maxRecDepth 20000 in
private theorem centralPoint_properties :
    centralPoint ∈ Subgroup.center Model ∧ orderOf centralPoint = 2 ∧
    ∀ x : Model, x ^ 2 ≠ centralPoint := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · apply orderOf_eq_prime
    · decide
    · decide
  · decide

private def words (a b : Model) : Finset Model :=
  let z := a * b * a⁻¹ * b⁻¹
  {1, a, b, a * b, z, a * z, b * z, a * b * z}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem model_generation : ∀ a b : Model, a * b ≠ b * a →
    ∀ x : Model, x ∈ words a b ∨ x * centralPoint ∈ words a b := by
  decide


private theorem relative_indices
    {S : Type*} [Group S] [Finite S]
    (Q₁ Q₂ : Subgroup S) [Q₁.Normal] [Q₂.Normal]
    (hQ₁ : IsElementaryAbelian 2 Q₁) (hQ₂ : IsElementaryAbelian 2 Q₂)
    (hc₁ : Nat.card Q₁ = 4) (hc₂ : Nat.card Q₂ = 4)
    (hnc : ¬ IsMulCommutative ↥(Q₁ ⊔ Q₂)) :
    (Q₁ ⊓ Q₂).relIndex Q₁ = 2 ∧ (Q₁ ⊓ Q₂).relIndex Q₂ = 2 ∧
      Nat.card ↥(Q₁ ⊔ Q₂) = 8 := by
  let := hQ₁
  let := hQ₂
  have hIbot : Q₁ ⊓ Q₂ ≠ ⊥ := by
    intro hbot
    have hcom : ⁅Q₁, Q₂⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_le_inf Q₁ Q₂).trans hbot.le)
    let : IsElementaryAbelian 2 ↥(Q₁ ⊔ Q₂) :=
      IsElementaryAbelian.sup_of_le_centralizer
      (Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcom))
    exact hnc inferInstance
  have hIlt : Nat.card ↥(Q₁ ⊓ Q₂) < 4 := by
    have hle := Subgroup.card_le_of_le (show Q₁ ⊓ Q₂ ≤ Q₁ from inf_le_left)
    rw [hc₁] at hle
    apply lt_of_le_of_ne hle
    intro heq
    have h₁ : Q₁ ⊓ Q₂ = Q₁ := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    have h₂ : Q₁ ⊓ Q₂ = Q₂ := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
    have hEq : Q₁ = Q₂ := h₁.symm.trans h₂
    apply hnc
    rw [hEq, sup_idem]
    infer_instance
  have hIcard : Nat.card ↥(Q₁ ⊓ Q₂) = 2 := by
    have hlo : 1 < Nat.card ↥(Q₁ ⊓ Q₂) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hIbot
    have hdvd := Subgroup.card_dvd_of_le (show Q₁ ⊓ Q₂ ≤ Q₁ from inf_le_left)
    rw [hc₁] at hdvd
    interval_cases h : Nat.card ↥(Q₁ ⊓ Q₂) <;> norm_num at *
  have hi₁ : (Q₁ ⊓ Q₂).relIndex Q₁ = 2 := by
    have h := ((Q₁ ⊓ Q₂).subgroupOf Q₁).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
      hIcard, hc₁] at h
    change 2 * (Q₁ ⊓ Q₂).relIndex Q₁ = 4 at h
    omega
  have hi₂ : (Q₁ ⊓ Q₂).relIndex Q₂ = 2 := by
    have h := ((Q₁ ⊓ Q₂).subgroupOf Q₂).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
      hIcard, hc₂] at h
    change 2 * (Q₁ ⊓ Q₂).relIndex Q₂ = 4 at h
    omega
  refine ⟨hi₁, hi₂, ?_⟩
  have hi : Q₁.relIndex (Q₁ ⊔ Q₂) = 2 := by
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right]
    exact hi₂
  have h := (Q₁.subgroupOf (Q₁ ⊔ Q₂)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, hc₁] at h
  change 4 * Q₁.relIndex (Q₁ ⊔ Q₂) = Nat.card ↥(Q₁ ⊔ Q₂) at h
  omega

/-- A noncommutative join of two normal elementary four-planes in `C₂ × D₈`
has index two and all its involutions lie in the planes; it misses a central
involution which has no square root in the whole group. -/
public theorem c2d8_two_plane_geometry
    {S : Type*} [Group S] [Finite S]
    (e : S ≃* Multiplicative (ZMod 2) × DihedralGroup 4)
    (Q₁ Q₂ : Subgroup S) [Q₁.Normal] [Q₂.Normal]
    (hQ₁ : IsElementaryAbelian 2 Q₁) (hQ₂ : IsElementaryAbelian 2 Q₂)
    (hc₁ : Nat.card Q₁ = 4) (hc₂ : Nat.card Q₂ = 4)
    (hnc : ¬ IsMulCommutative ↥(Q₁ ⊔ Q₂)) :
    (Q₁ ⊔ Q₂).index = 2 ∧
      (∀ u ∈ Q₁ ⊔ Q₂, u ^ 2 = 1 → u ∈ Q₁ ∨ u ∈ Q₂) ∧
      ∃ t : S, t ∈ Subgroup.center S ∧ orderOf t = 2 ∧
        t ∉ Q₁ ⊔ Q₂ ∧ ∀ x : S, x ^ 2 ≠ t := by
  classical
  obtain ⟨hi₁, hi₂, hUcard⟩ := relative_indices Q₁ Q₂ hQ₁ hQ₂ hc₁ hc₂ hnc
  have hScard : Nat.card S = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, DihedralGroup.card]
  have hUindex : (Q₁ ⊔ Q₂).index = 2 := by
    have h := (Q₁ ⊔ Q₂).card_mul_index
    rw [hUcard, hScard] at h
    omega
  refine ⟨hUindex, ?_, ?_⟩
  · intro u hu hu2
    apply Subgroup.involution_mem_union_of_elementary_factors_index_two
      Q₁ Q₂ hQ₁ hQ₂ _ _ hi₁ hi₂ hnc hu hu2
    all_goals simp only [Subgroup.normalizer_eq_top, le_top]
  let t := e.symm centralPoint
  have het : e t = centralPoint := e.apply_symm_apply _
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro x
    apply e.injective
    simpa only [map_mul, het] using
      (Subgroup.mem_center_iff.mp centralPoint_properties.1 (e x))
  · rw [← e.orderOf_eq t, het]
    exact centralPoint_properties.2.1
  · intro ht
    obtain ⟨a, b, hab⟩ : ∃ a b : ↥(Q₁ ⊔ Q₂), a * b ≠ b * a := by
      simpa only [isMulCommutative_iff, not_forall] using hnc
    have hab' : e (a : S) * e (b : S) ≠ e (b : S) * e (a : S) := by
      intro heq
      apply hab
      apply Subtype.ext
      exact e.injective (by simpa only [Subgroup.coe_mul, map_mul] using heq)
    have hwords {x : Model} (hx : x ∈ words (e a) (e b)) : e.symm x ∈ Q₁ ⊔ Q₂ := by
      simp only [words, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [map_one, map_mul, map_inv, e.symm_apply_apply]
      all_goals solve_by_elim (maxDepth := 16) only [Subgroup.one_mem,
        Subgroup.mul_mem, Subgroup.inv_mem, a.property, b.property]
    have htop : Q₁ ⊔ Q₂ = ⊤ := by
      apply top_unique
      intro x _
      obtain hx | hx := model_generation (e a) (e b) hab' (e x)
      · simpa only [e.symm_apply_apply] using hwords hx
      · have hxt : x * t ∈ Q₁ ⊔ Q₂ := by
          simpa only [map_mul, e.symm_apply_apply] using hwords hx
        exact (Q₁ ⊔ Q₂).mul_mem_cancel_right ht |>.mp hxt
    rw [htop, Subgroup.index_top] at hUindex
    contradiction
  · intro x hx
    apply centralPoint_properties.2.2 (e x)
    simpa only [map_pow, het] using congrArg e hx

end CyclicTwoDihedralFour
