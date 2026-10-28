module

public import Theory.GroupAction.FourPointSylowFixed
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.SpecificGroups.KleinFour


/-!
# Two point stabilizers on the outside four points of an elementary eight-group

A Sylow-fixed point in a four-point action is fixed by the whole group when
its stabilizer acts transitively on the other three points. Two distinct
points with this stabilizer property are therefore impossible. The ambient
version uses the literal conjugation action on an invariant four-element set.

For an elementary eight-group containing an exterior central involution t
inside K⟨t⟩, its intersection with K is a four-group. A transitive action of
its normalizer on the three nonidentity elements becomes the point-stabilizer
action on the other three elements of its outside coset.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 2.5.21 on printed p.565, the two three-point stabilizers on F \ E.
-/

public section

namespace MulAction
variable {N X : Type*} [Group N] [Finite N] [MulAction N X] [Finite X]

private theorem exists_third_of_card_four (hX : Nat.card X = 4) (x y : X) :
    ∃ z : X, z ≠ x ∧ z ≠ y := by
  classical
  by_contra! h
  have hsub : (Set.univ : Set X) ⊆ {x, y} := by
    intro z _
    by_cases hz : z = x
    · exact Or.inl hz
    · exact Or.inr (h z hz)
  have hbound := (Set.ncard_le_ncard hsub).trans (Set.ncard_insert_le x {y})
  rw [Set.ncard_singleton] at hbound
  rw [Set.ncard_univ, hX] at hbound
  omega

/-- A Sylow-fixed point whose stabilizer is transitive elsewhere is globally fixed. -/
theorem fixed_of_card_four_of_stabilizer_transitive_of_sylow_fixed
    (hX : Nat.card X = 4) (S : Sylow 2 N) (t : X)
    (hfix : ∀ s ∈ (S : Subgroup N), s • t = t)
    (htrans : ∀ y z : X, y ≠ t → z ≠ t →
      ∃ a : N, a • t = t ∧ a • y = z) :
    ∀ g : N, g • t = t := by
  obtain ⟨x, hx⟩ := exists_fixed_of_card_four_of_sylow_fixed hX S t hfix
  suffices hxt : x = t by simpa only [← hxt] using hx
  by_contra hxt
  obtain ⟨y, hyt, hyx⟩ := exists_third_of_card_four hX t x
  obtain ⟨a, _, hay⟩ := htrans x y hxt hyt
  exact hyx (hay.symm.trans (hx a))

/-- Two distinct transitive point stabilizers contradict a Sylow-fixed point. -/
theorem false_of_card_four_of_two_transitive_stabilizers
    (hX : Nat.card X = 4) (S : Sylow 2 N) (t t' : X) (hne : t ≠ t')
    (hfix : ∀ s ∈ (S : Subgroup N), s • t = t)
    (htrans : ∀ y z : X, y ≠ t → z ≠ t →
      ∃ a : N, a • t = t ∧ a • y = z)
    (htrans' : ∀ y z : X, y ≠ t' → z ≠ t' →
      ∃ a : N, a • t' = t' ∧ a • y = z) : False := by
  have hall := fixed_of_card_four_of_stabilizer_transitive_of_sylow_fixed hX S t hfix htrans
  obtain ⟨y, hyt, hyt'⟩ := exists_third_of_card_four hX t t'
  obtain ⟨a, _, hay⟩ := htrans' t y hne hyt'
  exact hyt (hay.symm.trans (hall a))
end MulAction

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Apply the four-point obstruction to the actual ambient conjugation action. -/
theorem false_of_four_set_two_transitive_stabilizers
    (N : Subgroup G) (Ω : Set G) (hΩ : Ω.ncard = 4)
    (hstable : ∀ n ∈ N, ∀ y ∈ Ω, MulAut.conj n y ∈ Ω)
    (S : Sylow 2 N) (t t' : G) (ht : t ∈ Ω) (ht' : t' ∈ Ω) (hne : t ≠ t')
    (hfix : ∀ s ∈ (S : Subgroup N), MulAut.conj (s : G) t = t)
    (htrans : ∀ y ∈ Ω, ∀ z ∈ Ω, y ≠ t → z ≠ t →
      ∃ a ∈ N, MulAut.conj a t = t ∧ MulAut.conj a y = z)
    (htrans' : ∀ y ∈ Ω, ∀ z ∈ Ω, y ≠ t' → z ≠ t' →
      ∃ a ∈ N, MulAut.conj a t' = t' ∧ MulAut.conj a y = z) : False := by
  let : MulAction N G := MulAction.compHom G (MulAut.conj.comp N.subtype)
  let X : SubMulAction N G := {
    carrier := Ω
    smul_mem' := fun n y hy => hstable n n.property y hy }
  let x : X := ⟨t, ht⟩
  let x' : X := ⟨t', ht'⟩
  apply MulAction.false_of_card_four_of_two_transitive_stabilizers
    (N := N) (X := X) hΩ S x x' (fun he => hne (congrArg Subtype.val he))
  · intro s hs
    exact Subtype.ext (hfix s hs)
  · intro y z hy hz
    obtain ⟨a, ha, hat, hay⟩ := htrans y y.property z z.property
      (fun he => hy (Subtype.ext he)) (fun he => hz (Subtype.ext he))
    exact ⟨⟨a, ha⟩, Subtype.ext hat, Subtype.ext hay⟩
  · intro y z hy hz
    obtain ⟨a, ha, hat, hay⟩ := htrans' y y.property z z.property
      (fun he => hy (Subtype.ext he)) (fun he => hz (Subtype.ext he))
    exact ⟨⟨a, ha⟩, Subtype.ext hat, Subtype.ext hay⟩
end Subgroup

namespace Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

private theorem normalizes_of_centralizing_point (K : Subgroup G) (t : G)
    (hK : K ≤ centralizer ({t} : Set G)) : t ∈ normalizer (K : Set G) := by
  apply mem_normalizer_fintype
  intro k hk
  have hc : Commute k t := mem_centralizer_singleton_iff.mp (hK hk)
  simpa only [hc.symm.eq, mul_inv_cancel_right] using hk

/-- In a split involution centralizer, four-group fusion gives transitivity on
the three outside points distinct from the central involution. -/
theorem elementaryEight_centralizer_point_stabilizer_transitive
    (K F : Subgroup G) [IsElementaryAbelian 2 F] (hF : Nat.card F = 8)
    (t : G) (htF : t ∈ F) (htK : t ∉ K)
    (hFC : F ≤ centralizer ({t} : Set G))
    (hC : centralizer ({t} : Set G) = K ⊔ zpowers t)
    (hfour : ∀ A : Subgroup G, A ≤ K → IsKleinFour A →
      ∀ a ∈ A, ∀ b ∈ A, a ≠ 1 → b ≠ 1 →
        ∃ n ∈ K ⊓ normalizer (A : Set G), MulAut.conj n a = b) :
    ((F : Set G) \ (K : Set G)).ncard = 4 ∧
      ∀ y ∈ F, ∀ z ∈ F, y ∉ K → z ∉ K → y ≠ t → z ≠ t →
        ∃ n ∈ normalizer (F : Set G),
          MulAut.conj n t = t ∧ MulAut.conj n y = z := by
  classical
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t htF
  have ht1 : t ≠ 1 := fun he => htK (he ▸ K.one_mem)
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht2)
  have hKC : K ≤ centralizer ({t} : Set G) := by
    rw [hC]
    exact le_sup_left
  have htN : t ∈ normalizer (K : Set G) := normalizes_of_centralizing_point K t hKC
  have hcases (x : G) (hx : x ∈ F) : x ∈ K ∨ x * t ∈ K := by
    have hxC : x ∈ K ⊔ zpowers t := hC ▸ hFC hx
    have hs := coe_mul_of_right_le_normalizer_left K (zpowers t) (zpowers_le.mpr htN)
    rw [← SetLike.mem_coe, hs] at hxC
    obtain ⟨k, hk, a, ha, rfl⟩ := hxC
    change k ∈ K at hk
    change a ∈ zpowers t at ha
    rw [mem_zpowers_iff_mem_range_orderOf, hto] at ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have hi2 : i < 2 := Finset.mem_range.mp hi
    interval_cases i
    · exact Or.inl (by simpa only [pow_zero, mul_one] using hk)
    · exact Or.inr (by simpa only [pow_one, mul_assoc, ← pow_two, ht2, mul_one] using hk)
  let A : Subgroup G := F ⊓ K
  have hsplit : F = A ⊔ zpowers t := by
    apply le_antisymm
    · intro x hx
      rcases hcases x hx with hxK | hxtK
      · exact mem_sup_left ⟨hx, hxK⟩
      · have hh := mul_mem_sup (show x * t ∈ A from ⟨F.mul_mem hx htF, hxtK⟩)
          (mem_zpowers t)
        simpa only [mul_assoc, ← pow_two, ht2, mul_one] using hh
    · exact sup_le inf_le_left (zpowers_le.mpr htF)
  have htnA : t ∈ normalizer (A : Set G) :=
    normalizes_of_centralizing_point A t (inf_le_left.trans hFC)
  have hAcard : Nat.card A = 4 := by
    have hc := card_sup_zpowers_of_normalizing_involution A t ht2 (fun h => htK h.2) htnA
    rw [← hsplit, hF] at hc
    omega
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
    (inclusion (show A ≤ F from inf_le_left)) (inclusion_injective _)
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by rw [hAcard]; decide)
  have hA : IsKleinFour A := ⟨hAcard, IsElementaryAbelian.exponent_eq_prime⟩
  constructor
  · have hc := Set.ncard_inter_add_ncard_sdiff_eq_ncard (F : Set G) (K : Set G)
    change Nat.card A + ((F : Set G) \ (K : Set G)).ncard = Nat.card F at hc
    omega
  · intro y hy z hz hyK hzK hyt hzt
    have hyA : y * t ∈ A := ⟨F.mul_mem hy htF, (hcases y hy).resolve_left hyK⟩
    have hzA : z * t ∈ A := ⟨F.mul_mem hz htF, (hcases z hz).resolve_left hzK⟩
    have hyt1 : y * t ≠ 1 := fun he => hyt ((eq_inv_iff_mul_eq_one.mpr he).trans hti)
    have hzt1 : z * t ≠ 1 := fun he => hzt ((eq_inv_iff_mul_eq_one.mpr he).trans hti)
    obtain ⟨n, hn, hconj⟩ := hfour A inf_le_right hA (y * t) hyA (z * t) hzA hyt1 hzt1
    have hnt : MulAut.conj n t = t := by
      have hc : Commute n t := mem_centralizer_singleton_iff.mp (hKC hn.1)
      exact mul_inv_eq_iff_eq_mul.mpr hc.eq
    have hnline : n ∈ normalizer (zpowers t : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [MonoidHom.map_zpowers]
      exact congrArg zpowers hnt
    have hnF : n ∈ normalizer (F : Set G) := by
      rw [hsplit]
      exact normalizer_inf_normalizer_le_normalizer_sup A (zpowers t) ⟨hn.2, hnline⟩
    refine ⟨n, hnF, hnt, ?_⟩
    rw [map_mul, hnt] at hconj
    exact mul_right_cancel hconj
end Subgroup
