module

public import Theory.GroupTheory.PGroup.OrderThirtyTwoCharacteristicRecognition
public import Theory.GroupTheory.PGroup.MaximalCharacteristicAbelianCenter

/-!
# Characteristic subgroup bounds at order thirty-two

With no characteristic subgroup of order two and no characteristic elementary
subgroup of order at least eight, an abelian characteristic subgroup has order
one, four, or sixteen. The square kernel has order four; its characteristic
image excludes order eight and then order thirty-two. If the center has at
least four elements, it is therefore elementary abelian of order four.

If there is no characteristic abelian base of order sixteen, the center is
maximal characteristic abelian. The critical-subgroup argument then puts the
derived subgroup in the center and forces exponent at most four. This leaves
the class-two base construction and the inverter construction as structural
steps; neither is assumed by the bounds proved here.

Source context: Janko–Thompson, Math. Z. 113 (1970), results 1.3–1.4,
printed p.386; the maximal-center argument uses the critical-subgroup API.
-/

open Subgroup

namespace OrderThirtyTwoCharacteristicBounds

private theorem divisor_cases {n : ℕ} (hn : n ∣ 32) :
    n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16 ∨ n = 32 := by
  obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show n ∣ 2 ^ 5 from hn)
  interval_cases k <;> simp_all

private theorem characteristic_square_kernel_card
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8)
    (A : Subgroup G) [A.Characteristic] [IsMulCommutative A] (hA : 1 < Nat.card A) :
    let : CommGroup A := IsMulCommutative.instCommGroup
    Nat.card (powMonoidHom 2 : A →* A).ker = 4 := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  let f : A →* A := powMonoidHom 2
  let : f.ker.Characteristic := NormalSixteenC4Square.pow_ker_characteristic 2
  let K := f.ker.map A.subtype
  let : IsElementaryAbelian 2 f.ker :=
    ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => Subtype.ext x.property)⟩
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.map_subtype
  have hKcard : Nat.card K = Nat.card f.ker := card_map_of_injective A.subtype_injective
  have hupper : Nat.card f.ker < 8 := by
    rw [← hKcard]
    exact helem K inferInstance inferInstance
  have hne : Nat.card f.ker ≠ 2 := by
    rw [← hKcard]
    exact hchar K inferInstance
  have hdiv : Nat.card A ∣ 32 := hcard ▸ A.card_subgroup_dvd_card
  have htwo : 2 ∣ Nat.card A := by
    rcases divisor_cases hdiv with h | h | h | h | h | h <;> omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 htwo
  have hpow : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  let : Nontrivial f.ker := nontrivial_of_ne (⟨x, hpow⟩ : f.ker) 1 (by
    intro heq
    have heq' : x = 1 := congrArg Subtype.val heq
    simp [heq'] at hx)
  have hlower := Finite.one_lt_card (α := f.ker)
  have hdker : Nat.card f.ker ∣ 32 := f.ker.card_subgroup_dvd_card.trans hdiv
  rcases divisor_cases hdker with h | h | h | h | h | h <;> omega

private theorem characteristic_abelian_card_ne_eight
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8)
    (A : Subgroup G) [A.Characteristic] [IsMulCommutative A] : Nat.card A ≠ 8 := by
  intro hA
  let : CommGroup A := IsMulCommutative.instCommGroup
  let f : A →* A := powMonoidHom 2
  let : f.range.Characteristic := NormalSixteenC4Square.pow_range_characteristic 2
  have hk := characteristic_square_kernel_card hcard hchar helem A (by omega)
  have hp := f.ker.card_mul_index
  rw [index_ker, hA, show Nat.card f.ker = 4 from hk] at hp
  have hr : Nat.card f.range = 2 := by omega
  apply hchar (f.range.map A.subtype) inferInstance
  rw [card_map_of_injective A.subtype_injective, hr]

/-- Characteristic abelian subgroups have only three possible orders. -/
public theorem characteristic_abelian_card_cases
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8)
    (A : Subgroup G) [A.Characteristic] [IsMulCommutative A] :
    Nat.card A = 1 ∨ Nat.card A = 4 ∨ Nat.card A = 16 := by
  have htwo := hchar A inferInstance
  have height := characteristic_abelian_card_ne_eight hcard hchar helem A
  have hthirtytwo : Nat.card A ≠ 32 := by
    intro hA
    let : CommGroup A := IsMulCommutative.instCommGroup
    let f : A →* A := powMonoidHom 2
    let : f.range.Characteristic := NormalSixteenC4Square.pow_range_characteristic 2
    have hk := characteristic_square_kernel_card hcard hchar helem A (by omega)
    have hp := f.ker.card_mul_index
    rw [index_ker, hA, show Nat.card f.ker = 4 from hk] at hp
    have hr : Nat.card f.range = 8 := by omega
    apply characteristic_abelian_card_ne_eight hcard hchar helem (f.range.map A.subtype)
    rw [card_map_of_injective A.subtype_injective, hr]
  have hdiv : Nat.card A ∣ 32 := hcard ▸ A.card_subgroup_dvd_card
  rcases divisor_cases hdiv with h | h | h | h | h | h <;> omega

/-- The hypotheses exclude an abelian ambient group. -/
public theorem not_isMulCommutative
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8) :
    ¬ IsMulCommutative G := by
  intro h
  let : IsMulCommutative G := h
  have hc := characteristic_abelian_card_cases hcard hchar helem (⊤ : Subgroup G)
  rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv, hcard] at hc
  omega

/-- The center has order four. -/
public theorem center_card
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hcenter : 4 ≤ Nat.card (center G))
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8) :
    Nat.card (center G) = 4 := by
  have hc := characteristic_abelian_card_cases hcard hchar helem (center G)
  have hn := not_isMulCommutative hcard hchar helem
  rcases hc with hc | hc | hc
  · omega
  · exact hc
  · have hp := (center G).card_mul_index
    rw [hc, hcard] at hp
    have hi : (center G).index = 2 := by omega
    let : IsCyclic (G ⧸ center G) := isCyclic_of_prime_card hi
    exact (hn (isMulCommutative_of_isCyclic_quotient_center_self G)).elim

/-- Every element of the center has square one. -/
public theorem center_elementary
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hcenter : 4 ≤ Nat.card (center G))
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8) :
    IsElementaryAbelian 2 (center G) := by
  let : CommGroup (center G) := IsMulCommutative.instCommGroup
  have hc := center_card hcard hcenter hchar helem
  have hk := characteristic_square_kernel_card hcard hchar helem (center G) (by omega)
  have heq : (powMonoidHom 2 : center G →* center G).ker = ⊤ := by
    apply eq_top_of_card_eq
    omega
  refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
  intro x
  have hx : x ∈ (powMonoidHom 2 : center G →* center G).ker := by rw [heq]; trivial
  exact hx

/-- If the desired base has not yet been found, the group has class two
and exponent at most four. -/
public theorem base_or_class_two
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hcenter : 4 ≤ Nat.card (center G))
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8) :
    (∃ A : Subgroup G, A.Characteristic ∧ IsMulCommutative A ∧ Nat.card A = 16) ∨
      (_root_.commutator G ≤ center G ∧ ∀ x : G, x ^ 4 = 1) := by
  classical
  by_cases hbase : ∃ A : Subgroup G,
      A.Characteristic ∧ IsMulCommutative A ∧ Nat.card A = 16
  · exact Or.inl hbase
  right
  have hc := center_card hcard hcenter hchar helem
  have hmax : ∀ A : Subgroup G, A.Characteristic → IsMulCommutative A →
      center G ≤ A → A = center G := by
    intro A hAchar hAcomm hZA
    let : A.Characteristic := hAchar
    let : IsMulCommutative A := hAcomm
    have hle := card_le_of_le hZA
    rcases characteristic_abelian_card_cases hcard hchar helem A with hA | hA | hA
    · omega
    · exact (eq_of_le_of_card_ge hZA (by omega)).symm
    · exact (hbase ⟨A, hAchar, hAcomm, hA⟩).elim
  have hP : IsPGroup 2 G := IsPGroup.iff_card.mpr ⟨5, hcard⟩
  let : IsElementaryAbelian 2 (center G) := center_elementary hcard hcenter hchar helem
  exact ⟨hP.commutator_le_center_of_maximal_characteristic_abelian_center hmax,
    hP.exponent_four_of_maximal_characteristic_abelian_center hmax⟩

end OrderThirtyTwoCharacteristicBounds
