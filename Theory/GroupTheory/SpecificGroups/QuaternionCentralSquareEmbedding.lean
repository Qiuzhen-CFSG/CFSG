module
public import Theory.GroupTheory.QuaternionGenerated
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.IntervalCases

/-!
# Embedding quaternion subgroups whose squares are central

A subgroup of a generalized quaternion group whose elements have central
squares embeds into any quaternion subgroup of order eight. The embedding
preserves equality with each element of the ambient center.

The normal forms first show that central elements square to one and that the
ambient group has a unique involution. For a subgroup of exponent dividing
four, its intersection with the rotations is cyclic. If there is an outside
element, this cyclic intersection and that element generate the subgroup.
The rotation generator has order two or four, giving respectively the cyclic
quaternion model of order four or the quaternion model of order eight by the
quaternion presentation. A cyclic group of exponent dividing four also embeds
into the quaternion group of order eight. Finally, injectivity and uniqueness
of the ambient involution give compatibility with the center.

This intrinsic quaternion geometry supplies the quaternion-core embedding
used in the binary-centralizer argument of GLS, *The Classification of the
Finite Simple Groups*, volume 2, Proposition 22.4. It requires neither
normality of the designated quaternion eight nor an order bound on the ambient
group. The normal forms use Mathlib's generalized quaternion presentation.
-/

namespace QuaternionGroup
variable {m : ℕ}

private theorem half_ne_zero (hm : 0 < m) : (m : ZMod (2 * m)) ≠ 0 := by
  intro h
  have := congrArg ZMod.val h
  simp only [ZMod.val_natCast, ZMod.val_zero,
    Nat.mod_eq_of_lt (by omega : m < 2 * m)] at this
  omega

private theorem index_of_self_neg (hm : 0 < m) (i : ZMod (2 * m)) (hi : i = -i) :
    i = 0 ∨ i = m := by
  let : NeZero m := ⟨by omega⟩
  by_cases h : i = 0
  · exact Or.inl h
  right
  let : NeZero i := ⟨h⟩
  have hv := congrArg ZMod.val hi
  rw [ZMod.val_neg_of_ne_zero] at hv
  have hil := ZMod.val_lt i
  apply ZMod.val_injective
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : m < 2 * m)]
  omega

/-- An element squaring to one is the identity or the halfway rotation. -/
public theorem eq_one_or_eq_a_of_sq_eq_one (hm : 0 < m) (x : QuaternionGroup m) (hx : x ^ 2 = 1) :
    x = 1 ∨ x = a m := by
  cases x with
  | a i =>
    have hi : i + i = 0 := a.inj (by simpa only [pow_two, a_mul_a, one_def] using hx)
    have hn : i = -i := by linear_combination hi
    rcases index_of_self_neg hm i hn with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  | xa i =>
    rw [xa_sq, one_def] at hx
    exact (half_ne_zero hm (a.inj hx)).elim

/-- Central elements of a nonabelian generalized quaternion model square to one. -/
public theorem sq_eq_one_of_mem_center (hm : 2 ≤ m) (x : QuaternionGroup m)
    (hx : x ∈ Subgroup.center (QuaternionGroup m)) : x ^ 2 = 1 := by
  cases x with
  | a i =>
    have hi : i = -i := by
      simpa using Subgroup.mem_center_iff.mp hx (xa 0)
    simp only [pow_two, a_mul_a, one_def]
    congr 1
    linear_combination hi
  | xa i =>
    have hi : i - 1 = i + 1 := xa.inj (Subgroup.mem_center_iff.mp hx (a 1))
    have htwo : (2 : ZMod (2 * m)) = 0 := by linear_combination -hi
    have hv := congrArg ZMod.val htwo
    have hval : ZMod.val (2 : ZMod (2 * m)) = 2 :=
      ZMod.val_natCast_of_lt (by omega : 2 < 2 * m)
    rw [hval, ZMod.val_zero] at hv
    omega

private theorem mem_rotation_iff [NeZero m] (x : QuaternionGroup m) :
    x ∈ Subgroup.zpowers (a 1 : QuaternionGroup m) ↔ ∃ i, x = a i := by
  constructor
  · rintro ⟨k, rfl⟩
    have h : ∀ k : ℤ, (a 1 : QuaternionGroup m) ^ k = a (k : ZMod (2 * m)) := by
      intro k
      cases k with
      | ofNat n => simp
      | negSucc n =>
        rw [zpow_negSucc, a_one_pow]
        have hinv (j : ZMod (2 * m)) : (a j : QuaternionGroup m)⁻¹ = a (-j) := by
          apply inv_eq_of_mul_eq_one_right
          simp
        rw [hinv]
        congr 1
        simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
    exact ⟨k, h k⟩
  · rintro ⟨i, rfl⟩
    refine ⟨(i.val : ℤ), ?_⟩
    change (a 1 : QuaternionGroup m) ^ (i.val : ℤ) = a i
    rw [zpow_natCast, a_one_pow, ZMod.natCast_zmod_val]

private theorem involution_unique (hm : 0 < m) (x y : QuaternionGroup m)
    (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  have hne {z : QuaternionGroup m} (hz : orderOf z = 2) : z ≠ 1 := by
    intro h
    simp [h] at hz
  have hs {z : QuaternionGroup m} (hz : orderOf z = 2) : z ^ 2 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  exact ((eq_one_or_eq_a_of_sq_eq_one hm x (hs hx)).resolve_left (hne hx)).trans
    ((eq_one_or_eq_a_of_sq_eq_one hm y (hs hy)).resolve_left (hne hy)).symm

/-- A quaternion subgroup of exponent dividing four is cyclic or quaternion-eight. -/
public theorem isCyclic_or_nonempty_equiv_two_of_pow_four (hm : 2 ≤ m)
    (T : Subgroup (QuaternionGroup m))
    (hfour : ∀ t ∈ T, t ^ 4 = 1) :
    IsCyclic T ∨ Nonempty (T ≃* QuaternionGroup 2) := by
  classical
  let : NeZero m := ⟨by omega⟩
  let C := Subgroup.zpowers (a 1 : QuaternionGroup m)
  by_cases hTC : T ≤ C
  · exact Or.inl (Subgroup.isCyclic_of_le hTC)
  obtain ⟨d, hdT, hdC⟩ := SetLike.not_le_iff_exists.mp hTC
  obtain ⟨j, rfl⟩ : ∃ j, d = xa j := by
    cases d with
    | a i => exact (hdC ((mem_rotation_iff _).mpr ⟨i, rfl⟩)).elim
    | xa j => exact ⟨j, rfl⟩
  let A := T ⊓ C
  have hA : IsCyclic A := Subgroup.isCyclic_of_le (show A ≤ C from inf_le_right)
  obtain ⟨c, hcA⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp hA
  have hcMem : c ∈ A := hcA ▸ Subgroup.mem_zpowers c
  obtain ⟨i, rfl⟩ := (mem_rotation_iff c).mp hcMem.2
  have hc4 : orderOf (a i : QuaternionGroup m) ∣ 4 :=
    orderOf_dvd_of_pow_eq_one (hfour _ hcMem.1)
  have hsA : (xa j : QuaternionGroup m) ^ 2 ∈ A := by
    refine ⟨T.pow_mem hdT 2, ?_⟩
    rw [xa_sq]
    exact (mem_rotation_iff _).mpr ⟨m, rfl⟩
  have htwo : 2 ∣ orderOf (a i : QuaternionGroup m) := by
    have h := orderOf_dvd_of_mem_zpowers (hcA ▸ hsA)
    simpa only [orderOf_pow, orderOf_xa, show Nat.gcd 4 2 = 2 from rfl, Nat.reduceDiv] using h
  have hgen : Subgroup.closure ({a i, xa j} : Set (QuaternionGroup m)) = T := by
    apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact hcMem.1
      · exact Set.mem_singleton_iff.mp hx ▸ hdT
    · let U := Subgroup.closure ({a i, xa j} : Set (QuaternionGroup m))
      have haU : a i ∈ U := Subgroup.subset_closure (by simp)
      have hdU : xa j ∈ U := Subgroup.subset_closure (by simp)
      have hAU : A ≤ U := by rw [← hcA]; exact Subgroup.zpowers_le.mpr haU
      intro x hx
      cases x with
      | a k => exact hAU ⟨hx, (mem_rotation_iff _).mpr ⟨k, rfl⟩⟩
      | xa k =>
        have hxA : xa j * xa k ∈ A :=
          ⟨T.mul_mem hdT hx, (mem_rotation_iff _).mpr ⟨_, rfl⟩⟩
        simpa only [inv_mul_cancel_left] using U.mul_mem (U.inv_mem hdU) (hAU hxA)
  have hinv : xa j * a i * (xa j)⁻¹ = (a i)⁻¹ := by
    have ha : (a i : QuaternionGroup m)⁻¹ = a (-i) := by
      apply inv_eq_of_mul_eq_one_right
      simp
    apply mul_right_cancel (b := xa j)
    simp only [mul_assoc, inv_mul_cancel, mul_one, ha, xa_mul_a, a_mul_xa, sub_neg_eq_add]
  have hout : xa j ∉ Subgroup.zpowers (a i : QuaternionGroup m) := by
    intro h
    exact hdC ((show A ≤ C from inf_le_right) (hcA ▸ h))
  have horders : orderOf (a i : QuaternionGroup m) = 2 ∨ orderOf (a i : QuaternionGroup m) = 4 := by
    have h := (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf (a i) ∣ 2 ^ 2 from hc4)
    obtain ⟨k, hk, he⟩ := h
    interval_cases k
    · norm_num [he] at htwo
    · exact Or.inl he
    · exact Or.inr he
  rcases horders with hc | hc
  · have hsq : (xa j : QuaternionGroup m) ^ 2 = (a i) ^ 1 := by
      apply involution_unique (by omega)
      · rw [orderOf_pow, orderOf_xa]; rfl
      · simpa using hc
    obtain ⟨_, ⟨e⟩⟩ := closure_equiv_of_relations (m := 1) (by decide)
      (a i) (xa j) hc hsq hinv hout
    rw [hgen] at e
    let := quaternionGroup_one_isCyclic
    exact Or.inl (isCyclic_of_injective e.toMonoidHom e.injective)
  · have hsq : (xa j : QuaternionGroup m) ^ 2 = (a i) ^ 2 := by
      apply involution_unique (by omega) <;>
        (simp only [orderOf_pow, orderOf_xa, hc]; rfl)
    obtain ⟨_, he⟩ := closure_equiv_of_relations (m := 2) (by decide)
      (a i) (xa j) hc hsq hinv hout
    rw [hgen] at he
    exact Or.inr he

private theorem cyclic_embedding {G : Type*} [Group G] [IsCyclic G]
    (hfour : ∀ x : G, x ^ 4 = 1) :
    ∃ f : G →* QuaternionGroup 2, Function.Injective f := by
  obtain ⟨c, hc⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
  have hd : Nat.card G ∣ 4 := hc ▸ orderOf_dvd_of_pow_eq_one (hfour c)
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card G ∣ 2 ^ 2 from hd)
  obtain ⟨q, hq⟩ : ∃ q : QuaternionGroup 2, orderOf q = Nat.card G := by
    interval_cases k
    · exact ⟨1, by simp [he]⟩
    · exact ⟨a 2, by rw [he, orderOf_a]; rfl⟩
    · exact ⟨a 1, by rw [he, orderOf_a_one]; rfl⟩
  let e : G ≃* Subgroup.zpowers q := mulEquivOfCyclicCardEq (by
    rw [Nat.card_zpowers, hq])
  exact ⟨(Subgroup.zpowers q).subtype.comp e.toMonoidHom,
    (Subgroup.zpowers q).subtype_injective.comp e.injective⟩

/-- Every quaternion subgroup of exponent dividing four embeds into quaternion-eight. -/
public theorem exists_embedding_into_two_of_pow_four (hm : 2 ≤ m) (T : Subgroup (QuaternionGroup m))
    (hfour : ∀ t ∈ T, t ^ 4 = 1) :
    ∃ f : T →* QuaternionGroup 2, Function.Injective f := by
  rcases isCyclic_or_nonempty_equiv_two_of_pow_four hm T hfour with hcyc | he
  · let := hcyc
    apply cyclic_embedding
    intro t
    exact Subtype.ext (hfour t t.property)
  · obtain ⟨e⟩ := he
    exact ⟨e.toMonoidHom, e.injective⟩

private theorem sq_eq_one_of_mem_center_of_equiv {R : Type*} [Group R]
    (hm : 2 ≤ m) (model : R ≃* QuaternionGroup m)
    (z : R) (hz : z ∈ Subgroup.center R) : z ^ 2 = 1 := by
  apply model.injective
  rw [map_pow, map_one]
  apply sq_eq_one_of_mem_center hm
  apply Subgroup.mem_center_iff.mpr
  intro q
  obtain ⟨r, rfl⟩ := model.surjective q
  simpa only [← map_mul] using congrArg model (Subgroup.mem_center_iff.mp hz r)

/-- Every injection between subgroups of a quaternion group preserves equality
with ambient central elements. -/
public theorem injective_hom_preserves_center {R : Type*} [Group R]
    (hm : 2 ≤ m) (model : R ≃* QuaternionGroup m)
    (K T : Subgroup R) (f : T →* K) (hf : Function.Injective f)
    (t : T) (z : R) (hz : z ∈ Subgroup.center R) :
    ((t : R) = z ↔ ((f t : K) : R) = z) := by
  let F := K.subtype.comp f
  have hF : Function.Injective F := K.subtype_injective.comp hf
  have huniq (x y : R) (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxn : x ≠ 1) (hyn : y ≠ 1) :
      x = y := by
    apply model.injective
    have hsq (w : R) (hw : w ^ 2 = 1) : (model w) ^ 2 = 1 := by
      rw [← map_pow, hw, map_one]
    have hne (w : R) (hw : w ≠ 1) : model w ≠ 1 := by
      intro h
      exact hw (model.injective (h.trans model.map_one.symm))
    exact ((eq_one_or_eq_a_of_sq_eq_one (by omega) _ (hsq x hx)).resolve_left (hne x hxn)).trans
      ((eq_one_or_eq_a_of_sq_eq_one (by omega) _ (hsq y hy)).resolve_left (hne y hyn)).symm
  by_cases hz1 : z = 1
  · subst z
    change (t : R) = 1 ↔ F t = 1
    constructor
    · intro ht
      have ht1 : t = 1 := Subtype.ext ht
      rw [ht1, map_one]
    · intro ht
      have ht1 : t = 1 := hF (ht.trans F.map_one.symm)
      exact congrArg Subtype.val ht1
  have hz2 := sq_eq_one_of_mem_center_of_equiv hm model z hz
  change (t : R) = z ↔ F t = z
  constructor
  · intro ht
    have ht2 : t ^ 2 = 1 := Subtype.ext (by
      simpa only [Subgroup.coe_pow, ht, Subgroup.coe_one] using hz2)
    have hft2 : (F t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
    apply huniq _ _ hft2 hz2 _ hz1
    intro h
    have ht1 : t = 1 := hF (h.trans F.map_one.symm)
    exact hz1 (ht.symm.trans (congrArg Subtype.val ht1))
  · intro ht
    have ht2 : t ^ 2 = 1 := hF (by rw [map_pow, ht, hz2, map_one])
    apply huniq _ _ (congrArg Subtype.val ht2) hz2 _ hz1
    intro ht1
    have h : t = 1 := Subtype.ext ht1
    exact hz1 (ht.symm.trans (by rw [h, map_one]))

/-- A quaternion subgroup with central squares embeds into any quaternion eight,
preserving equality with every ambient central element. -/
public theorem exists_embedding_preserving_center {R : Type*} [Group R]
    (hm : 2 ≤ m) (model : R ≃* QuaternionGroup m)
    (K T : Subgroup R) (hK : Nonempty (K ≃* QuaternionGroup 2))
    (hsq : ∀ t : T, (t : R) ^ 2 ∈ Subgroup.center R) :
    ∃ f : T →* K, Function.Injective f ∧
      ∀ t : T, ∀ z : R, z ∈ Subgroup.center R →
        ((t : R) = z ↔ ((f t : K) : R) = z) := by
  have hfour (t : T) : (t : R) ^ 4 = 1 := by
    simpa only [← pow_mul] using sq_eq_one_of_mem_center_of_equiv hm model _ (hsq t)
  let U := T.map model.toMonoidHom
  have hU : ∀ u ∈ U, u ^ 4 = 1 := by
    rintro u ⟨t, ht, rfl⟩
    rw [← map_pow, hfour ⟨t, ht⟩, map_one]
  obtain ⟨g, hg⟩ := exists_embedding_into_two_of_pow_four hm U hU
  obtain ⟨e⟩ := hK
  let f : T →* K := e.symm.toMonoidHom.comp (g.comp (model.subgroupMap T).toMonoidHom)
  have hf : Function.Injective f := e.symm.injective.comp (hg.comp (model.subgroupMap T).injective)
  exact ⟨f, hf, injective_hom_preserves_center hm model K T f hf⟩

end QuaternionGroup
