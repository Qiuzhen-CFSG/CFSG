module

public import Theory.GroupTheory.PGroup.BinaryHallNoNormalFour
public import Theory.GroupTheory.PGroup.BinaryModularOmega
public import Theory.GroupTheory.PGroup.BinaryModular
public import Theory.GroupTheory.PGroup.Omega

/-!
# The binary cyclic-self-centralizer dichotomy

A normal elementary four-group supplies the modular involution action on a
cyclic normal self-centralizing subgroup. Its square centralizer is generated
by the cyclic subgroup and this involution. If the cyclic subgroup has order
at least eight, all involutions in the square centralizer lie in the chosen
four-group. Every normal elementary subgroup centralizes the squares, so
automorphisms preserve this four-group, which is the embedded first omega
subgroup. The order-four cyclic case is dihedral. In the absence of a normal
four-group, the existing Hall-factor classification finishes the proof.

Source: Gorenstein, *Finite Groups*, Section 5.4, Lemma 4.8, pp. 197–198.
The normal-four-group argument gives an alternative to the source's split
according to cyclicity of the action quotient.
-/

open Subgroup
open scoped commutatorElement

private theorem centralizes_zpowers_of_conj_eq {G : Type*} [Group G]
    (a g : G) (h : g * a * g⁻¹ = a) :
    g ∈ centralizer (zpowers a : Set G) := by
  intro x hx
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
  exact ((show Commute a g from (mul_inv_eq_iff_eq_mul.mp h).symm).zpow_left i).eq

private theorem normal_elementary_le_centralizer_sq
    {G : Type*} [Group G] (a : G) [(zpowers a).Normal]
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] :
    U ≤ centralizer (zpowers (a ^ 2) : Set G) := by
  intro x hx
  have hc : ⁅x, a⁆ ∈ U ⊓ zpowers a :=
    commutator_le_inf U (zpowers a)
      (commutator_mem_commutator hx (mem_zpowers a))
  have hc2 : ⁅x, a⁆ ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hc.1
  have hca : Commute ⁅x, a⁆ a :=
    ((zpowers a).le_centralizer hc.2 a (mem_zpowers a)).symm
  apply centralizes_zpowers_of_conj_eq
  change MulAut.conj x (a ^ 2) = a ^ 2
  rw [map_pow, conj_eq_commutatorElement_mul, hca.mul_pow, hc2, one_mul]

private theorem conj_discrepancy_sq_eq_one
    {G : Type*} [Group G] (a g : G) [(zpowers a).Normal]
    (hg : g ∈ centralizer (zpowers (a ^ 2) : Set G)) :
    ⁅g, a⁆ ^ 2 = 1 := by
  have hcA : ⁅g, a⁆ ∈ zpowers a := by
    exact (zpowers a).mul_mem
      (Normal.conj_mem inferInstance a (mem_zpowers a) g)
      ((zpowers a).inv_mem (mem_zpowers a))
  have hca : Commute ⁅g, a⁆ a :=
    ((zpowers a).le_centralizer hcA a (mem_zpowers a)).symm
  have hp : ⁅g, a⁆ ^ 2 * a ^ 2 = a ^ 2 := by
    rw [← hca.mul_pow, ← conj_eq_commutatorElement_mul, ← map_pow]
    exact mul_inv_eq_iff_eq_mul.mpr (hg _ (mem_zpowers _)).symm
  exact mul_right_cancel (hp.trans (one_mul (a ^ 2)).symm)

private theorem eq_one_or_of_sq_eq_one_in_cyclic
    {G : Type*} [Group G] [Finite G] (A : Subgroup G) [IsCyclic A]
    (z : G) (hzA : z ∈ A) (hz : orderOf z = 2)
    (x : G) (hxA : x ∈ A) (hx : x ^ 2 = 1) : x = 1 ∨ x = z := by
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  right
  exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
    (x := (⟨x, hxA⟩ : A)) (y := ⟨z, hzA⟩)
    (by simpa using orderOf_eq_prime hx hx1) (by simpa using hz))

private theorem centralizer_sq_eq_sup_of_normal_four_element
    {G : Type*} [Group G] [Finite G] (a : G) [(zpowers a).Normal]
    (hC : centralizer (zpowers a : Set G) ≤ zpowers a)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (e : G) (heU : e ∈ U) (heA : e ∉ zpowers a) :
    centralizer (zpowers (a ^ 2) : Set G) = zpowers a ⊔ zpowers e := by
  let z := ⁅e, a⁆
  have hz : z ∈ U ⊓ zpowers a := commutator_le_inf U (zpowers a)
    (commutator_mem_commutator heU (mem_zpowers a))
  have hz2 : z ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hz.1
  have hz1 : z ≠ 1 := by
    intro h
    apply heA
    apply hC
    apply centralizes_zpowers_of_conj_eq
    change MulAut.conj e a = a
    rw [conj_eq_commutatorElement_mul, show ⁅e, a⁆ = 1 from h, one_mul]
  have hzorder : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  apply le_antisymm
  · intro g hg
    have hcA : ⁅g, a⁆ ∈ zpowers a := (zpowers a).mul_mem
      (Normal.conj_mem inferInstance a (mem_zpowers a) g)
      ((zpowers a).inv_mem (mem_zpowers a))
    rcases eq_one_or_of_sq_eq_one_in_cyclic (zpowers a) z hz.2 hzorder
      ⁅g, a⁆ hcA (conj_discrepancy_sq_eq_one a g hg) with hc | hc
    · apply (le_sup_left : zpowers a ≤ zpowers a ⊔ zpowers e)
      apply hC
      apply centralizes_zpowers_of_conj_eq
      change MulAut.conj g a = a
      rw [conj_eq_commutatorElement_mul, hc, one_mul]
    · have hconj : g * a * g⁻¹ = e * a * e⁻¹ := by
        change MulAut.conj g a = MulAut.conj e a
        rw [conj_eq_commutatorElement_mul, conj_eq_commutatorElement_mul, hc]
      have hdA : e⁻¹ * g ∈ zpowers a := by
        apply hC
        apply centralizes_zpowers_of_conj_eq
        calc
          (e⁻¹ * g) * a * (e⁻¹ * g)⁻¹ = e⁻¹ * (g * a * g⁻¹) * e := by group
          _ = a := by rw [hconj]; group
      have hh := (zpowers a ⊔ zpowers e).mul_mem
        ((le_sup_right : zpowers e ≤ zpowers a ⊔ zpowers e) (mem_zpowers e))
        ((le_sup_left : zpowers a ≤ zpowers a ⊔ zpowers e) hdA)
      simpa using hh
  · apply sup_le
    · exact (zpowers a).le_centralizer.trans (centralizer_le (zpowers_le.mpr
        ((zpowers a).pow_mem (mem_zpowers a) 2)))
    · exact zpowers_le.mpr (normal_elementary_le_centralizer_sq a U heU)

private theorem exists_twist_of_normal_four
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (a : G) [(zpowers a).Normal]
    (hC : centralizer (zpowers a : Set G) ≤ zpowers a)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : Nat.card U = 4) :
    ∃ (e : G) (n : ℕ), 2 ≤ n ∧ orderOf a = 2 ^ n ∧
      e ∈ U ∧ e ∉ zpowers a ∧ e ^ 2 = 1 ∧
      a ^ (2 ^ (n - 1)) ∈ U ∧
      e * a * e⁻¹ = a ^ (1 + 2 ^ (n - 1)) := by
  have hUA : ¬ U ≤ zpowers a := by
    intro h
    let : IsCyclic U := Subgroup.isCyclic_of_le h
    have hh : Nat.card U ∣ 2 := by
      rw [← IsCyclic.exponent_eq_card]
      exact IsElementaryAbelian.exponent_dvd_p 2 U
    norm_num [hU] at hh
  obtain ⟨e, heU, heA⟩ := SetLike.not_le_iff_exists.mp hUA
  obtain ⟨n, ha⟩ := hG.exists_orderOf_eq_pow a
  have he2 : e ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ heU
  let z := ⁅e, a⁆
  have hz : z ∈ U ⊓ zpowers a := commutator_le_inf U (zpowers a)
    (commutator_mem_commutator heU (mem_zpowers a))
  have hz2 : z ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hz.1
  have hz1 : z ≠ 1 := by
    intro h
    apply heA
    apply hC
    apply centralizes_zpowers_of_conj_eq
    change MulAut.conj e a = a
    rw [conj_eq_commutatorElement_mul, show ⁅e, a⁆ = 1 from h, one_mul]
  have hzorder : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hnpos : 0 < n := by
    by_contra hn
    have ha1 : a = 1 := orderOf_eq_one_iff.mp (by simpa [show n = 0 by omega] using ha)
    exact hz1 (by simp [z, ha1])
  have hsplit : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  have hhalf : orderOf (a ^ (2 ^ (n - 1))) = 2 := by
    have hh := orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos a))
      (show 2 ∣ orderOf a by rw [ha, hsplit]; exact dvd_mul_left _ _)
    simpa [ha, hsplit] using hh
  have hzval : z = a ^ (2 ^ (n - 1)) := congrArg Subtype.val
    (IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨z, hz.2⟩ : zpowers a))
      (y := ⟨a ^ (2 ^ (n - 1)), pow_mem (mem_zpowers a) _⟩)
      (by simpa using hzorder) (by simpa using hhalf))
  have hact : e * a * e⁻¹ = a ^ (1 + 2 ^ (n - 1)) := by
    change MulAut.conj e a = _
    rw [conj_eq_commutatorElement_mul, show ⁅e, a⁆ = a ^ (2 ^ (n - 1)) from hzval,
      ← pow_succ, Nat.add_comm]
  have hn2 : 2 ≤ n := by
    by_contra hn
    have hn1 : n = 1 := by omega
    have heq : MulAut.conj e a = 1 := by
      change e * a * e⁻¹ = 1
      rw [hact]
      simpa only [ha, hn1, pow_one, Nat.sub_self, pow_zero, Nat.reduceAdd] using pow_orderOf_eq_one a
    have ha1 : a = 1 := (MulAut.conj e).injective (heq.trans (map_one _).symm)
    simp [ha1, hn1] at ha
  exact ⟨e, n, hn2, ha, heU, heA, he2, hzval ▸ hz.1, hact⟩

private theorem closure_pair_eq_subgroup_top
    {G : Type*} [Group G] (a e : G) (M : Subgroup G)
    (hM : M = zpowers a ⊔ zpowers e) :
    ∃ aM eM : M, (aM : G) = a ∧ (eM : G) = e ∧
      closure ({aM, eM} : Set M) = ⊤ := by
  have haM : a ∈ M := hM ▸ (le_sup_left : zpowers a ≤ zpowers a ⊔ zpowers e) (mem_zpowers a)
  have heM : e ∈ M := hM ▸ (le_sup_right : zpowers e ≤ zpowers a ⊔ zpowers e) (mem_zpowers e)
  refine ⟨⟨a, haM⟩, ⟨e, heM⟩, rfl, rfl, ?_⟩
  apply (map_injective M.subtype_injective)
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, M.range_subtype]
  rw [Set.image_insert_eq, Set.image_singleton]
  change closure ({a, e} : Set G) = M
  rw [← Set.singleton_union, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure, hM]

private theorem modular_of_normal_four_twist
    {G : Type*} [Group G] [Finite G] (a e : G) (n : ℕ)
    [(zpowers a).Normal] (hn : 3 ≤ n) (ha : orderOf a = 2 ^ n)
    (he : e ^ 2 = 1) (heA : e ∉ zpowers a)
    (hact : e * a * e⁻¹ = a ^ (1 + 2 ^ (n - 1)))
    (M : Subgroup G) (hM : M = zpowers a ⊔ zpowers e) :
    IsBinaryModularGroup M := by
  obtain ⟨aM, eM, haM, heM, hgen⟩ := closure_pair_eq_subgroup_top a e M hM
  refine ⟨n, hn, ?_, aM, eM, ?_, ?_, ?_, hgen⟩
  · rw [hM, card_sup_zpowers_of_normalizing_involution (zpowers a) e he heA
      (by rw [normalizer_eq_top]; trivial), Nat.card_zpowers, ha, pow_succ, Nat.mul_comm]
  · simpa [← haM] using ha
  · have heorder : orderOf e = 2 := orderOf_eq_prime he
      (fun h => heA (h ▸ (zpowers a).one_mem))
    simpa [← heM] using heorder
  · apply Subtype.ext
    simpa only [coe_mul, coe_inv, coe_pow, haM, heM] using hact

private theorem involutions_in_modular_join
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (a e : G) (n : ℕ) [(zpowers a).Normal] (hn : 3 ≤ n)
    (ha : orderOf a = 2 ^ n) (he : e ^ 2 = 1) (heA : e ∉ zpowers a)
    (hact : e * a * e⁻¹ = a ^ (1 + 2 ^ (n - 1)))
    (U : Subgroup G) (heU : e ∈ U) (hzU : a ^ (2 ^ (n - 1)) ∈ U)
    (x : G) (hx : x ∈ zpowers a ⊔ zpowers e) (hx2 : x ^ 2 = 1) : x ∈ U := by
  classical
  have hsplit : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  have hzorder : orderOf (a ^ (2 ^ (n - 1))) = 2 := by
    have hh := orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos a))
      (show 2 ∣ orderOf a by rw [ha, hsplit]; exact dvd_mul_left _ _)
    simpa [ha, hsplit] using hh
  have hsmall (d : G) (hd : d ∈ zpowers a) (hd2 : d ^ 2 = 1) : d ∈ U := by
    rcases eq_one_or_of_sq_eq_one_in_cyclic (zpowers a)
      (a ^ (2 ^ (n - 1))) (pow_mem (mem_zpowers a) _) hzorder d hd hd2 with rfl | rfl
    · exact U.one_mem
    · exact hzU
  obtain ⟨d, hd, t, ht, rfl⟩ := mem_sup_of_normal_left.mp hx
  have htcase : t = 1 ∨ t = e := by
    have heorder : orderOf e = 2 := orderOf_eq_prime he
      (fun h => heA (h ▸ (zpowers a).one_mem))
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp ht)
    have hi2 : i < 2 := by simpa only [heorder] using Finset.mem_range.mp hi
    interval_cases i <;> simp
  rcases htcase with ht1 | hte
  · simp only [ht1, mul_one] at hx2 ⊢
    exact hsmall d hd hx2
  · subst t
    have haction : e * d * e⁻¹ = d ^ (1 + 2 ^ (n - 1)) := by
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hd)
      change MulAut.conj e (a ^ k) = _
      rw [map_pow, MulAut.conj_apply, hact, ← pow_mul, ← pow_mul, Nat.mul_comm]
    have hdPow : d ^ (2 + 2 ^ (n - 1)) = 1 := by
      calc
        d ^ (2 + 2 ^ (n - 1)) = d * d ^ (1 + 2 ^ (n - 1)) := by
          rw [← pow_succ']; congr 1; omega
        _ = d * (e * d * e⁻¹) := by rw [haction]
        _ = (d * e) ^ 2 * (e ^ 2)⁻¹ := by simp only [pow_two]; group
        _ = 1 := by rw [hx2, he]; simp
    have hhalf : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
      conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega]
      rw [pow_succ]
    have hodd : Nat.Coprime 2 (1 + 2 ^ (n - 2)) := by
      apply Nat.coprime_two_left.mpr
      exact Odd.add_even (by decide : Odd (1 : ℕ))
        (Nat.even_pow.mpr ⟨by decide, by omega⟩)
    have hd2 : d ^ 2 = 1 := by
      apply (hG.powEquiv hodd).injective
      simp only [IsPGroup.powEquiv_apply, one_pow, ← pow_mul]
      convert hdPow using 1
      rw [hhalf]
      congr 1
      ring
    exact U.mul_mem (hsmall d hd hd2) heU

private theorem characteristic_omega_of_normal_four_twist
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (a e : G) (n : ℕ) [(zpowers a).Normal] (hn : 3 ≤ n)
    (ha : orderOf a = 2 ^ n) (he : e ^ 2 = 1) (heA : e ∉ zpowers a)
    (hact : e * a * e⁻¹ = a ^ (1 + 2 ^ (n - 1)))
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (heU : e ∈ U) (hzU : a ^ (2 ^ (n - 1)) ∈ U)
    (hM : centralizer (zpowers (a ^ 2) : Set G) = zpowers a ⊔ zpowers e) :
    ((omega₁ (centralizer (zpowers (a ^ 2) : Set G)) (p := 2)).map
      (centralizer (zpowers (a ^ 2) : Set G)).subtype).Characteristic := by
  let M := centralizer (zpowers (a ^ 2) : Set G)
  have hUM : U ≤ M := normal_elementary_le_centralizer_sq a U
  have hinvol (x : G) (hx : x ∈ M) (hx2 : x ^ 2 = 1) : x ∈ U :=
    involutions_in_modular_join hG a e n hn ha he heA hact U heU hzU x (hM ▸ hx) hx2
  have hchar : U.Characteristic := by
    apply characteristic_iff_map_le.mpr
    intro f
    let V := U.map f.toMonoidHom
    let : V.Normal := Normal.map inferInstance f.toMonoidHom f.surjective
    let : IsElementaryAbelian 2 V := IsElementaryAbelian.map f.toMonoidHom
    have hVM : V ≤ M := normal_elementary_le_centralizer_sq a V
    intro x hx
    exact hinvol x (hVM hx) (elemPow_eq_one_of_isElementaryAbelian x hx)
  have heq : (omega₁ M (p := 2)).map M.subtype = U := by
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply (Subgroup.closure_le _).2
      intro x hx
      exact hinvol x x.property (congrArg Subtype.val (show x ^ 2 = 1 by simpa using hx))
    · intro x hx
      refine mem_map.mpr ⟨⟨x, hUM hx⟩, ?_, rfl⟩
      apply Subgroup.subset_closure
      change (⟨x, hUM hx⟩ : M) ^ (2 ^ 1) = 1
      apply Subtype.ext
      simpa using elemPow_eq_one_of_isElementaryAbelian x hx
  change ((omega₁ M (p := 2)).map M.subtype).Characteristic
  rw [heq]
  exact hchar

private theorem dihedral_of_normal_four_twist_order_four
    {G : Type*} [Group G] [Finite G] (a e : G) [(zpowers a).Normal]
    (hC : centralizer (zpowers a : Set G) ≤ zpowers a)
    (ha : orderOf a = 4) (he : e ^ 2 = 1) (heA : e ∉ zpowers a)
    (hact : e * a * e⁻¹ = a ^ 3) : Nonempty (G ≃* DihedralGroup 4) := by
  let A := zpowers a
  let f : G →* MulAut A := MulAut.conjNormal
  have hker : f.ker ≤ A := by
    intro g hg
    apply hC
    intro b hb
    have hh := congrArg (fun t : MulAut A => (t ⟨b, hb⟩ : G)) (MonoidHom.mem_ker.mp hg)
    change g * b * g⁻¹ = b at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hindex : A.index ≤ 2 := calc
    A.index ≤ f.ker.index := index_antitone hker
    _ = Nat.card f.range := index_ker f
    _ ≤ Nat.card (MulAut A) := card_le_card_group _
    _ = 2 := by rw [IsCyclic.card_mulAut, Nat.card_zpowers, ha]; decide
  have hcardA : Nat.card A = 4 := by rw [Nat.card_zpowers, ha]
  have hcardG : Nat.card G ≤ 8 := by
    rw [← A.card_mul_index, hcardA]
    omega
  have hcardK : Nat.card (zpowers a ⊔ zpowers e : Subgroup G) = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution (zpowers a) e he heA
      (by rw [normalizer_eq_top]; trivial), Nat.card_zpowers, ha]
  have htop : zpowers a ⊔ zpowers e = ⊤ :=
    eq_top_of_le_card _ (by omega)
  have hgen : closure ({a, e} : Set G) = ⊤ := by
    rw [← Set.singleton_union, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure, htop]
  have hcard : Nat.card G = 2 * 4 := by
    rw [htop, card_top] at hcardK
    exact hcardK
  have ha4 : a ^ 4 = 1 := ha ▸ pow_orderOf_eq_one a
  have hinv : e * a * e⁻¹ = a⁻¹ := by
    rw [hact]
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using ha4
  exact dihedralGroup_equiv_of_presentation (by decide) a e ha he hinv hgen hcard

namespace IsPGroup

/-- A finite two-group with a normal cyclic self-centralizing subgroup is a
Hall factor, or the centralizer of the squares of that cyclic subgroup is
modular and its first omega subgroup is characteristic in the ambient group.
The modular alternative includes the case where the cyclic subgroup has
index two. -/
public theorem isBinaryHallFactor_or_isBinaryModularGroup_centralizer_sq
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (a : G) [(zpowers a).Normal]
    (hC : centralizer (zpowers a : Set G) ≤ zpowers a) :
    IsBinaryHallFactor G ∨
      (IsBinaryModularGroup (centralizer (zpowers (a ^ 2) : Set G)) ∧
        ((omega₁ (centralizer (zpowers (a ^ 2) : Set G)) (p := 2)).map
          (centralizer (zpowers (a ^ 2) : Set G)).subtype).Characteristic) := by
  by_cases hfour : ∃ U : Subgroup G, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4
  · obtain ⟨U, hUn, hUe, hU⟩ := hfour
    let : U.Normal := hUn
    let : IsElementaryAbelian 2 U := hUe
    obtain ⟨e, n, hn, ha, heU, heA, he, hzU, hact⟩ :=
      exists_twist_of_normal_four hG a hC U hU
    by_cases hn3 : 3 ≤ n
    · right
      have hM := centralizer_sq_eq_sup_of_normal_four_element a hC U e heU heA
      exact ⟨modular_of_normal_four_twist a e n hn3 ha he heA hact _ hM,
        characteristic_omega_of_normal_four_twist hG a e n hn3 ha he heA hact U heU hzU hM⟩
    · have hn2 : n = 2 := by omega
      have hd := dihedral_of_normal_four_twist_order_four a e hC
        (by simpa [hn2] using ha) he heA (by simpa [hn2] using hact)
      exact Or.inl (Or.inr (Or.inr (Or.inl ⟨4, hd⟩)))
  · exact Or.inl (hG.isBinaryHallFactor_of_no_normal_four hfour)

/-- A cyclic self-centralizer either gives a Hall factor or an abelian
second omega and a noncyclic first omega in the centralizer of its squares.
These are the local inputs for excluding the modular case of Hall's theorem. -/
public theorem isBinaryHallFactor_or_omega_centralizer_sq
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (a : G) [(zpowers a).Normal]
    (hC : centralizer (zpowers a : Set G) ≤ zpowers a) :
    IsBinaryHallFactor G ∨
      (IsMulCommutative (omega (centralizer (zpowers (a ^ 2) : Set G)) (p := 2) 2) ∧
        ¬ IsCyclic (omega₁ (centralizer (zpowers (a ^ 2) : Set G)) (p := 2))) := by
  rcases hG.isBinaryHallFactor_or_isBinaryModularGroup_centralizer_sq a hC with
    hHall | ⟨hmod, _⟩
  · exact Or.inl hHall
  · exact Or.inr ⟨hmod.isMulCommutative_omega_two, hmod.not_isCyclic_omega_one⟩

end IsPGroup
