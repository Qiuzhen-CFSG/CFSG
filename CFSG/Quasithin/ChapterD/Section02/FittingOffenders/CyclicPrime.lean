module


public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Preliminaries
public import CFSG.Quasithin.ChapterD.Section02.SmallSupport
public import Theory.Representation.BinaryGroupAction
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Odd primes moved by cyclic minimum offenders

An involution moving a normal odd prime group inverts a nonidentity
commutator. The small-support theorem limits its order to three or five,
and the prime-group hypothesis identifies the prime. At displacement rank
one only three occurs. For a rank-one member of the genuine starred cubic
family, the ratio is the displacement dimension. Transport the given
representation to its actual elementary abelian additive group to apply
these group-action results.

Uniqueness of the inverted small-support factor identifies the actual
prime-core commutator. Saturation fixes its complementary space and yields
the order-three and order-five support decompositions, with explicit cyclic
group equivalences. A separate rank-one theorem only assumes action ratio
below two; it is the local input after a hyperplane ratio drop.

Source: Aschbacher--Smith, D.2.13(1)--(4) in the cyclic branch,
printed pp.184--185. The noncyclic hyperplane reduction remains separate.
-/


public section
open Subgroup Representation.BinaryOffender
open scoped commutatorElement ENNReal
namespace CFSG.Quasithin.ChapterD

private theorem exists_inverted_of_nontrivial_commutator
    {G : Type*} [Group G] (P : Subgroup G) [P.Normal]
    (t : G) (ht : IsInvolution t) (hm : ⁅P, zpowers t⁆ ≠ ⊥) :
    ∃ x ∈ P, x ≠ 1 ∧ t * x * t⁻¹ = x⁻¹ := by
  have hex : ∃ y ∈ P, ⁅y, t⁆ ≠ 1 := by
    by_contra! h
    apply hm
    rw [commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨n, rfl⟩ := ha
    exact ((commutatorElement_eq_one_iff_commute.mp (h y hy)).symm.zpow_left n).eq
  obtain ⟨y, hy, hn⟩ := hex
  refine ⟨⁅y,t⁆, commutator_le_left P (zpowers t)
    (commutator_mem_commutator hy (mem_zpowers t)), hn, ?_⟩
  have htt : t * t = 1 := by simpa only [pow_two] using ht.2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  simp only [commutatorElement_def, mul_inv_rev, inv_inv, hti, mul_assoc, htt, mul_one]

private theorem prime_eq_of_prime_order
    {G : Type*} [Group G] {p q : ℕ} [Fact p.Prime] (hq : q.Prime)
    (P : Subgroup G) (hP : IsPGroup p P) {x : G} (hx : x ∈ P)
    (hne : x ≠ 1) (ho : orderOf x = q) : p = q := by
  have hd := hP.dvd_orderOf (g := (⟨x,hx⟩ : P)) (fun h => hne (congrArg Subtype.val h))
  rw [← orderOf_injective P.subtype P.subtype_injective] at hd
  change p ∣ orderOf x at hd
  rw [ho] at hd
  exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hq).mp hd

private theorem odd_order_of_mem_pGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (P : Subgroup G) (hP : IsPGroup p P) {x : G} (hx : x ∈ P) : Odd (orderOf x) := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  exact (hn ▸ hp.pow : Odd (Nat.card P)).of_dvd_nat (P.orderOf_dvd_natCard hx)

private theorem faithful_fixing_bot
    {G W : Type*} [Group G] [Group W] [MulDistribMulAction G W] [FaithfulSMul G W] :
    fixingSubgroup G (Set.univ : Set W) = ⊥ := by
  apply bot_unique
  intro g hg
  apply eq_of_smul_eq_smul (α := W)
  intro w
  simpa only [one_smul] using ((mem_fixingSubgroup_iff (M := G)).mp hg w (Set.mem_univ w))

/-- A small binary involution moving a normal odd prime group forces the prime to be 3 or 5. -/
theorem prime_three_or_five_of_small_involution
    {G W : Type*} [Group G] [Finite G] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction G W] [FaithfulSMul G W]
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (t : G) (ht : IsInvolution t) (hm : ⁅P, zpowers t⁆ ≠ ⊥)
    (hs : Nat.card (commutatorAction (zpowers t) W) ≤ 4) : p = 3 ∨ p = 5 := by
  obtain ⟨x, hx, hn, hi⟩ := exists_inverted_of_nontrivial_commutator P t ht hm
  have ho := odd_order_of_mem_pGroup hp P hP hx
  rcases invertedOddElement_order_three_or_five_of_small_involution_support
    x t hn ho ht hi hs (faithful_fixing_bot (G := G) (W := W)) with h3 | h5
  · exact Or.inl (prime_eq_of_prime_order (by decide) P hP hx hn h3)
  · exact Or.inr (prime_eq_of_prime_order (by decide) P hP hx hn h5)

/-- At displacement rank one the moved odd prime is exactly three. -/
theorem prime_three_of_involution_support_two
    {G W : Type*} [Group G] [Finite G] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction G W] [FaithfulSMul G W]
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (t : G) (ht : IsInvolution t) (hm : ⁅P, zpowers t⁆ ≠ ⊥)
    (hs : Nat.card (commutatorAction (zpowers t) W) = 2) : p = 3 := by
  obtain ⟨x, hx, hn, hi⟩ := exists_inverted_of_nontrivial_commutator P t ht hm
  have ho := odd_order_of_mem_pGroup hp P hP hx
  have h3 := (invertedOddElement_order_three_of_involution_card_two
    x t hn ho ht hi hs (faithful_fixing_bot (G := G) (W := W))).1
  exact prime_eq_of_prime_order (by decide) P hP hx hn h3

/-- Saturated small involution support identifies the actual odd-core commutator.
The two cases are a moved three-group at displacement rank one and a moved
five-group at displacement rank two. -/
theorem primeCore_commutator_of_saturated_involution
    {G W : Type*} [Group G] [Finite G] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction G W] [FaithfulSMul G W]
    {p k : ℕ} [Fact p.Prime] (hk : k = 1 ∨ k = 2) (hp : p = 2 * k + 1)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P) (hPF : P ≤ fittingSubgroup G)
    (t : G) (ht : IsInvolution t) (hm : ⁅P, zpowers t⁆ ≠ ⊥)
    (hs : Nat.card (commutatorAction (zpowers t) W) = 2 ^ k) :
    Nat.card (⁅P, zpowers t⁆ : Subgroup G) = p ∧
      Nat.card (commutatorAction (⁅P, zpowers t⁆ : Subgroup G) W) = 2 ^ (2 * k) ∧
      (∀ v ∈ FixedPoints.subgroup (⁅P, zpowers t⁆ : Subgroup G) W, t • v = v) := by
  classical
  have hpodd : Odd p := hp ▸ ⟨k, rfl⟩
  have hfaith := faithful_fixing_bot (G := G) (W := W)
  have hfactor (x : G) (hx : x ∈ P) (hne : x ≠ 1)
      (hinv : t * x * t⁻¹ = x⁻¹) :
      zpowers x ∈ smallSupportFactors G W k := by
    have hodd := odd_order_of_mem_pGroup hpodd P hP hx
    have hd : orderOf x = p ∧
        Nat.card (commutatorAction (zpowers x) W) = 2 ^ (2 * k) := by
      rcases hk with rfl | rfl
      · have hd := invertedOddElement_order_three_of_involution_card_two
          x t hne hodd ht hinv (by simpa using hs) hfaith
        exact ⟨hd.1.trans (by omega), by simpa using hd.2⟩
      · obtain ⟨h35, h5⟩ := invertedOddElement_order_three_or_five_of_involution_card_four
          x t hne hodd ht hinv (by simpa using hs) hfaith
        have he : orderOf x = 5 := h35.resolve_left (fun h3 => by
          have := prime_eq_of_prime_order (by decide) P hP hx hne h3
          omega)
        exact ⟨he.trans (by omega), by simpa using h5 he⟩
    exact ⟨(zpowers_le.mpr hx).trans hPF, by rw [Nat.card_zpowers, hd.1, hp], hd.2⟩
  have hinverts (x : G) (hi : t * x * t⁻¹ = x⁻¹) :
      ∀ y ∈ zpowers x, t * y * t⁻¹ = y⁻¹ := by
    rintro y ⟨n, rfl⟩
    rw [← conj_zpow, hi, inv_zpow]
  obtain ⟨x, hx, hxn, hxi⟩ := exists_inverted_of_nontrivial_commutator P t ht hm
  have hX := hfactor x hx hxn hxi
  have hunique : ∀ y ∈ P, y ≠ 1 → t * y * t⁻¹ = y⁻¹ → zpowers y = zpowers x := by
    rcases smallSupportFactors_involution_alternative (V := W) hk t ht hs with hfix | hmove
    · have hc := (hfix.1 _ hX).1 x (mem_zpowers x)
      have he : x = x⁻¹ := by simpa only [hc.eq, mul_inv_cancel_right] using hxi
      have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact (congrArg (fun z => z * x) he).trans (inv_mul_cancel x)
      have hdiv := orderOf_dvd_of_pow_eq_one hx2
      have hord : orderOf x = 2 * k + 1 := by simpa only [Nat.card_zpowers] using hX.2.1
      rw [hord] at hdiv
      have hb := Nat.le_of_dvd (by decide : 0 < 2) hdiv
      rcases hk with rfl | rfl <;> omega
    · obtain ⟨X, _, _, huniq, _⟩ := hmove
      intro y hy hyn hyi
      exact (huniq _ (hfactor y hy hyn hyi) (hinverts y hyi)).trans
        (huniq _ hX (hinverts x hxi)).symm
  have hDX : ⁅P, zpowers t⁆ ≤ zpowers x := by
    rw [commutator_le]
    intro y hy a ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp ha)
    have hnt := Finset.mem_range.mp hn
    have hto : orderOf t = 2 := orderOf_eq_prime ht.2 ht.1
    rw [hto] at hnt
    interval_cases n
    · simp
    · simp only [pow_one]
      by_cases hz : ⁅y,t⁆ = 1
      · simp [hz]
      · have hzP := commutator_le_left P (zpowers t)
          (commutator_mem_commutator hy (mem_zpowers t))
        have hzi : t * ⁅y,t⁆ * t⁻¹ = ⁅y,t⁆⁻¹ := by
          have htt : t * t = 1 := by simpa only [pow_two] using ht.2
          have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
          simp only [commutatorElement_def, mul_inv_rev, inv_inv, hti,
            mul_assoc, htt, mul_one]
        rw [← hunique _ hzP hz hzi]
        exact mem_zpowers _
  have hXD : zpowers x ≤ ⁅P, zpowers t⁆ := by
    apply zpowers_le.mpr
    have hx2 : x ^ 2 ∈ ⁅P, zpowers t⁆ := by
      have he : ⁅x,t⁆ = x ^ 2 := by
        calc
          ⁅x,t⁆ = x * (t * x * t⁻¹)⁻¹ := by simp [commutatorElement_def, mul_assoc]
          _ = x ^ 2 := by rw [hxi, inv_inv, pow_two]
      rw [← he]
      exact commutator_mem_commutator hx (mem_zpowers t)
    obtain ⟨n, hn⟩ := exists_pow_eq_pow_two_mul (pow_orderOf_eq_one x)
      (odd_order_of_mem_pGroup hpodd P hP hx) 1
    rw [pow_one, pow_mul] at hn
    rw [hn]
    exact pow_mem hx2 n
  have heq := le_antisymm hDX hXD
  rw [heq]
  refine ⟨hX.2.1.trans hp.symm, hX.2.2, ?_⟩
  exact (invertedOddElement_full_support x t (odd_order_of_mem_pGroup hpodd P hP hx)
    ht hxi (by rw [hX.2.2, hs, ← pow_mul, Nat.mul_comm k 2]) hfaith).2.1

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [FiniteDimensional (ZMod 2) V] in
private theorem moved_involution_eq_range (t : G) (ht : orderOf t = 2) :
    subspaceCommutator ρ ⊤ (zpowers t) = LinearMap.range (ρ t - LinearMap.id) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, _, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp ha)
    have hi := Finset.mem_range.mp hi
    rw [ht] at hi
    interval_cases i
    · simp
    · exact ⟨v, by simp⟩
  · rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨t, mem_zpowers t, v, Submodule.mem_top, rfl⟩

private theorem rank_one_generator {A : Subgroup G} (hA : IsElementaryTwo A) (hr : rank A = 1) :
    ∃ t : G, orderOf t = 2 ∧ zpowers t = A := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨a, ha⟩ := ne_bot_iff_exists_ne_one.mp hA.1
  have ht : orderOf (a : G) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (a : G) a.property)
      (fun h => ha (Subtype.ext h))
  refine ⟨a, ht, eq_of_le_of_card_ge (zpowers_le.mpr a.property) ?_⟩
  rw [hA.card_eq_two_pow_rank, hr, Nat.card_zpowers, ht]
  norm_num

/-- D.2.13(1) and the ratio assertion of (3), for a rank-one starred actor. -/
theorem source_lemma_D_2_13_cyclic_prime
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : rank A = 1) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hm : ⁅pCore p G, A⁆ ≠ ⊥) :
    (p = 3 ∨ p = 5) ∧ (cubicRatio ρ = 1 ∨ cubicRatio ρ = 2) ∧
      (cubicRatio ρ = 1 → p = 3) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := Representation.BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative V) := Representation.BinaryGroupAction.elementary
  let : FaithfulSMul G (Multiplicative V) := Representation.BinaryGroupAction.faithful ρ hf
  obtain ⟨t, ht, hgen⟩ := rank_one_generator hA.1.2.1 hr
  have hti : IsInvolution t := ⟨fun h => by simp [h] at ht, ht ▸ pow_orderOf_eq_one t⟩
  have hdim : fixedCodim ρ A ≤ 2 := by
    have hb := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.trans_le hA.1.1)
    simpa only [hr, mul_one] using hb
  have hs : Nat.card (commutatorAction (zpowers t) (Multiplicative V)) = 2 ^ fixedCodim ρ A := by
    rw [Representation.BinaryGroupAction.commutator_card, moved_involution_eq_range ρ t ht,
      ← fixedCodim_zpowers_eq_displacement_rank, hgen]
  have hm' : ⁅pCore p G, zpowers t⁆ ≠ ⊥ := hgen ▸ hm
  refine ⟨prime_three_or_five_of_small_involution (W := Multiplicative V) hp
    (pCore p G) pCore_isPGroup t hti hm' ?_,
    QhatStar.ratio_one_or_two_of_rank_one ρ hf hA hr, ?_⟩
  · rw [hs]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hdim)
  · intro hq
    have hcodim : fixedCodim ρ A = 1 := by
      have he := hA.1.2.2.2
      rw [actionRatio, hr, Nat.cast_one, div_one, hq] at he
      exact_mod_cast he
    apply prime_three_of_involution_support_two (W := Multiplicative V)
      hp (pCore p G) pCore_isPGroup t hti hm'
    rw [hs, hcodim, pow_one]

/-- The support and fixed-space conclusions of D.2.13 for a saturated cyclic
actor, stated for any normal prime subgroup of the Fitting subgroup. -/
theorem cyclic_actor_saturated_support
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : IsElementaryTwo A)
    (hr : rank A = 1) {p k : ℕ} [Fact p.Prime]
    (hk : k = 1 ∨ k = 2) (hp : p = 2 * k + 1)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P) (hPF : P ≤ fittingSubgroup G)
    (hm : ⁅P, A⁆ ≠ ⊥) (hd : fixedCodim ρ A = k) :
    Nat.card (⁅P, A⁆ : Subgroup G) = p ∧
      Nonempty ((⁅P, A⁆ : Subgroup G) ≃* Multiplicative (ZMod p)) ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅P, A⁆) = 2 * k ∧
      IsCompl (subspaceCommutator ρ ⊤ ⁅P, A⁆) (fixedSpace ρ (⁅P, A⁆ ⊔ A)) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := Representation.BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative V) := Representation.BinaryGroupAction.elementary
  let : FaithfulSMul G (Multiplicative V) := Representation.BinaryGroupAction.faithful ρ hf
  obtain ⟨t, ht, hgen⟩ := rank_one_generator hA hr
  have hti : IsInvolution t := ⟨fun h => by simp [h] at ht, ht ▸ pow_orderOf_eq_one t⟩
  have hs : Nat.card (commutatorAction (zpowers t) (Multiplicative V)) = 2 ^ k := by
    rw [Representation.BinaryGroupAction.commutator_card, moved_involution_eq_range ρ t ht,
      ← fixedCodim_zpowers_eq_displacement_rank, hgen, hd]
  obtain ⟨hc, hdim, hfix⟩ := primeCore_commutator_of_saturated_involution
    (W := Multiplicative V) hk hp P hP hPF t hti (hgen ▸ hm) hs
  rw [hgen] at hc hdim hfix
  refine ⟨hc, ⟨mulEquivOfPrimeCardEq hc (by simp)⟩, ?_, ?_⟩
  · rw [Representation.BinaryGroupAction.commutator_card] at hdim
    exact Nat.pow_right_injective (by decide : 1 < 2) hdim
  · have hfixed : fixedSpace ρ (⁅P,A⁆ ⊔ A) = fixedSpace ρ ⁅P,A⁆ := by
      apply le_antisymm (fixedSpace_antitone ρ le_sup_left)
      intro v hv a
      have htfix : ρ t v = v := by
        exact congrArg Multiplicative.toAdd (hfix (Multiplicative.ofAdd v) hv)
      have hAv : v ∈ fixedSpace ρ A := by
        rw [← hgen, mem_fixedSpace_zpowers_iff]
        exact htfix
      let F : Subgroup G :=
        { carrier := {g | ρ g v = v}
          one_mem' := by simp
          mul_mem' := by
            intro a b ha hb
            change ρ a v = v at ha
            change ρ b v = v at hb
            change ρ (a * b) v = v
            rw [map_mul, Module.End.mul_apply, hb, ha]
          inv_mem' := by
            intro a ha
            change ρ a v = v at ha
            change ρ a⁻¹ v = v
            have he := congrArg (fun w => ρ a⁻¹ w) ha
            simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
              map_one, Module.End.one_apply] using he.symm }
      have hDF : ⁅P,A⁆ ≤ F := fun d hd => hv ⟨d,hd⟩
      have hAF : A ≤ F := fun d hd => hAv ⟨d,hd⟩
      exact (sup_le hDF hAF) a.property
    rw [hfixed]
    have hodd : Odd (Nat.card (⁅P,A⁆ : Subgroup G)) := hc ▸ hp ▸ ⟨k, rfl⟩
    have hs := Representation.GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) hodd
    have he : Representation.RegularCyclicNormalClosure.displacementSpan
        ρ ⁅P,A⁆ ⊤ = subspaceCommutator ρ ⊤ ⁅P,A⁆ := by
      unfold Representation.RegularCyclicNormalClosure.displacementSpan subspaceCommutator
      congr 1
      ext v
      simp only [Set.mem_ofPred_eq, eq_comm]
    rw [he] at hs
    exact hs.symm

/-- D.2.13(2) in the cyclic branch, including the literal order-five
commutator and the fixed complement of its join with the actor. -/
theorem source_lemma_D_2_13_cyclic_five
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : rank A = 1) (hm : ⁅pCore 5 G, A⁆ ≠ ⊥) :
    cubicRatio ρ = 2 ∧ Nat.card (⁅pCore 5 G, A⁆ : Subgroup G) = 5 ∧
      Nonempty ((⁅pCore 5 G, A⁆ : Subgroup G) ≃* Multiplicative (ZMod 5)) ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅pCore 5 G, A⁆) = 4 ∧
      IsCompl (subspaceCommutator ρ ⊤ ⁅pCore 5 G, A⁆)
        (fixedSpace ρ (⁅pCore 5 G, A⁆ ⊔ A)) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hprime := source_lemma_D_2_13_cyclic_prime ρ hf hA hr (by decide : Odd 5) hm
  have hq : cubicRatio ρ = 2 := hprime.2.1.resolve_left (fun he => by
    have := hprime.2.2 he
    omega)
  have hd : fixedCodim ρ A = 2 := by
    have he := hA.1.2.2.2
    rw [actionRatio, hr, Nat.cast_one, div_one, hq] at he
    exact_mod_cast he
  exact ⟨hq, cyclic_actor_saturated_support ρ hf hA.1.2.1 hr (p := 5) (k := 2) (Or.inr rfl) rfl
    (pCore 5 G) pCore_isPGroup (pCore_le_fitting G 5) hm hd⟩

/-- The ratio-one support conclusion of D.2.13(3). -/
theorem source_lemma_D_2_13_cyclic_ratio_one
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : rank A = 1) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hm : ⁅pCore p G, A⁆ ≠ ⊥) (hq : cubicRatio ρ = 1) :
    p = 3 ∧ Nat.card (⁅pCore 3 G, A⁆ : Subgroup G) = 3 ∧
      Nonempty ((⁅pCore 3 G, A⁆ : Subgroup G) ≃* Multiplicative (ZMod 3)) ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅pCore 3 G, A⁆) = 2 ∧
      IsCompl (subspaceCommutator ρ ⊤ ⁅pCore 3 G, A⁆)
        (fixedSpace ρ (⁅pCore 3 G, A⁆ ⊔ A)) := by
  have hp3 := (source_lemma_D_2_13_cyclic_prime ρ hf hA hr hp hm).2.2 hq
  have hd : fixedCodim ρ A = 1 := by
    have he := hA.1.2.2.2
    rw [actionRatio, hr, Nat.cast_one, div_one, hq] at he
    exact_mod_cast he
  refine ⟨hp3, cyclic_actor_saturated_support ρ hf hA.1.2.1 hr (p := 3) (k := 1) (Or.inl rfl) rfl
    (pCore 3 G) pCore_isPGroup (pCore_le_fitting G 3) ?_ hd⟩
  simpa only [hp3] using hm

/-- The rank-one argument needed after the strict hyperplane ratio drop.
It uses only the actual action ratio, so no minimum assertion for a new
local group is needed. -/
theorem normal_prime_group_rank_one_ratio_lt_two
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : IsElementaryTwo A)
    (hr : rank A = 1) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P) (hPF : P ≤ fittingSubgroup G)
    (hm : ⁅P, A⁆ ≠ ⊥) (hlt : actionRatio ρ A < 2) :
    p = 3 ∧ fixedCodim ρ A = 1 ∧ actionRatio ρ A = 1 ∧
      Nat.card (⁅P, A⁆ : Subgroup G) = 3 ∧
      Nonempty ((⁅P, A⁆ : Subgroup G) ≃* Multiplicative (ZMod 3)) ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅P, A⁆) = 2 ∧
      IsCompl (subspaceCommutator ρ ⊤ ⁅P, A⁆) (fixedSpace ρ (⁅P, A⁆ ⊔ A)) := by
  have hd : fixedCodim ρ A = 1 := by
    rw [actionRatio, hr, Nat.cast_one, div_one] at hlt
    have hlt' : fixedCodim ρ A < 2 := by exact_mod_cast hlt
    have hpos := fixedCodim_pos_of_faithful ρ hf hA.1
    omega
  have he : actionRatio ρ A = 1 := by
    rw [actionRatio, hd, hr, Nat.cast_one, div_one]
  have hp3 : p = 3 := by
    let : Finite V := Module.finite_of_finite (ZMod 2)
    let := Representation.BinaryGroupAction.action ρ
    let : IsElementaryAbelian 2 (Multiplicative V) := Representation.BinaryGroupAction.elementary
    let : FaithfulSMul G (Multiplicative V) := Representation.BinaryGroupAction.faithful ρ hf
    obtain ⟨t, ht, hgen⟩ := rank_one_generator hA hr
    apply prime_three_of_involution_support_two (W := Multiplicative V) hp P hP t
      ⟨fun h => by simp [h] at ht, ht ▸ pow_orderOf_eq_one t⟩ (hgen ▸ hm)
    rw [Representation.BinaryGroupAction.commutator_card, moved_involution_eq_range ρ t ht,
      ← fixedCodim_zpowers_eq_displacement_rank, hgen, hd, pow_one]
  subst p
  exact ⟨rfl, hd, he, cyclic_actor_saturated_support ρ hf hA hr
    (p := 3) (k := 1) (Or.inl rfl) rfl P hP hPF hm hd⟩

end CFSG.Quasithin.ChapterD
