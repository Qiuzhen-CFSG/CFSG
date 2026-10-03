module

public import Stellmacher.Recognition.LyonsU3Four.OrderFifteenNormalizer
public import Stellmacher.Recognition.LyonsU3Four.OrderFifteenAction
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.GroupTheory.Commutator.CentralFourSurjectivity

/-!
# Order-four fusion from the explicit automizer index

Assume Lyons's intrinsic Sylow structure and that the supplied Sylow subgroup
has automizer index fifteen. Every element of order four has Sylow centralizer
of order sixteen, and its entire central coset is fused within the Sylow.
The actual normalizer action then fuses all fifteen nonidentity central
quotient elements, giving one ambient order-four class and its rationality.

The local calculation uses an elementary replacement for the character-degree
count. The order-fifteen automorphism moves every nonidentity central element,
so some commutator row has two distinct nonidentity values. Such a row fills
the four-element center; quotient transitivity transfers this to every
noncentral element. The kernel of each row is its centralizer.

The normalizer equivalence and action are imported from the existing modules.
Simplicity is unnecessary once the automizer index is supplied. The local
results are also exposed for an explicitly supplied order-fifteen automorphism.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 1(a),(b),
p. 373.
-/

namespace Stellmacher.Recognition.LyonsU3Four

open scoped commutatorElement

private theorem commutator_eq_of_center_coset_eq
    {P : Type*} [Group P] (u v y : P)
    (he : QuotientGroup.mk' (Subgroup.center P) u =
      QuotientGroup.mk' (Subgroup.center P) v) : ⁅u,y⁆ = ⁅v,y⁆ := by
  have hz : u⁻¹ * v ∈ Subgroup.center P := QuotientGroup.eq.mp he
  have hcomm : ⁅u⁻¹ * v,y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_center_iff.mp hz y).symm
  have hv : v = u * (u⁻¹ * v) := by group
  conv_rhs => rw [hv, commutatorElement_mul_left_eq_conj_mul, hcomm]
  simp

/-- The commutator map of every order-four element fills the center. -/
public theorem order_four_commutator_surjective_of_order_fifteen
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (t : S) (ht : orderOf t = 4) :
    Function.Surjective (Subgroup.centerCommutatorHom h.center_eq_commutator.ge t) := by
  obtain ⟨a, ha⟩ : ∃ a : S, a ∉ Subgroup.center S := by
    by_contra! hall
    have htop : Subgroup.center S = ⊤ := top_unique (fun a _ => hall a)
    have hc := h.center_card
    rw [htop, Subgroup.card_top, h.card] at hc
    omega
  obtain ⟨b, hab⟩ : ∃ b : S, ⁅a,b⁆ ≠ 1 := by
    by_contra! hall
    exact ha (Subgroup.mem_center_iff.mpr fun b =>
      (commutatorElement_eq_one_iff_mul_comm.mp (hall b)).symm)
  have hm : β ⁅a,b⁆ ≠ ⁅a,b⁆ := by
    intro he
    have hz : ⁅a,b⁆ ∈ Subgroup.center S := h.center_eq_commutator.ge
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
    exact hab (congrArg Subtype.val (order_fifteen_center_fixed_eq_one S h β hβ
      ⟨⁅a,b⁆, hz⟩ (Subtype.ext he)))
  obtain ⟨x, y, z, hy, hz, hyz⟩ := Subgroup.exists_two_commutators_of_aut_moves β a b hm
  have hx : x ∉ Subgroup.center S := by
    intro hxc
    exact hy (commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hxc y).symm)
  have htZ := (order_four_iff_not_mem_center S h t).mp ht
  let Z := Subgroup.center S
  obtain ⟨n, hn⟩ := order_fifteen_quotient_transitive S h β hβ
    (QuotientGroup.mk' Z x) (QuotientGroup.mk' Z t)
    (fun he => hx ((QuotientGroup.eq_one_iff x).mp he))
    (fun he => htZ ((QuotientGroup.eq_one_iff t).mp he))
  let γ := β ^ n
  have hqt : QuotientGroup.mk' Z (γ x) = QuotientGroup.mk' Z t := by
    simpa only [γ, Z, ← map_zpow, Subgroup.quotientAut_apply_mk] using hn
  have hval (w : S) : ⁅t,γ w⁆ = γ ⁅x,w⁆ :=
    (commutator_eq_of_center_coset_eq (γ x) t (γ w) hqt).symm.trans
      (map_commutatorElement γ x w).symm
  apply Subgroup.centerCommutatorHom_surjective_of_two_values
    h.center_eq_commutator.ge h.center_card t (γ y) (γ z)
  · rw [hval]
    exact fun he => hy (γ.injective (he.trans γ.map_one.symm))
  · rw [hval]
    exact fun he => hz (γ.injective (he.trans γ.map_one.symm))
  · rw [hval, hval]
    exact fun he => hyz (γ.injective he)

/-- The centralizer within the supplied Sylow has order sixteen. -/
public theorem order_four_centralizer_card_of_order_fifteen
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (t : S) (ht : orderOf t = 4) :
    Nat.card (Subgroup.centralizer ({t} : Set S)) = 16 := by
  have hsurj := order_four_commutator_surjective_of_order_fifteen S h β hβ t ht
  have hi : (Subgroup.centralizer ({t} : Set S)).index = 4 := by
    rw [← Subgroup.centerCommutatorHom_ker h.center_eq_commutator.ge t,
      Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, h.center_card]
  have hc := (Subgroup.centralizer ({t} : Set S)).index_mul_card
  rw [hi, h.card] at hc
  omega

/-- Every member of the central coset of an order-four element is conjugate
 to it within the Sylow subgroup. -/
public theorem order_four_center_coset_isConj_of_order_fifteen
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (t : S) (ht : orderOf t = 4) (z : Subgroup.center S) : IsConj t (t * z) := by
  obtain ⟨y, hy⟩ := order_four_commutator_surjective_of_order_fifteen S h β hβ t ht z⁻¹
  have he : ⁅t,y⁆ = (z : S)⁻¹ := congrArg Subtype.val hy
  have hy' : ⁅y,t⁆ = (z : S) := by rw [← commutatorElement_inv, he, inv_inv]
  apply isConj_iff.mpr
  refine ⟨y, ?_⟩
  change MulAut.conj y t = t * z
  rw [conj_eq_commutatorElement_mul, hy']
  exact (Subgroup.mem_center_iff.mp z.property t).symm

end Stellmacher.Recognition.LyonsU3Four

namespace Stellmacher.Recognition.LyonsU3Four

/-- The order-fifteen action can be represented by an actual element of the
normalizer of the supplied Sylow subgroup. -/
public theorem exists_order_fifteen_normalizer_action
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (h : SylowStructure S) (h15 : automizerIndex S = 15) :
    ∃ n : Subgroup.normalizer (S : Set G),
      orderOf ((S : Subgroup G).normalizerMonoidHom n) = 15 := by
  obtain ⟨β, α, hβ, hα, e, he⟩ := exists_orderFifteen_normalizer_equiv S h h15
  let c : Multiplicative (ZMod 15) := Multiplicative.ofAdd 1
  let O := pPrimeCore 2 (Subgroup.normalizer (S : Set G))
  let q := QuotientGroup.mk' O
  obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective O (e.symm (SemidirectProduct.inr c))
  have hen : e (q n) = SemidirectProduct.inr c := by
    rw [hn, e.apply_symm_apply]
  have hnβ : (S : Subgroup G).normalizerMonoidHom n = β := by
    apply MulEquiv.ext
    intro s
    apply sylowNormalizerQuotientMap_injective S h
    apply e.injective
    have hf : sylowNormalizerQuotientMap S
        ((S : Subgroup G).normalizerMonoidHom n s) =
        q n * sylowNormalizerQuotientMap S s * (q n)⁻¹ := by
      change q (n * Subgroup.inclusion (S : Subgroup G).le_normalizer s * n⁻¹) = _
      simp only [map_mul, map_inv]
      rfl
    rw [hf, map_mul, map_mul, map_inv, hen, he, he]
    simpa only [map_inv] using (SemidirectProduct.inl_aut (φ := α) c s).symm.trans
      (congrArg SemidirectProduct.inl (DFunLike.congr_fun hα s))
  exact ⟨n, by rw [hnβ]; exact hβ⟩

/-- Coset fusion and the actual automizer imply fusion of the order-four
Sylow elements in the ambient group. -/
private theorem sylow_order_four_isConj_of_center_coset_fusion
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (h : SylowStructure S) (h15 : automizerIndex S = 15)
    (hcoset : ∀ t : S, orderOf t = 4 →
      ∀ z : Subgroup.center S, IsConj t (t * z))
    (x y : S) (hx : orderOf x = 4) (hy : orderOf y = 4) :
    IsConj (x : G) (y : G) := by
  obtain ⟨n, hn⟩ := exists_order_fifteen_normalizer_action S h h15
  let β := (S : Subgroup G).normalizerMonoidHom n
  let Z := Subgroup.center S
  have hxZ := (order_four_iff_not_mem_center S h x).mp hx
  have hyZ := (order_four_iff_not_mem_center S h y).mp hy
  obtain ⟨k, hk⟩ := order_fifteen_quotient_transitive S h β hn
    (QuotientGroup.mk' Z x) (QuotientGroup.mk' Z y)
    (fun he => hxZ ((QuotientGroup.eq_one_iff x).mp he))
    (fun he => hyZ ((QuotientGroup.eq_one_iff y).mp he))
  let u := (β ^ k) x
  have hquot : QuotientGroup.mk' Z u = QuotientGroup.mk' Z y := by
    simpa only [u, Z, ← map_zpow, Subgroup.quotientAut_apply_mk] using hk
  have hz : u⁻¹ * y ∈ Z := QuotientGroup.eq.mp hquot
  have hu : orderOf u = 4 := ((β ^ k).orderOf_eq x).trans hx
  have huy : IsConj u y := by
    simpa only [mul_inv_cancel_left] using hcoset u hu ⟨u⁻¹ * y, hz⟩
  have hxu : IsConj (x : G) (u : G) := by
    apply isConj_iff.mpr
    refine ⟨((n ^ k : Subgroup.normalizer (S : Set G)) : G), ?_⟩
    change _ = (((((S : Subgroup G).normalizerMonoidHom n) ^ k) x : S) : G)
    rw [← map_zpow]
    rfl
  exact hxu.trans ((S : Subgroup G).subtype.map_isConj huy)

private theorem orderOf_eq_of_isConj {G : Type*} [Group G] {x y : G}
    (hxy : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
  exact ((MulAut.conj g).orderOf_eq x).symm

/-- Sylow conjugacy extends the coset-fusion calculation to every ambient
order-four element. -/
private theorem order_four_isConj_of_center_coset_fusion
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (h : SylowStructure S) (h15 : automizerIndex S = 15)
    (hcoset : ∀ t : S, orderOf t = 4 →
      ∀ z : Subgroup.center S, IsConj t (t * z))
    {x y : G} (hx : orderOf x = 4) (hy : orderOf y = 4) : IsConj x y := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hxu⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 2) hx
  obtain ⟨v, hyv⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 2) hy
  have hu : orderOf u = 4 := by
    rw [← Subgroup.orderOf_coe u, ← orderOf_eq_of_isConj hxu, hx]
  have hv : orderOf v = 4 := by
    rw [← Subgroup.orderOf_coe v, ← orderOf_eq_of_isConj hyv, hy]
  exact hxu.trans ((sylow_order_four_isConj_of_center_coset_fusion
    S h h15 hcoset u v hu hv).trans hyv.symm)

end Stellmacher.Recognition.LyonsU3Four

namespace Stellmacher.Recognition.LyonsU3Four

/-- Under the explicit automizer-index hypothesis, each order-four Sylow
 element has centralizer of order sixteen in that Sylow subgroup. -/
public theorem order_four_centralizer_card_of_automizer_eq_fifteen
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (h : SylowStructure S) (h15 : automizerIndex S = 15)
    (t : S) (ht : orderOf t = 4) :
    Nat.card (Subgroup.centralizer ({t} : Set S)) = 16 := by
  obtain ⟨n, hn⟩ := exists_order_fifteen_normalizer_action S h h15
  exact order_four_centralizer_card_of_order_fifteen S h _ hn t ht

/-- The entire central coset of an order-four element forms one conjugacy
 class within the supplied Sylow subgroup. -/
public theorem order_four_center_coset_isConj_of_automizer_eq_fifteen
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (h : SylowStructure S) (h15 : automizerIndex S = 15)
    (t : S) (ht : orderOf t = 4) (z : Subgroup.center S) :
    IsConj t (t * z) := by
  obtain ⟨n, hn⟩ := exists_order_fifteen_normalizer_action S h h15
  exact order_four_center_coset_isConj_of_order_fifteen S h _ hn t ht z

/-- There is one ambient conjugacy class of elements of order four. -/
public theorem order_four_isConj_of_automizer_eq_fifteen
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (h : SylowStructure S) (h15 : automizerIndex S = 15)
    {x y : G} (hx : orderOf x = 4) (hy : orderOf y = 4) : IsConj x y :=
  order_four_isConj_of_center_coset_fusion S h h15
    (order_four_center_coset_isConj_of_automizer_eq_fifteen S h h15) hx hy

/-- The ambient class of order-four elements is rational. -/
public theorem order_four_isConj_pow_of_automizer_eq_fifteen
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (h : SylowStructure S) (h15 : automizerIndex S = 15)
    {x : G} (hx : orderOf x = 4) (m : ℕ) (hm : m.Coprime 4) :
    IsConj x (x ^ m) := by
  apply order_four_isConj_of_automizer_eq_fifteen S h h15 hx
  exact (Nat.Coprime.orderOf_pow (hx ▸ hm.symm)).trans hx

end Stellmacher.Recognition.LyonsU3Four
