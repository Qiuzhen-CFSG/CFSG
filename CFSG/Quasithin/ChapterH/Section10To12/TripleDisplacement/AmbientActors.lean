module

public import CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement.SylowStructure
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage
public import Theory.Mathieu.M22.Properties.CubicInverters
public import Theory.Mathieu.M22.Properties.ElevenFiveFrobenius

public import CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement.AmbientActors.FrobeniusLift

/-!
# Ambient actors for a genuine triple cover of M₂₂

For a finite group with F*(G) = L and the actual central quotient L/Z(L) ≃ M₂₂,
self-centralization and faithful descent embed G/L in Out(M₂₂). The faithful
concrete design action bounds that outer quotient by two. Consequently all
odd-prime-order elements of G belong to L.

Every ambient involution induces an involution on the actual M₂₂ quotient:
the kernel centralizes L and lies in its cubic center. An inverted cubic
quotient element lifts by taking a suitable power of x a(x)⁻¹. Exhaustive
Sylow coverage in the native M₂₂ automorphism group supplies this quotient
element for every ambient involution, including all permitted outer extensions.

The checked native eleven-by-five configuration lifts through the central
cubic kernel. Thus every order-five element of L normalizes an actual subgroup
of order eleven, its nonidentity powers act fixed-point-freely there, and their
join has order 55. Both witness theorems have no additional model premises.

Source: Aschbacher–Smith H.12.1, printed pp.393–394, combined manuscript
of 1 March 2004. No split cover or class labels replace the genuine groups.
-/

public section

open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement.AmbientActors
private theorem m22_outer_card_dvd_two : Nat.card (MulAut.Outer M22) ∣ 2 := by
  let N := M22.subgroupOf m22DesignAut
  let : N.Normal := M22_normal_in_m22DesignAut
  have hle : N ≤ (MulAut.innerSubgroup M22).comap m22DesignAutToAut := by
    intro g hg
    refine ⟨⟨g.val, hg⟩, ?_⟩
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [m22DesignAutToAut_apply_perm]
    rfl
  let q : (m22DesignAut ⧸ N) →* MulAut.Outer M22 :=
    QuotientGroup.map N (MulAut.innerSubgroup M22) m22DesignAutToAut hle
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup M22) x
    obtain ⟨g, rfl⟩ := m22DesignAutToAut_surjective a
    exact ⟨QuotientGroup.mk' N g, rfl⟩
  have htwo : Nat.card (m22DesignAut ⧸ N) = 2 := by
    rw [← N.index_eq_card]
    have heq : N = m22EvenDesignAut := by
      ext g
      simp [N, M22, m22EvenDesignAut]
    rw [heq, m22EvenDesignAut_index]
  exact htwo ▸ card_dvd_of_surjective q hq

variable {G : Type*} [Group G] [Finite G]
/-- The only possible ambient extension has index at most two. -/
theorem index_dvd_two (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L) : L.index ∣ 2 := by
  subst L
  let L := generalizedFitting G
  let : IsQuasisimple L := hL.quasisimple
  obtain ⟨e⟩ := hL.centralQuotient
  have hinj : Function.Injective (MulAut.outerAction L) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    change (QuotientGroup.map _ _ _ _).ker = ⊥
    rw [QuotientGroup.ker_map, MulAut.conjNormal_comap_innerSubgroup,
      sup_eq_left.mpr ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le,
      QuotientGroup.map_mk'_self]
  rw [Subgroup.index_eq_card]
  exact (card_dvd_of_injective (MulAut.outerAction L) hinj).trans
    ((card_dvd_of_injective (MulAut.centralQuotientOuter e)
      (MulAut.centralQuotientOuter_injective e)).trans m22_outer_card_dvd_two)

/-- Every odd-prime-order ambient element belongs to the triple cover. -/
theorem odd_prime_mem (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (x : G) (hx : orderOf x = p) : x ∈ L := by
  have hi := index_dvd_two L hL hF
  let : L.Normal := hF ▸ inferInstance
  let q := QuotientGroup.mk' L
  have htwo : orderOf (q x) ∣ 2 := (orderOf_dvd_natCard (q x)).trans
    (L.index_eq_card ▸ hi)
  have hp' : orderOf (q x) ∣ p := hx ▸ orderOf_map_dvd q x
  have he : orderOf (q x) = 1 := Nat.eq_one_of_dvd_coprimes
    ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) hp' htwo
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp he)

/-- The source prime spectrum also holds for all odd-prime ambient actors. -/
theorem ambient_odd_prime_order_cases (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (x : G) (hx : orderOf x = p) : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
  have hm := odd_prime_mem L hL hF hp hp2 x hx
  apply odd_prime_order_cases hL hp hp2 (⟨x, hm⟩ : L)
  exact (orderOf_injective L.subtype L.subtype_injective _).symm.trans hx

/-- Inverting a cubic element of an equivariant quotient supplies one upstairs. -/
theorem lift_inverted_three {E B : Type*} [Group E] [Finite E] [Group B]
    (f : E →* B) (hf : Function.Surjective f) (a : MulAut E) (b : MulAut B)
    (ha : a ^ 2 = 1) (hab : ∀ x, f (a x) = b (f x))
    (v : B) (hv : orderOf v = 3) (hbv : b v = v⁻¹) :
    ∃ y : E, orderOf y = 3 ∧ a y = y⁻¹ := by
  let : Finite B := Finite.of_surjective f hf
  obtain ⟨x, hx⟩ := hf v
  let d := x * (a x)⁻¹
  have hfd : f d = v ^ 2 := by simp [d, hab, hx, hbv, pow_two]
  have hd3 : 3 ∣ orderOf d := by
    have h := orderOf_map_dvd f d
    rwa [hfd, orderOf_pow, hv, show Nat.gcd 3 2 = 1 by decide] at h
  have haa : a (a x) = x := by
    have h := DFunLike.congr_fun ha x
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
  have had : a d = d⁻¹ := by simp [d, map_mul, map_inv, haa]
  refine ⟨d ^ (orderOf d / 3), orderOf_pow_orderOf_div (orderOf_pos d).ne' hd3, ?_⟩
  rw [map_pow, had, inv_pow]

/-- Every ambient involution acts as an actual involution on the central quotient. -/
theorem quotient_action_order_two (L : Subgroup G) [L.Normal]
    (hL : IsTripleM22 L) (hF : generalizedFitting G = L)
    (e : L ⧸ center L ≃* M22) (t : G) (ht : orderOf t = 2) :
    orderOf (MulAut.centralQuotientAction e (MulAut.conjNormal t)) = 2 := by
  let : IsQuasisimple L := hL.quasisimple
  let a : MulAut L := MulAut.conjNormal t
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have ha2 : a ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  apply orderOf_eq_prime (by rw [← map_pow, ha2, map_one])
  intro h
  have ha : a = 1 := MulAut.centralQuotientAction_injective e
    (h.trans (map_one _).symm)
  have hc : t ∈ centralizer (L : Set G) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer]
    exact ha
  have htL : t ∈ L := by
    rw [← hF] at hc ⊢
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le hc
  have hz : (⟨t, htL⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_iff.mp hc x x.property)
  have hd := orderOf_dvd_natCard (⟨⟨t, htL⟩, hz⟩ : center L)
  rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe] at hd
  change orderOf t ∣ Nat.card (center L) at hd
  rw [ht, hL.center_card] at hd
  norm_num at hd

/-- Reduction of all ambient involutions to the genuine M₂₂ automorphism calculation. -/
theorem exists_inverted_three_of_model
    (hmodel : ∀ b : MulAut M22, orderOf b = 2 →
      ∃ v : M22, orderOf v = 3 ∧ b v = v⁻¹)
    (L : Subgroup G) (hL : IsTripleM22 L) (hF : generalizedFitting G = L)
    (t : G) (ht : orderOf t = 2) :
    ∃ y : G, y ∈ L ∧ orderOf y = 3 ∧ t * y * t⁻¹ = y⁻¹ := by
  let : L.Normal := hF ▸ inferInstance
  obtain ⟨e⟩ := hL.centralQuotient
  let a : MulAut L := MulAut.conjNormal t
  let b := MulAut.centralQuotientAction e a
  obtain ⟨v, hv, hbv⟩ := hmodel b (quotient_action_order_two L hL hF e t ht)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have ha2 : a ^ 2 = 1 := by
    rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  obtain ⟨y, hy, hay⟩ := lift_inverted_three f
    (e.surjective.comp (QuotientGroup.mk'_surjective (center L))) a b ha2
    (fun x => (MulAut.centralQuotientAction_apply e a x).symm) v hv hbv
  refine ⟨y, y.property, ?_, ?_⟩
  · simpa only [Subgroup.orderOf_coe] using hy
  · exact congrArg Subtype.val hay

/-- Every ambient involution inverts an element of order three in the genuine
triple cover, including when the involution lies outside the cover. -/
theorem exists_inverted_three (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L) (t : G) (ht : orderOf t = 2) :
    ∃ y : G, y ∈ L ∧ orderOf y = 3 ∧ t * y * t⁻¹ = y⁻¹ :=
  exists_inverted_three_of_model m22_exists_inverted_three L hL hF t ht

/-- Every order-five element of the genuine triple cover lies in a Frobenius
subgroup of order 55 with an actual order-eleven kernel. -/
theorem exists_eleven_five {L : Type*} [Group L] [Finite L] (hL : IsTripleM22 L)
    (y : L) (hy : orderOf y = 5) :
    ∃ K : Subgroup L, Nat.card K = 11 ∧
      zpowers y ≤ normalizer (K : Set L) ∧
      (∀ a ∈ zpowers y, a ≠ 1 → ∀ k ∈ K, a * k * a⁻¹ = k → k = 1) ∧
      Nat.card (K ⊔ zpowers y : Subgroup L) = 55 :=
  exists_eleven_five_of_model m22_exists_eleven_five hL y hy

end CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement.AmbientActors
