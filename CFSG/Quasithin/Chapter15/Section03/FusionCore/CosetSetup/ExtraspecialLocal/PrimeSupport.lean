module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.Residual

/-!
# The ordinary alternative and three-prime local subgroups

In the ordinary case, every element of order three in C_M(V) belongs to
O^{3′}(M) = Y and hence to O₂(Y), which is impossible. Conversely, the
extraspecial alternative forces a factor of three in C_M(V). The product
factorization transfers this restriction to M ∩ Mc and M ∩ H. The ordinary
E₉ quotient then identifies C_Y(Z) with C_Y(V).

Thus every clause of 15.3.49(3), including the actual E₉ isomorphism and
the prime-to-three residual, is equivalent to (4), under the earlier
15.3.7 dichotomy. This is an equivalence, not the later exclusion of its
extraspecial branch. The natural-action normalizer calculation for (5)
is a separate outstanding result.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.7, printed p.1122, and 15.3.49, printed pp.1142–1143.
-/

@[expose] public section

open Subgroup Stellmacher
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

variable {G : Type*} [Group G] [Finite G]

private theorem coprime_three_of_no_order_three
    {K : Type*} [Group K] [Finite K] (h : ∀ x : K, orderOf x ≠ 3) :
    Nat.Coprime 3 (Nat.card K) := by
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 hd
  exact h x hx

omit [Finite G] in
private theorem no_order_three_in_two_subgroup (X : Subgroup G)
    (hp : IsPGroup 2 X) {x : G} (hx : x ∈ X) (ho : orderOf x = 3) : False := by
  have hc := hp.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨x, hx⟩ : X)
  rw [← Subgroup.orderOf_coe, ho] at hc
  norm_num at hc

/-- The ordinary residual clause excludes elements of order three from C_M(V). -/
theorem centralizer_three_prime_of_ordinary
    (M Y V : Subgroup G)
    (hres : Y = (primeToResidual 3 M).map M.subtype)
    (hc : Y ⊓ centralizer (V : Set G) = Y.pCoreIn 2) :
    Nat.Coprime 3 (Nat.card (M ⊓ centralizer (V : Set G) : Subgroup G)) := by
  apply coprime_three_of_no_order_three
  intro x hx
  have ho : orderOf (x : G) = 3 := (Subgroup.orderOf_coe x).trans hx
  have hy : (x : G) ∈ Y := by
    rw [hres]
    refine ⟨⟨x, x.property.1⟩, mem_primeToResidual_of_pow (n := 1) ?_, rfl⟩
    apply Subtype.ext
    change (x : G) ^ (3 ^ 1) = 1
    rw [pow_one, ← ho, pow_orderOf_eq_one]
  exact no_order_three_in_two_subgroup (Y.pCoreIn 2) (isPGroup_pCoreIn 2 Y)
    (hc ▸ show (x : G) ∈ Y ⊓ centralizer (V : Set G) from ⟨hy, x.property.2⟩) ho

/-- A two-residual centralizer bound transfers the prime restriction to a subgroup of M. -/
theorem three_prime_of_residual_bound
    (X M V : Subgroup G) (hXM : X ≤ M)
    (hc : Nat.Coprime 3 (Nat.card (M ⊓ centralizer (V : Set G) : Subgroup G)))
    (hres : twoResidualAmbient X ≤ centralizer (V : Set G)) :
    Nat.Coprime 3 (Nat.card X) := by
  apply coprime_three_of_no_order_three
  intro x hx
  have ho : orderOf (x : G) = 3 := (Subgroup.orderOf_coe x).trans hx
  have hxC : (x : G) ∈ M ⊓ centralizer (V : Set G) :=
    ⟨hXM x.property, hres (theta_le_twoResidual X (Subgroup.subset_closure ⟨x.property, ho⟩))⟩
  have hd : 3 ∣ Nat.card (M ⊓ centralizer (V : Set G) : Subgroup G) := by
    rw [← ho, Subgroup.orderOf_coe (⟨x, hxC⟩ : (M ⊓ centralizer (V : Set G) : Subgroup G))]
    exact orderOf_dvd_natCard _
  exact Nat.prime_three.coprime_iff_not_dvd.mp hc hd

omit [Finite G] in
/-- A three-prime subgroup has trivial image in a three-group two-core quotient. -/
theorem three_prime_subgroup_le_core
    (X Y : Subgroup G) (hXY : X ≤ Y)
    (hX : Nat.Coprime 3 (Nat.card X)) (hp : IsPGroup 3 (Y ⧸ pCore 2 Y)) :
    X ≤ Y.pCoreIn 2 := by
  let f := (QuotientGroup.mk' (pCore 2 Y)).comp (inclusion hXY)
  intro x hx
  obtain ⟨n, hn⟩ := hp (f ⟨x, hx⟩)
  have ho : orderOf (f ⟨x, hx⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes (hX.pow_left n)
      (orderOf_dvd_of_pow_eq_one hn)
      ((orderOf_map_dvd f (⟨x, hx⟩ : X)).trans (orderOf_dvd_natCard _))
  have hq : (⟨x, hXY hx⟩ : Y) ∈ pCore 2 Y :=
    (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp ho)
  exact ⟨⟨x, hXY hx⟩, hq, rfl⟩

omit [Finite G] in
/-- The supplied E₉ isomorphism makes the actual quotient a three-group. -/
theorem ordinary_quotient_is_three_group (M Y V : Subgroup G)
    (h : OrdinaryCase M Y V) : IsPGroup 3 (Y ⧸ pCore 2 Y) := by
  obtain ⟨e⟩ := h.quotient_equiv
  apply IsPGroup.of_card (n := 2)
  rw [Nat.card_congr e.toEquiv]
  norm_num [Nat.card_eq_fintype_card]

omit [Finite G] in
/-- The factorization and the ordinary quotient identify C_Y(Z) with C_Y(V). -/
theorem ordinary_centralizers_eq
    (M Mc Y V Z : Subgroup G) (h : OrdinaryCase M Y V)
    (hYM : Y ≤ M) (hZV : Z ≤ V) (hMc : Mc = centralizer (Z : Set G))
    (hprime : Nat.Coprime 3 (Nat.card (M ⊓ Mc : Subgroup G))) :
    Y ⊓ centralizer (V : Set G) = Y ⊓ centralizer (Z : Set G) := by
  apply le_antisymm (inf_le_inf_left _ (centralizer_le hZV))
  rw [h.centralizer_eq]
  apply three_prime_subgroup_le_core _ Y inf_le_left
  · apply hprime.of_dvd_right
    apply card_dvd_of_le
    rw [hMc]
    exact inf_le_inf_right _ hYM
  · exact ordinary_quotient_is_three_group M Y V h

omit [Finite G] in
/-- The extraspecial alternative forces a factor of three in the order of C_M(V). -/
theorem extraspecial_centralizer_not_three_prime
    (M Y V : Subgroup G) (hYM : Y ≤ M) (h : ExtraspecialCase M Y V) :
    ¬ Nat.Coprime 3 (Nat.card (M ⊓ centralizer (V : Set G) : Subgroup G)) := by
  let := h.extraspecial
  intro hc
  apply Nat.prime_three.coprime_iff_not_dvd.mp hc
  have h3 : 3 ∣ Nat.card (Y ⊓ centralizer (V : Set G) : Subgroup G) := by
    rw [h.centralizer_eq]
    exact three_dvd_card_twoCenter Y
  exact h3.trans (card_dvd_of_le (inf_le_inf_right _ hYM))

/-- Equivalence of every clause of source 15.3.49(3) with (4), derived from the actual 15.3.7 dichotomy. -/
theorem ordinary_iff_prime_support
    (M Mc H Y V Z : Subgroup G) (T : Sylow 2 G)
    (hYM : Y ≤ M) (hZV : Z ≤ V) (hMc : Mc = centralizer (Z : Set G))
    (hM : M ≤ normalizer (V : Set G)) (hTM : (T : Subgroup G) ≤ M)
    (hH : H ≤ Mc)
    (hfactor : ∀ x ∈ M ⊓ Mc,
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (hcases : OrdinaryCase M Y V ∨ ExtraspecialCase M Y V) :
    OrdinaryConclusion M Y V Z ↔
      Nat.Coprime 3 (Nat.card (M ⊓ centralizer (V : Set G) : Subgroup G)) ∧
      Nat.Coprime 3 (Nat.card (M ⊓ H : Subgroup G)) := by
  have hrMc := (lemma_15_3_49_1 M Mc Mc V T hM hTM le_rfl hfactor).trans inf_le_right
  have hrH := (lemma_15_3_49_1 M Mc H V T hM hTM hH hfactor).trans inf_le_right
  constructor
  · rintro ⟨h, _⟩
    have hc := centralizer_three_prime_of_ordinary M Y V h.residual_eq h.centralizer_eq
    exact ⟨hc, three_prime_of_residual_bound (M ⊓ H) M V inf_le_left hc hrH⟩
  · rintro ⟨hc, _⟩
    rcases hcases with h | h
    · exact ⟨h, ordinary_centralizers_eq M Mc Y V Z h hYM hZV hMc
        (three_prime_of_residual_bound (M ⊓ Mc) M V inf_le_left hc hrMc)⟩
    · exact (extraspecial_centralizer_not_three_prime M Y V hYM h hc).elim

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

end
