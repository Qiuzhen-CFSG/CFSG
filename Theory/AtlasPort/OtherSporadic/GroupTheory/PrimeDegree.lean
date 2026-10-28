/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/PrimeDegree.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.Linarith

/-!
# PrimeDegree

A faithful multiply transitive action of prime degree gives a simplicity criterion.
Sylow counts and normalizer bounds exclude proper nontrivial normal subgroups.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/PrimeDegree.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

/-! Supporting lemmas for the prime-degree simplicity criterion. -/

open scoped Pointwise

namespace Atlas.GroupTheory
set_option linter.unusedVariables false in
/-- Numerical conclusion from the Sylow congruence and the degree bound. -/
theorem prime_degree_normalizer_arithmetic {p r m s a : ℕ}
    (hp : 0 < p) (hrpos : 0 < r) (hr : r < p) (hs : s < p)
    (hm : m % p = 1) (ha : a % p = 1)
    (he : p * s * a = p * r * m) : s = r ∧ a = m := by
  have he' : s * a = r * m := by nlinarith [hp]
  have hemod := congrArg (fun t : ℕ => t % p) he'
  simp only [Nat.mul_mod, ha, hm, Nat.mul_one,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hr] at hemod
  refine ⟨hemod, ?_⟩
  nlinarith


variable {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]

/-- Sylow order when the prime occurs exactly once in the group order. -/
theorem sylow_card_prime [Finite G] (p : ℕ) [hp : Fact p.Prime]
    (hd : p ∣ Nat.card G) (hsq : ¬ p ^ 2 ∣ Nat.card G) (P : Sylow p G) :
    Nat.card P = p := by
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hdP := P.dvd_card_of_dvd_card hd
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, pow_zero] at hk
    rw [hk] at hdP
    exact hp.out.not_dvd_one hdP
  have hk2 : ¬ 2 ≤ k := by
    intro h
    apply hsq
    exact (hk ▸ (pow_dvd_pow p h)).trans P.toSubgroup.card_subgroup_dvd_card
  have : k = 1 := by omega
  simpa [this] using hk

/-- A nonidentity element generates any prime-order subgroup containing it. -/
theorem prime_subgroup_eq_zpowers [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Subgroup G) (hP : Nat.card P = p) (g : G) (hg : g ∈ P) (hne : g ≠ 1) :
    Subgroup.zpowers g = P := by
  have hne' : (⟨g,hg⟩ : P) ≠ 1 := fun h => hne (congrArg Subtype.val h)
  have ho := orderOf_eq_card_of_zpowers_eq_top (zpowers_eq_top_of_prime_card hP hne')
  have hc : Nat.card (Subgroup.zpowers g) = Nat.card P := by
    rw [Nat.card_zpowers, ← ho]
    exact (orderOf_injective P.subtype P.subtype_injective ⟨g,hg⟩)
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg) hc.symm.le

/-- An element of order p in a faithful action of degree p has no fixed point. -/
theorem prime_order_fixedPointFree [Finite X] (p : ℕ) [hp : Fact p.Prime]
    (hX : Nat.card X = p) (z : G) (hz : orderOf z = p) (x : X) : z • x ≠ x := by
  classical
  let := Fintype.ofFinite X
  let σ := MulAction.toPermHom G X z
  have ho : orderOf σ = Fintype.card X := by
    rw [orderOf_injective (MulAction.toPermHom G X) MulAction.toPerm_injective, hz,
      ← Nat.card_eq_fintype_card, hX]
  have hc : σ.IsCycle := Equiv.Perm.isCycle_of_prime_order''
    (by simpa only [← Nat.card_eq_fintype_card, hX] using hp.out) ho
  have hs : σ.support = Finset.univ := Finset.eq_univ_of_card _
    (hc.orderOf.symm.trans ho)
  have hx : x ∈ σ.support := by rw [hs]; exact Finset.mem_univ x
  exact Equiv.Perm.mem_support.mp hx

/-- A subgroup of order p acts regularly in a faithful action of degree p. -/
theorem prime_subgroup_pretransitive [Finite X] (p : ℕ) [Fact p.Prime]
    (hX : Nat.card X = p) (P : Subgroup G) (hP : Nat.card P = p) :
    MulAction.IsPretransitive P X := by
  have : Finite P := Nat.finite_of_card_ne_zero (hP ▸ (Fact.out : p.Prime).ne_zero)
  have hi (a : X) : Function.Injective (fun g : P => g • a) := by
    intro g h he
    change g • a = h • a at he
    by_contra hne
    have hne' : g⁻¹ * h ≠ 1 := fun hh => hne (inv_mul_eq_one.mp hh)
    have hgen := zpowers_eq_top_of_prime_card hP hne'
    have hord : orderOf (g⁻¹ * h) = p :=
      (orderOf_eq_card_of_zpowers_eq_top hgen).trans hP
    have hf := prime_order_fixedPointFree p hX (↑(g⁻¹ * h) : G)
      ((orderOf_injective P.subtype P.subtype_injective _).trans hord) a
    apply hf
    change (g⁻¹ * h) • a = a
    rw [mul_smul, ← he, inv_smul_smul]
  constructor
  intro a b
  exact ((hi a).bijective_of_nat_card_le (by rw [hX, hP])).2 b

/-- A normalizing element is determined by its conjugation on a transitive
subgroup and its value at one point. -/
theorem normalizer_action_injective (P : Subgroup G)
    [MulAction.IsPretransitive P X] (a : X) :
    Function.Injective (fun g : (Subgroup.normalizer (P : Set G)) =>
      (P.normalizerMonoidHom g, (g : G) • a)) := by
  intro g h he
  have hconj := congrArg Prod.fst he
  have hpoint := congrArg Prod.snd he
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := X)
  intro x
  obtain ⟨u, rfl⟩ := MulAction.exists_smul_eq P a x
  have hu : (g : G) * (u : G) * (g : G)⁻¹ =
      (h : G) * (u : G) * (h : G)⁻¹ :=
    congrArg (fun e : MulAut P => (e u : G)) hconj
  change (g : G) • ((u : G) • a) = (h : G) • ((u : G) • a)
  calc
    (g : G) • ((u : G) • a) =
        ((g : G) * (u : G) * (g : G)⁻¹) • ((g : G) • a) := by simp [mul_smul]
    _ = ((h : G) * (u : G) * (h : G)⁻¹) • ((h : G) • a) := by rw [hu]; exact congrArg _ hpoint
    _ = (h : G) • ((u : G) • a) := by simp [mul_smul]

/-- The normalizer of a transitive prime-order subgroup has order at most p(p−1). -/
theorem prime_normalizer_card_bound [Finite G] [Finite X]
    (P : Subgroup G) [MulAction.IsPretransitive P X] (a : X)
    (p : ℕ) [hp : Fact p.Prime] (hP : Nat.card P = p) (hX : Nat.card X = p) :
    Nat.card (Subgroup.normalizer (P : Set G)) ≤ p * (p - 1) := by
  have : IsCyclic P := isCyclic_of_prime_card hP
  have hc := Nat.card_le_card_of_injective _ (normalizer_action_injective P a)
  rw [Nat.card_prod, IsCyclic.card_mulAut, hP, hX, Nat.totient_prime hp.out, mul_comm] at hc
  exact hc

/-- Nonidentity elements of distinct prime-order Sylow subgroups are disjoint. -/
theorem sylow_nonidentity_injective [Finite G] (p : ℕ) [Fact p.Prime]
    (hP : ∀ P : Sylow p G, Nat.card P = p) :
    Function.Injective (fun u : (Σ P : Sylow p G, {g : P // g ≠ 1}) => (u.2.val : G)) := by
  rintro ⟨P,g⟩ ⟨Q,h⟩ he
  change (g.val : G) = (h.val : G) at he
  have hg : (g.val : G) ≠ 1 := fun h => g.property (Subtype.ext h)
  have hPQ : P = Q := by
    apply Sylow.ext
    exact (prime_subgroup_eq_zpowers (G := G) p P (hP P) (g.val : G) g.val.property hg).symm.trans
      (prime_subgroup_eq_zpowers (G := G) p Q (hP Q) (g.val : G) (he.symm ▸ h.val.property) hg)
  subst Q
  have hgh : g = h := Subtype.ext (Subtype.ext he)
  subst h
  rfl

/-- The union of the nonidentity Sylow elements has size a(p−1). -/
theorem sylow_nonidentity_card [Finite G] (p : ℕ) [Fact p.Prime]
    (hP : ∀ P : Sylow p G, Nat.card P = p) :
    Nat.card (Σ P : Sylow p G, {g : P // g ≠ 1}) = Nat.card (Sylow p G) * (p - 1) := by
  classical
  let := Fintype.ofFinite (Sylow p G)
  let (P : Sylow p G) := Fintype.ofFinite P
  have hc (P : Sylow p G) : Nat.card {g : P // g ≠ 1} = p - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp only [Fintype.card_unique, ← Nat.card_eq_fintype_card]
    change Nat.card P - 1 = p - 1
    rw [hP P]
  rw [Nat.card_sigma]
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]


/-- Chapman’s counting argument: a transitive degree-p group whose order is p
 times its Sylow count has just one Sylow p-subgroup. -/
theorem sylow_count_one_of_card [Finite G] [Finite X]
    [MulAction.IsPretransitive G X] (p : ℕ) [hp : Fact p.Prime]
    (hX : Nat.card X = p) (hP : ∀ P : Sylow p G, Nat.card P = p)
    (hG : Nat.card G = p * Nat.card (Sylow p G)) : Nat.card (Sylow p G) = 1 := by
  classical
  let f : (Σ P : Sylow p G, {g : P // g ≠ 1}) → G := fun u => u.2.val
  let D : Set G := Set.range f
  have hD : D.ncard = Nat.card (Sylow p G) * (p - 1) := by
    change Nat.card (Set.range f) = _
    rw [Nat.card_range_of_injective (sylow_nonidentity_injective p hP)]
    exact sylow_nonidentity_card p hP
  have hDc : Dᶜ.ncard = Nat.card (Sylow p G) := by
    have h := Set.ncard_add_ncard_compl D
    rw [hD, hG] at h
    have := hp.out.one_lt
    have : p - 1 + 1 = p := by omega
    nlinarith
  have hsubset (x : X) : (MulAction.stabilizer G x : Set G) ⊆ Dᶜ := by
    intro g hg hgd
    obtain ⟨⟨P,u⟩, rfl⟩ := hgd
    have hne : (u.val : G) ≠ 1 := fun h => u.property (Subtype.ext h)
    have hzp := prime_subgroup_eq_zpowers (G := G) p P (hP P) u.val u.val.property hne
    have ho : orderOf (u.val : G) = p := by
      rw [← Nat.card_zpowers, hzp]
      exact hP P
    exact prime_order_fixedPointFree (G := G) p hX (u.val : G) ho x hg
  have hstab (x : X) : Nat.card (MulAction.stabilizer G x) = Nat.card (Sylow p G) := by
    have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G x)
    rw [Nat.card_prod] at hc
    have ho : Nat.card (MulAction.orbit G x) = p := by
      rw [MulAction.orbit_eq_univ]
      simpa using hX
    rw [ho, hG] at hc
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos hc
  have heq (x : X) : (MulAction.stabilizer G x : Set G) = Dᶜ :=
    Set.eq_of_subset_of_ncard_le (hsubset x) (by rw [hDc]; exact (hstab x).ge)
  have : Nonempty X := (Nat.card_pos_iff.mp (hX ▸ hp.out.pos)).1
  let x : X := Classical.choice inferInstance
  have hbot : MulAction.stabilizer G x = ⊥ := by
    apply le_antisymm _ bot_le
    intro g hg
    rw [Subgroup.mem_bot]
    apply eq_of_smul_eq_smul (α := X)
    intro y
    have hy : g ∈ MulAction.stabilizer G y := by
      change g ∈ (MulAction.stabilizer G y : Set G)
      rw [heq y, ← heq x]
      exact hg
    exact hy.trans (one_smul G y).symm
  have hc := hstab x
  rw [hbot, Subgroup.card_bot] at hc
  exact hc.symm


/-- Restriction along the actual inclusion gives a bijection of Sylow sets
when every ambient Sylow subgroup is contained in the subgroup. -/
theorem sylow_card_subgroup_of_all_le [Finite G] (p : ℕ) [Fact p.Prime]
    (N : Subgroup G) (hN : ∀ P : Sylow p G, P ≤ N) :
    Nat.card (Sylow p G) = Nat.card (Sylow p N) := by
  apply Nat.card_eq_of_bijective (fun P : Sylow p G => P.subtype (hN P))
  constructor
  · intro P Q h
    exact Sylow.subtype_injective h
  · intro Q
    obtain ⟨P,hP⟩ := Q.exists_comap_subtype_eq
    refine ⟨P, ?_⟩
    apply Sylow.ext
    exact hP


/-- Normality puts every ambient Sylow subgroup in N when p divides |N|
and p occurs just once in |G|. -/
theorem sylow_le_normal_of_prime_dvd [Finite G] (p : ℕ) [Fact p.Prime]
    (hsq : ¬ p ^ 2 ∣ Nat.card G) (N : Subgroup G) [N.Normal]
    (hdN : p ∣ Nat.card N) (R : Sylow p G) : R ≤ N := by
  have hdG : p ∣ Nat.card G := hdN.trans N.card_subgroup_dvd_card
  have hsqN : ¬ p ^ 2 ∣ Nat.card N := fun h => hsq (h.trans N.card_subgroup_dvd_card)
  let Q : Sylow p N := Classical.choice inferInstance
  have hQ := sylow_card_prime p hdN hsqN Q
  obtain ⟨P,hP⟩ := Q.exists_comap_subtype_eq
  have hle : (Q : Subgroup N).map N.subtype ≤ (P : Subgroup G) := by
    apply Subgroup.map_le_iff_le_comap.mpr
    exact hP.symm.le
  have heq : (Q : Subgroup N).map N.subtype = (P : Subgroup G) := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Subgroup.card_map_of_injective N.subtype_injective, sylow_card_prime p hdG hsq P]
    exact hQ.ge
  have hPN : P ≤ N := heq ▸ Subgroup.map_subtype_le (Q : Subgroup N)
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P R
  intro z hz
  change z ∈ MulAut.conj g • (P : Set G) at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact Subgroup.Normal.conj_mem inferInstance y (hPN hy) g


/-- Orbit–stabilizer and the subgroup index in its normalizer. -/
theorem sylow_normalizer_factor [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (hP : Nat.card P = p) :
    ∃ s : ℕ, 0 < s ∧ Nat.card (Subgroup.normalizer (P : Set G)) = p * s ∧
      Nat.card G = p * s * Nat.card (Sylow p G) := by
  let K := Subgroup.normalizer (P : Set G)
  let Q := (P : Subgroup G).subgroupOf K
  have hcQ : Nat.card Q = p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show (P : Subgroup G) ≤ K from
      Subgroup.le_normalizer)).toEquiv).trans hP
  refine ⟨Q.index, Nat.pos_of_ne_zero Q.index_ne_zero_of_finite, ?_, ?_⟩
  · have h := Q.card_mul_index
    rw [hcQ] at h
    exact h.symm
  · have h := K.card_mul_index
    have hQ := Q.card_mul_index
    rw [hcQ] at hQ
    rw [← hQ, ← P.card_eq_index_normalizer] at h
    exact h.symm


/-- Chapman's prime-degree simplicity criterion (American Mathematical Monthly
102 (1995), 544–545), for a faithful transitive action on the actual set X. -/
theorem prime_degree_simple [Finite G] [Finite X] [MulAction.IsPretransitive G X]
    (p r m : ℕ) [hp : Fact p.Prime] [hr : Fact r.Prime]
    (hrp : r < p) (hm : 1 < m) (hmcong : m % p = 1)
    (hX : Nat.card X = p) (hG : Nat.card G = p * r * m) : IsSimpleGroup G := by
  have hpd : p ∣ Nat.card G := by rw [hG]; exact dvd_mul_of_dvd_left (dvd_mul_right p r) m
  have hsq : ¬ p ^ 2 ∣ Nat.card G := by
    rw [hG, pow_two, mul_assoc, Nat.mul_dvd_mul_iff_left hp.out.pos,
      hp.out.dvd_mul]
    intro h
    rcases h with h | h
    · exact (Nat.not_dvd_of_pos_of_lt hr.out.pos hrp) h
    · have hzero := Nat.mod_eq_zero_of_dvd h
      omega
  have hcP := sylow_card_prime (G := G) p hpd hsq
  let P : Sylow p G := Classical.choice inferInstance
  have : MulAction.IsPretransitive P X := prime_subgroup_pretransitive (G := G) p hX (P : Subgroup G) (hcP P)
  have : Nonempty X := (Nat.card_pos_iff.mp (hX ▸ hp.out.pos)).1
  let a : X := Classical.choice inferInstance
  obtain ⟨s, hspos, hnorm, hfactor⟩ := sylow_normalizer_factor p P (hcP P)
  have hbound := prime_normalizer_card_bound (G := G) P a p (hcP P) hX
  change Nat.card (Subgroup.normalizer (P : Set G)) ≤ p * (p - 1) at hbound
  rw [hnorm] at hbound
  have hs : s < p := by nlinarith [hp.out.pos, Nat.sub_add_cancel hp.out.one_lt.le]
  have ha : Nat.card (Sylow p G) % p = 1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hp.out.one_lt] using card_sylow_modEq_one p G
  have hsm := prime_degree_normalizer_arithmetic hp.out.pos hr.out.pos hrp hs hmcong ha
    (hfactor.symm.trans hG)
  have hcount : Nat.card (Sylow p G) = m := hsm.2
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hG]
    nlinarith [hp.out.two_le, hr.out.two_le])
  have : MulAction.IsPreprimitive G X := MulAction.IsPreprimitive.of_prime_card (hX ▸ hp.out)
  constructor
  intro N hnormal
  let := hnormal
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  have : MulAction.IsPretransitive N X := normal_pretransitive N hN
  have : FaithfulSMul N X := ⟨fun he => Subtype.ext (eq_of_smul_eq_smul (α := X) he)⟩
  have hdN : p ∣ Nat.card N := by
    have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup N a)
    rw [Nat.card_prod] at hc
    have ho : Nat.card (MulAction.orbit N a) = p := by
      rw [MulAction.orbit_eq_univ]
      simpa using hX
    rw [ho] at hc
    exact ⟨_, hc.symm⟩
  have hsqN : ¬ p ^ 2 ∣ Nat.card N := fun h => hsq (h.trans N.card_subgroup_dvd_card)
  have hle := sylow_le_normal_of_prime_dvd p hsq N hdN
  have hcountN : Nat.card (Sylow p N) = m :=
    (sylow_card_subgroup_of_all_le p N hle).symm.trans hcount
  let Q : Sylow p N := Classical.choice inferInstance
  have hcQ := sylow_card_prime (G := N) p hdN hsqN
  obtain ⟨t, htpos, _, ht⟩ := sylow_normalizer_factor p Q (hcQ Q)
  rw [hcountN] at ht
  have hdiv : (p * m) * t ∣ (p * m) * r := by
    have h := N.card_subgroup_dvd_card
    rw [ht, hG] at h
    convert h using 1 <;> ring
  have htr : t ∣ r := (Nat.mul_dvd_mul_iff_left
    (Nat.mul_pos hp.out.pos (by omega : 0 < m))).mp hdiv
  rcases (Nat.dvd_prime hr.out).mp htr with htone | htr
  · have hc : Nat.card N = p * Nat.card (Sylow p N) := by rw [ht, htone, hcountN, mul_one]
    have h1 := sylow_count_one_of_card (G := N) p hX hcQ hc
    rw [hcountN] at h1
    omega
  · apply N.eq_top_of_card_eq
    rw [ht, htr, hG]


end Atlas.GroupTheory
