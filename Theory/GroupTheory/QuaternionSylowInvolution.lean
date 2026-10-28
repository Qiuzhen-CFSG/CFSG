module

public import Theory.GroupTheory.Involution.Basic
public import Theory.GroupTheory.PPrimeCoreSubgroup
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Involutions with a generalized quaternion Sylow subgroup

If the center modulo the odd core has even order, every involution is central
modulo that core. Generalized quaternion groups have a unique involution;
commuting involutions lie in a common Sylow subgroup and hence coincide.
The odd-core quotient preserves the quaternion Sylow subgroup and the order
of each involution, so a central involution there equals any given involution.

This extracts the elementary quotient-centrality bridge from Peterfalvi's
Appendix II, `BenderSuzuki/PFAppendixII/proposition_1.lean`. The even-center
hypothesis is the separate input supplied by Brauer–Suzuki (Suzuki,
*Group Theory II*, VI, §2.2, Example 3).
-/

namespace BenderSuzuki.PFAppendixII

open BenderSuzuki.PFAppendixIII
open scoped Pointwise

universe u

private lemma appendixII_quaternionGroup_eq_a_parameter_of_isInvolution
    (m : ℕ) [NeZero m] {q : QuaternionGroup m} (hq : IsInvolution q) :
    q = QuaternionGroup.a (m : ZMod (2 * m)) := by
  have hm_pos : 0 < m := NeZero.pos m
  have hm_lt : m < 2 * m := by omega
  cases q with
  | xa i =>
      have horder_two :
          orderOf (QuaternionGroup.xa i : QuaternionGroup m) = 2 :=
        orderOf_eq_prime hq.sq_eq_one hq.ne_one
      rw [QuaternionGroup.orderOf_xa] at horder_two
      omega
  | a i =>
      have horder_two :
          orderOf (QuaternionGroup.a i : QuaternionGroup m) = 2 :=
        orderOf_eq_prime hq.sq_eq_one hq.ne_one
      rw [QuaternionGroup.orderOf_a] at horder_two
      have hdiv_mul :=
        Nat.div_mul_cancel (Nat.gcd_dvd_left (2 * m) i.val)
      rw [horder_two] at hdiv_mul
      have hgcd : Nat.gcd (2 * m) i.val = m := by omega
      have hm_dvd_i : m ∣ i.val := by
        obtain ⟨k, hk⟩ := Nat.gcd_dvd_right (2 * m) i.val
        refine ⟨k, ?_⟩
        calc
          i.val = Nat.gcd (2 * m) i.val * k := hk
          _ = m * k := by rw [hgcd]
      obtain ⟨k, hk⟩ := hm_dvd_i
      have hi_lt : i.val < 2 * m := ZMod.val_lt i
      have hi_ne_zero : i.val ≠ 0 := by
        intro hi_zero
        apply hq.ne_one
        rw [QuaternionGroup.one_def]
        congr 1
        exact (ZMod.val_eq_zero i).mp hi_zero
      have hk_ne_zero : k ≠ 0 := by
        intro hk_zero
        apply hi_ne_zero
        simp [hk, hk_zero]
      have hk_lt_two : k < 2 := by
        apply (Nat.mul_lt_mul_right hm_pos).mp
        simpa [Nat.mul_comm, hk] using hi_lt
      have hk_eq : k = 1 := by omega
      congr 1
      apply ZMod.val_injective
      simp [hk, hk_eq, ZMod.val_natCast, Nat.mod_eq_of_lt hm_lt]
/-- An involution generates a two-subgroup. -/
public theorem isPGroup_zpowers_of_involution
    {G : Type u} [Group G] [Finite G] {x : G} (hx : IsInvolution x) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have horder : orderOf x = 2 := (orderOf_eq_prime_iff).2 ⟨hx.2, hx.1⟩
  have hcard : Nat.card (Subgroup.zpowers x) = 2 := by
    simp [Nat.card_zpowers, horder]
  exact IsPGroup.of_card (p := 2) (G := Subgroup.zpowers x) (n := 1) (by
    simp [hcard])

private lemma appendixII_sylow_involution_unique
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G) {n : ℕ}
    (hQ : Nonempty (Q ≃* QuaternionGroup (2 ^ (n - 2)))) :
    ∀ x y : Q, IsInvolution x → IsInvolution y → x = y := by
  let eqv : Q ≃* QuaternionGroup (2 ^ (n - 2)) := Classical.choice hQ
  intro x y hx hy
  have hex : IsInvolution (eqv x) := by
    constructor
    · intro h
      apply hx.ne_one
      apply eqv.injective
      simpa using h
    · simpa using congrArg eqv hx.sq_eq_one
  have hey : IsInvolution (eqv y) := by
    constructor
    · intro h
      apply hy.ne_one
      apply eqv.injective
      simpa using h
    · simpa using congrArg eqv hy.sq_eq_one
  apply eqv.injective
  exact
    (appendixII_quaternionGroup_eq_a_parameter_of_isInvolution
      (2 ^ (n - 2)) hex).trans
      (appendixII_quaternionGroup_eq_a_parameter_of_isInvolution
        (2 ^ (n - 2)) hey).symm

private lemma appendixII_commuting_involutions_eq
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G)
    (hunique : ∀ x y : Q, IsInvolution x → IsInvolution y → x = y)
    {u v : G} (hu : IsInvolution u) (hv : IsInvolution v) (huv : Commute u v) :
    u = v := by
  have huP : IsPGroup 2 (Subgroup.zpowers u) :=
    isPGroup_zpowers_of_involution hu
  have hvP : IsPGroup 2 (Subgroup.zpowers v) :=
    isPGroup_zpowers_of_involution hv
  have hnorm : Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers v) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor <;> intro hy
    · rcases hx with ⟨m, rfl⟩
      rcases hy with ⟨n, rfl⟩
      exact ⟨n, by rw [huv.zpow_zpow m n, mul_inv_cancel_right]⟩
    · rcases hx with ⟨m, rfl⟩
      rcases hy with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      change v ^ n = u ^ m * y * (u ^ m)⁻¹ at hn
      have hcomm := huv.zpow_zpow m n
      calc
        v ^ n = (u ^ m)⁻¹ * (u ^ m * v ^ n) := by group
        _ = (u ^ m)⁻¹ * (v ^ n * u ^ m) := by rw [hcomm.eq]
        _ = (u ^ m)⁻¹ * ((u ^ m * y * (u ^ m)⁻¹) * u ^ m) := by rw [hn]
        _ = y := by group
  have hsupP : IsPGroup 2
      (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' huP hvP hnorm
  obtain ⟨S, hsup_le_S⟩ :=
    IsPGroup.exists_le_sylow (G := G) (p := 2) hsupP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  have huS : u ∈ (S : Subgroup G) :=
    hsup_le_S ((le_sup_left :
      Subgroup.zpowers u ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
        (Subgroup.mem_zpowers u))
  have hvS : v ∈ (S : Subgroup G) :=
    hsup_le_S ((le_sup_right :
      Subgroup.zpowers v ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
        (Subgroup.mem_zpowers v))
  have hcoe : ((g • S : Sylow 2 G) : Subgroup G) = (Q : Subgroup G) :=
    congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hg
  let ug : Q := ⟨g * u * g⁻¹, by
    have hmem' : g * u * g⁻¹ ∈ ((g • S : Sylow 2 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Set.mem_smul_set.mpr ⟨u, huS, rfl⟩
    have hmem : g * u * g⁻¹ ∈ (Q : Subgroup G) := by
      simpa [hcoe] using hmem'
    exact hmem⟩
  let vg : Q := ⟨g * v * g⁻¹, by
    have hmem' : g * v * g⁻¹ ∈ ((g • S : Sylow 2 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Set.mem_smul_set.mpr ⟨v, hvS, rfl⟩
    have hmem : g * v * g⁻¹ ∈ (Q : Subgroup G) := by
      simpa [hcoe] using hmem'
    exact hmem⟩
  have hugAmbient : IsInvolution (g * u * g⁻¹) := by
    simpa [rightConjugateElem] using
      isInvolution_rightConjugateElem (g := g⁻¹) hu
  have hvgAmbient : IsInvolution (g * v * g⁻¹) := by
    simpa [rightConjugateElem] using
      isInvolution_rightConjugateElem (g := g⁻¹) hv
  have hug : IsInvolution ug := by
    constructor
    · intro h
      apply hugAmbient.1
      simpa [ug] using congrArg Subtype.val h
    · apply Subtype.ext
      simpa [ug] using hugAmbient.2
  have hvg : IsInvolution vg := by
    constructor
    · intro h
      apply hvgAmbient.1
      simpa [vg] using congrArg Subtype.val h
    · apply Subtype.ext
      simpa [vg] using hvgAmbient.2
  have heq : ug = vg := hunique ug vg hug hvg
  have hcoe' : g * u * g⁻¹ = g * v * g⁻¹ := congrArg Subtype.val heq
  simpa using (mul_left_cancel (mul_right_cancel hcoe'))

private lemma appendixII_quotient_sylow
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G) {n : ℕ}
    (hQ : Nonempty (Q ≃* QuaternionGroup (2 ^ (n - 2)))) :
    ∃ Qbar : Sylow 2 (G ⧸ pPrimeCore 2 G),
      Nonempty (Qbar ≃* QuaternionGroup (2 ^ (n - 2))) := by
  classical
  let N : Subgroup G := pPrimeCore 2 G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Qbar : Sylow 2 (G ⧸ N) :=
    Q.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have hqinj : Function.Injective (q.comp (Q : Subgroup G).subtype) := by
    simpa [q, N] using
      IsPGroup.quotient_pPrimeCore_injective
        (G := G) (p := 2) (H := (Q : Subgroup G)) Q.isPGroup'
  let f : Q →* Qbar :=
    (q.comp (Q : Subgroup G).subtype).codRestrict Qbar (by
      intro x
      change q (x : G) ∈ (Qbar : Subgroup (G ⧸ N))
      rw [show (Qbar : Subgroup (G ⧸ N)) = (Q : Subgroup G).map q by
        simp [Qbar, Sylow.coe_mapSurjective]]
      exact Subgroup.mem_map_of_mem q x.2)
  have hfbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact congrArg Subtype.val (hqinj (congrArg Subtype.val hxy))
    · intro y
      have hy : (y : G ⧸ N) ∈ (Q : Subgroup G).map q := by
        have htemp : (Qbar : Subgroup (G ⧸ N)) = (Q : Subgroup G).map q := by
          simp [Qbar, Sylow.coe_mapSurjective]
        rw [← htemp]
        exact y.2
      rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hxy
  let eQbar : Q ≃* Qbar := MulEquiv.ofBijective f hfbij
  refine ⟨Qbar, ?_⟩
  exact ⟨eQbar.symm.trans (Classical.choice hQ)⟩

/-- A quaternion Sylow subgroup and an even center modulo the odd core force every
involution to be central modulo that core. -/
public theorem quotient_involution_central_of_even_center
    {G : Type u} [Group G] [Finite G]
    (P : Sylow 2 G) {n : ℕ}
    (hP : Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2))))
    (hcenterEven : 2 ∣ Nat.card (Subgroup.center (G ⧸ pPrimeCore 2 G)))
    (u : G) (huI : IsInvolution u) :
    QuotientGroup.mk' (pPrimeCore 2 G) u ∈
      Subgroup.center (G ⧸ pPrimeCore 2 G) := by
  classical
  let N : Subgroup G := pPrimeCore 2 G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  obtain ⟨Qbar, hQbar⟩ := appendixII_quotient_sylow P hP
  have huniqueQbar :=
    appendixII_sylow_involution_unique Qbar hQbar
  obtain ⟨z, hzorder⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := Subgroup.center (G ⧸ N)) 2 hcenterEven
  have hzorderAmbient : orderOf (z : G ⧸ N) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hzorder
  have hzI : IsInvolution (z : G ⧸ N) := by
    have hz := orderOf_eq_prime_iff.mp hzorderAmbient
    exact ⟨hz.2, by simpa [pow_two] using hz.1⟩
  have huP : IsPGroup 2 (Subgroup.zpowers u) :=
    isPGroup_zpowers_of_involution huI
  have hqinj :
      Function.Injective
        (q.comp (Subgroup.zpowers u).subtype) := by
    simpa [q, N] using
      IsPGroup.quotient_pPrimeCore_injective
        (G := G) (p := 2) (H := Subgroup.zpowers u) huP
  let uz : Subgroup.zpowers u := ⟨u, Subgroup.mem_zpowers u⟩
  have huzOrder : orderOf uz = 2 := by
    rw [← Subgroup.orderOf_coe uz]
    simpa [uz] using orderOf_eq_prime huI.sq_eq_one huI.ne_one
  have hquOrder : orderOf (q u) = 2 := by
    have horder :=
      orderOf_injective
        (q.comp (Subgroup.zpowers u).subtype) hqinj uz
    simpa [uz] using horder.trans huzOrder
  have hquI : IsInvolution (q u) := by
    have h := orderOf_eq_prime_iff.mp hquOrder
    exact ⟨h.2, by simpa [pow_two] using h.1⟩
  have hcomm : Commute (z : G ⧸ N) (q u) := by
    rw [commute_iff_eq]
    exact (Subgroup.mem_center_iff.mp z.2 (q u)).symm
  have hzu : (z : G ⧸ N) = q u :=
    appendixII_commuting_involutions_eq Qbar huniqueQbar hzI hquI hcomm
  rw [← hzu]
  exact z.2

end BenderSuzuki.PFAppendixII
