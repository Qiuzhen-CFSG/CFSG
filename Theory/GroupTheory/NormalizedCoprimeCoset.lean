module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Commuting representatives in normalized coprime cosets

If a Sylow `p`-subgroup `P` normalizes a subgroup `H` of order prime to `p`,
every `xy`, with `x ∈ P` and `y ∈ H`, is `H`-conjugate to `xv` for some
`v ∈ H` commuting with `x`.

Split `xy` into its commuting prime-power and prime-to-`p` parts inside
`PH`. The quotient `PH/H` is a `p`-group, so the second part lies in `H`.
Sylow conjugacy and injectivity of `P → PH/H` give an `H`-conjugator taking
the first part to `x`.

This is the group-theoretic transport in Glauberman, *A Characterization
of the Suzuki Groups* (1968), p. 90, immediately before equation (4.8).
The source is saved in `refs/original/n-group-global/odd-core-rank-two-source/`.
-/

open Subgroup

private theorem exists_prime_decomposition {G : Type*} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (g : G) :
    ∃ u v : G, (∃ k : ℕ, u ^ (p ^ k) = 1) ∧
      Nat.Coprime p (orderOf v) ∧ Commute u v ∧ u * v = g := by
  obtain ⟨k, m, hm, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
  have hmpos : 0 < m := by
    have := orderOf_pos g
    rw [hn] at this
    exact Nat.pos_of_mul_pos_left this
  have hord : orderOf (g ^ m) = p ^ k := by
    rw [orderOf_pow_of_dvd hmpos.ne' (by rw [hn]; exact dvd_mul_left _ _), hn]
    exact Nat.mul_div_cancel _ hmpos
  have hcop : Nat.Coprime m (orderOf (g ^ m)) := by
    rw [hord]
    exact (hp.coprime_iff_not_dvd.mpr hm).symm.pow_right k
  obtain ⟨b, hb⟩ := exists_pow_eq_self_of_coprime hcop
  let u := (g ^ m) ^ b
  let v := u⁻¹ * g
  have hum : u ^ m = g ^ m := by
    simpa only [u, ← pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hb
  have hug : Commute u g := (Commute.refl g).pow_left m |>.pow_left b
  have hvm : v ^ m = 1 := by
    rw [hug.inv_left.mul_pow, inv_pow, hum, inv_mul_cancel]
  refine ⟨u, v, ⟨k, ?_⟩, ?_, ?_, ?_⟩
  · change ((g ^ m) ^ b) ^ (p ^ k) = 1
    rw [← pow_mul, Nat.mul_comm b, pow_mul, ← hord, pow_orderOf_eq_one, one_pow]
  · exact (hp.coprime_iff_not_dvd.mpr hm).of_dvd_right
      (orderOf_dvd_of_pow_eq_one hvm)
  · exact (Commute.refl u).inv_right.mul_right hug
  · exact mul_inv_cancel_left u g

private theorem quotient_injective_on_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (N : Subgroup G) [N.Normal]
    (hcop : Nat.Coprime p (Nat.card N)) :
    Function.Injective ((QuotientGroup.mk' N).comp (S : Subgroup G).subtype) := by
  let f := (QuotientGroup.mk' N).comp (S : Subgroup G).subtype
  apply f.ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro s hs
  change s = 1
  have hsN : (s : G) ∈ N := (QuotientGroup.eq_one_iff (N := N) _).mp hs
  have hd : orderOf s ∣ Nat.card N := by
    simpa only [Subgroup.orderOf_coe] using N.orderOf_dvd_natCard hsN
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (S.isPGroup'.orderOf_coprime hcop s) dvd_rfl hd)

private theorem quotient_surjective_on_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (N : Subgroup G) [N.Normal]
    (hquot : IsPGroup p (G ⧸ N)) :
    Function.Surjective ((QuotientGroup.mk' N).comp (S : Subgroup G).subtype) := by
  let q := QuotientGroup.mk' N
  let T := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have htop : (T : Subgroup (G ⧸ N)) = ⊤ :=
    (T.is_maximal' (hquot.to_subgroup ⊤) le_top).symm
  intro a
  have ha : a ∈ (S : Subgroup G).map q := by
    rw [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective N) S, htop]
    trivial
  obtain ⟨s, hs, he⟩ := ha
  exact ⟨⟨s, hs⟩, he⟩

private theorem exists_conj_eq_of_quotient_eq
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (N : Subgroup G) [N.Normal]
    (hcop : Nat.Coprime p (Nat.card N)) (hquot : IsPGroup p (G ⧸ N))
    (u : G) (hu : ∃ k : ℕ, u ^ (p ^ k) = 1) (x : S)
    (he : QuotientGroup.mk' N u = QuotientGroup.mk' N x) :
    ∃ a : N, (a : G) * u * (a : G)⁻¹ = x := by
  let q := QuotientGroup.mk' N
  have hcyc : IsPGroup p (zpowers u) := by
    obtain ⟨k, hk⟩ := hu
    apply IsPGroup.of_card_dvd_pow (n := k)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hk
  obtain ⟨T, hT⟩ := hcyc.exists_le_sylow
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq G T S
  have hbu : b * u * b⁻¹ ∈ (S : Subgroup G) := by
    rw [← hb]
    exact ⟨u, hT (mem_zpowers u), rfl⟩
  obtain ⟨s, hs⟩ := quotient_surjective_on_sylow S N hquot (q b)
  have haN : (s : G)⁻¹ * b ∈ N := by
    apply (QuotientGroup.eq_one_iff (N := N) _).mp
    change q ((s : G)⁻¹ * b) = 1
    rw [map_mul, map_inv, ← hs]
    exact inv_mul_cancel _
  let a : N := ⟨(s : G)⁻¹ * b, haN⟩
  have ha : (a : G) * u * (a : G)⁻¹ =
      (s : G)⁻¹ * (b * u * b⁻¹) * s := by dsimp [a]; group
  have hau : (a : G) * u * (a : G)⁻¹ ∈ (S : Subgroup G) := by
    rw [ha]
    exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem
      ((S : Subgroup G).inv_mem s.property) hbu) s.property
  refine ⟨a, ?_⟩
  apply congrArg Subtype.val (quotient_injective_on_sylow S N hcop
    (a₁ := ⟨_, hau⟩) (a₂ := x) ?_)
  change q ((a : G) * u * (a : G)⁻¹) = q x
  have hqa : q a = 1 := (QuotientGroup.eq_one_iff (N := N) _).mpr a.property
  simpa only [map_mul, map_inv, hqa, one_mul, inv_one, mul_one] using he

/-- A coset of a normalized prime-to-`p` subgroup has a commuting representative
with the same Sylow component, obtained by conjugating within that subgroup. -/
public theorem Sylow.exists_conj_mul_commuting_of_normalized_coprime
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (H : Subgroup G)
    (hcop : Nat.Coprime p (Nat.card H))
    (hnorm : (P : Subgroup G) ≤ normalizer (H : Set G))
    (x : P) (y : H) :
    ∃ a v : H, Commute (x : G) (v : G) ∧
      (a : G) * ((x : G) * y) * (a : G)⁻¹ = (x : G) * v := by
  let L : Subgroup G := (P : Subgroup G) ⊔ H
  let N : Subgroup L := H.subgroupOf L
  let S : Sylow p L := P.subtype le_sup_left
  let : N.Normal := normal_subgroupOf_sup_of_le_normalizer hnorm
  let q := QuotientGroup.mk' N
  let xL : L := ⟨x, (le_sup_left : (P : Subgroup G) ≤ L) x.property⟩
  let yL : L := ⟨y, (le_sup_right : H ≤ L) y.property⟩
  have hNcop : Nat.Coprime p (Nat.card N) := hcop.of_dvd_right
    (card_comap_dvd_of_injective H L.subtype L.subtype_injective)
  let : (H.subgroupOf (P : Subgroup G)).Normal :=
    normal_subgroupOf_of_le_normalizer hnorm
  have hquot : IsPGroup p (L ⧸ N) :=
    (P.isPGroup'.to_quotient (H.subgroupOf (P : Subgroup G))).of_equiv
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient (P : Subgroup G) H hnorm)
  obtain ⟨u, v, hu, hv, huv, he⟩ :=
    exists_prime_decomposition p (Fact.out : p.Prime) (xL * yL)
  have hqv : q v = 1 := by
    obtain ⟨k, hk⟩ := hquot.exists_orderOf_eq_pow (q v)
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes (hv.pow_left k)
      (hk ▸ dvd_refl _) (orderOf_map_dvd q v)
  have hqu : q u = q xL := by
    have heq := congrArg q he
    have hqy : q yL = 1 := (QuotientGroup.eq_one_iff (N := N) _).mpr y.property
    simpa only [map_mul, hqv, hqy, mul_one] using heq
  obtain ⟨a, ha⟩ := exists_conj_eq_of_quotient_eq S N hNcop hquot u hu
    ⟨xL, x.property⟩ hqu
  change (a : L) * u * (a : L)⁻¹ = xL at ha
  let v' : L := (a : L) * v * (a : L)⁻¹
  have hvN : v ∈ N := (QuotientGroup.eq_one_iff (N := N) _).mp hqv
  have hv'N : v' ∈ N := N.mul_mem (N.mul_mem a.property hvN) (N.inv_mem a.property)
  refine ⟨⟨((a : L) : G), a.property⟩, ⟨(v' : G), hv'N⟩, ?_, ?_⟩
  · have hc := huv.map (MulAut.conj (a : L)).toMonoidHom
    change Commute ((a : L) * u * (a : L)⁻¹) v' at hc
    rw [ha] at hc
    exact hc.map L.subtype
  · have hprod : (a : L) * (xL * yL) * (a : L)⁻¹ = xL * v' := by
      rw [← he, ← ha]
      dsimp [v']
      group
    exact congrArg L.subtype hprod
