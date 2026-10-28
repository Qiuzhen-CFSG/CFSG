module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenSetup
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The local seven-centralizer normalizer structure

Every nonidentity element of the seven-centralizer has that same centralizer:
an involution acts without fixed points on each of these centralizers and
hence inverts it. Taking square roots in the odd-order centralizer gives
the factorization of its normalizer by the literal involution-centralizer
intersection. Sylow counting inside the group of order 168 supplies an
order-three element in both normalizers.

The complement has a unique involution. In the actual A₅ × C₂ model its
projection to A₅ therefore has odd order. The order-three witness and the
simple-group index bound force this image to have order three, and the
kernel has order two. Commuting elements of orders three and two generate
the resulting cyclic complement of order six.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), proof of (4.3), printed p.226.
-/

open Subgroup
private abbrev A5 := alternatingGroup (Fin 5)
private abbrev C2 := Multiplicative (ZMod 2)

private theorem complement_card_of_model {K : Type*} [Group K] [Finite K]
    (f : K →* A5 × C2) (hf : Function.Injective f)
    (h2 : 2 ∣ Nat.card K) (h3 : 3 ∣ Nat.card K)
    (hi : ∀ u : K, orderOf u = 2 → (f u).1 = 1) : Nat.card K = 6 := by
  let g : K →* A5 := (MonoidHom.fst A5 C2).comp f
  let k : g.ker →* C2 := ((MonoidHom.snd A5 C2).comp f).comp g.ker.subtype
  have hk : Function.Injective k := by
    intro x y he
    apply Subtype.ext
    apply hf
    apply Prod.ext
    · exact x.property.trans y.property.symm
    · exact he
  have hkdiv : Nat.card g.ker ∣ 2 := by
    have hc := Nat.card_congr (MonoidHom.ofInjective hk).toEquiv
    have hd := k.range.card_subgroup_dvd_card
    rw [← hc] at hd
    simpa [Nat.card_eq_fintype_card] using hd
  have hgodd : ¬ 2 ∣ Nat.card g.range := by
    intro hd
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := g.range) 2 hd
    obtain ⟨x, hx⟩ := u.property
    have hux : orderOf (g x) = 2 := by rw [hx]; exact (orderOf_coe u).trans hu
    have hx2 : x ^ 2 = 1 := by
      apply hf
      rw [map_pow, map_one]
      apply Prod.ext
      · change (g x) ^ 2 = 1
        exact hux ▸ pow_orderOf_eq_one (g x)
      · have h : ∀ z : C2, z ^ 2 = 1 := by decide +kernel
        exact h (f x).2
    have hxne : x ≠ 1 := by intro he; simp [he] at hux
    have hi' := hi x (orderOf_eq_prime_iff.mpr ⟨hx2, hxne⟩)
    change g x = 1 at hi'
    simp [hi'] at hux
  have hprod : Nat.card g.ker * Nat.card g.range = Nat.card K := by
    simpa only [index_ker] using g.ker.card_mul_index
  have hd : Nat.card g.range ∣ 60 := by
    have hd := g.range.card_subgroup_dvd_card
    change Nat.card g.range ∣ Nat.card (alternatingGroup (Fin 5)) at hd
    rw [nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
    exact hd
  have hg3 : 3 ∣ Nat.card g.range := by
    have hk3 : ¬ 3 ∣ Nat.card g.ker := fun hh => by
      have := hh.trans hkdiv
      norm_num at this
    rw [← hprod] at h3
    exact (Nat.Prime.dvd_mul (by decide : Nat.Prime 3)).mp h3 |>.resolve_left hk3
  have hcases : Nat.card g.range = 3 ∨ Nat.card g.range = 15 := by
    have hm := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    have hc : (60 : ℕ).divisors = {1,2,3,4,5,6,10,12,15,20,30,60} := by decide
    rw [hc] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  have hgcard : Nat.card g.range = 3 := by
    rcases hcases with hc | hc
    · exact hc
    have hi4 : g.range.index = 4 := by
      have hp := g.range.card_mul_index
      rw [hc, nat_card_alternatingGroup] at hp
      norm_num [Nat.factorial] at hp
      omega
    have htop := Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt g.range
      (by rw [hi4, nat_card_alternatingGroup]; norm_num [Nat.factorial])
    have hbad : Nat.card g.range = 60 := by rw [htop, card_top, nat_card_alternatingGroup]; norm_num [Nat.factorial]
    omega
  rw [hgcard] at hprod
  have hkcases := (Nat.dvd_prime Nat.prime_two).mp hkdiv
  omega

namespace CFSG.Quasithin.Janko1CentralizerData

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {d : ℕ} (localData : BenderPrimeData G d)

include h
private theorem involution_inverts_of_coprime (A : Subgroup G)
    (hc : Nat.Coprime (Nat.card A) 120)
    (t : G) (ht : orderOf t = 2) (htN : t ∈ normalizer (A : Set G)) :
    (∀ x : G, x ∈ A → t * x * t⁻¹ = x⁻¹) ∧ IsMulCommutative A := by
  let f : MulAut A := A.normalizerMonoidHom ⟨t, htN⟩
  have hdisj : Disjoint A (centralizer ({t} : Set G)) := by
    apply disjoint_of_coprime_natCard
    rw [h.involution_centralizer_card t ht]
    exact hc
  have hfree : MonoidHom.FixedPointFree f := by
    intro x hx
    apply Subtype.ext
    apply hdisj.le_bot
    refine ⟨x.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have he : t * (x : G) * t⁻¹ = x := congrArg Subtype.val hx
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hf2 : Function.Involutive f := by
    intro x
    apply Subtype.ext
    change t * (t * (x : G) * t⁻¹) * t⁻¹ = x
    have ht2 : t * t = 1 := by
      simpa only [pow_two] using (show t ^ 2 = 1 from ht ▸ pow_orderOf_eq_one t)
    calc
      _ = (t * t) * (x : G) * (t * t)⁻¹ := by group
      _ = x := by rw [ht2]; simp
  refine ⟨?_, ⟨⟨fun x y => (hfree.commute_all_of_involutive hf2 x y).eq⟩⟩⟩
  intro x hx
  exact congrArg Subtype.val (congrFun (hfree.coe_eq_inv_of_involutive hf2) ⟨x, hx⟩)

include h localData
private theorem small_centralizer_order (y : G)
    (hy : orderOf y = 2 ∨ orderOf y = 3 ∨ orderOf y = 5) :
    Nat.card (centralizer ({y} : Set G)) ∣ 120 := by
  rcases hy with hy | hy | hy
  · rw [h.involution_centralizer_card y hy]
  · rw [localData.centralizer_three y hy]
    split_ifs <;> decide
  · rw [localData.centralizer_five y hy]
    rcases localData.d_cases with hd | hd <;> rw [hd] <;> decide

private theorem element_centralizer_coprime (S : Subgroup G) (hS : Nat.card S = 7)
    (x : G) (hx : x ∈ centralizer (S : Set G)) (hne : x ≠ 1) :
    Nat.Coprime (Nat.card (centralizer ({x} : Set G))) 120 := by
  have hox : Nat.Coprime (orderOf x) 120 :=
    (h.seven_centralizer_coprime localData S hS).of_dvd_left
      ((centralizer (S : Set G)).orderOf_dvd_natCard hx)
  have no (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3 ∨ p = 5) :
      ¬ p ∣ Nat.card (centralizer ({x} : Set G)) := by
    intro hd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := centralizer ({x} : Set G)) p hd
    have hyG : orderOf (y : G) = p := (orderOf_coe y).trans hy
    have hxC : x ∈ centralizer ({(y : G)} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp y.property).symm
    have hdvd : orderOf x ∣ 120 :=
      ((centralizer ({(y : G)} : Set G)).orderOf_dvd_natCard hxC).trans
        (h.small_centralizer_order localData y
          (by rcases hp with rfl | rfl | rfl <;> tauto))
    exact hne (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hox dvd_rfl hdvd))
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have c2 := (Nat.prime_two.coprime_iff_not_dvd.mpr (no 2 (by simp))).symm
  have c3 := ((show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr (no 3 (by simp))).symm
  have c5 := ((show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr (no 5 (by simp))).symm
  exact (c2.pow_right 3).mul_right (c3.mul_right c5)

/-- Every nonidentity element of the seven-centralizer has the same
centralizer. -/
public theorem seven_regular_centralizer (S : Subgroup G) (hS : Nat.card S = 7)
    (t : G) (ht : orderOf t = 2) (htN : t ∈ normalizer (S : Set G))
    (x : G) (hx : x ∈ centralizer (S : Set G)) (hne : x ≠ 1) :
    centralizer ({x} : Set G) = centralizer (S : Set G) := by
  obtain ⟨hinv, hcomm⟩ := h.seven_centralizer_inverted localData S hS t ht htN
  let _ := hcomm
  have hxinv := hinv x hx
  have htCx : t ∈ normalizer (centralizer ({x} : Set G) : Set G) := by
    rw [mem_normalizer_iff]
    have ht2 : t * t = 1 := by
      simpa only [pow_two] using (show t ^ 2 = 1 from ht ▸ pow_orderOf_eq_one t)
    have forward : ∀ y : G, y ∈ centralizer ({x} : Set G) →
        t * y * t⁻¹ ∈ centralizer ({x} : Set G) := by
      intro y hy
      have hxy : Commute x y := (mem_centralizer_singleton_iff.mp hy).symm
      have hconj := congrArg (fun q : G => t * q * t⁻¹) hxy.eq
      have hconj' : Commute (t * x * t⁻¹) (t * y * t⁻¹) := by
        change (t * x * t⁻¹) * (t * y * t⁻¹) =
          (t * y * t⁻¹) * (t * x * t⁻¹)
        calc
          _ = t * (x * y) * t⁻¹ := by group
          _ = t * (y * x) * t⁻¹ := hconj
          _ = _ := by group
      have hconj'' : Commute x⁻¹ (t * y * t⁻¹) := by
        simpa only [hxinv] using hconj'
      exact mem_centralizer_singleton_iff.mpr
        (by simpa only [inv_inv] using hconj''.inv_left.eq.symm)
    intro y
    constructor
    · exact forward y
    · intro hy
      have hforward := forward (t * y * t⁻¹) hy
      have heq : t * (t * y * t⁻¹) * t⁻¹ = y := by
        calc
          _ = (t * t) * y * (t * t)⁻¹ := by group
          _ = y := by rw [ht2]; simp
      rw [heq] at hforward
      exact hforward
  have hcx := (involution_inverts_of_coprime (h := h) (centralizer ({x} : Set G))
    (element_centralizer_coprime h localData S hS x hx hne) t ht htCx).2
  let _ := hcx
  apply le_antisymm
  · intro y hy s hs
    have hsx : s ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.mpr (hx s hs)
    exact congrArg Subtype.val
      (@Std.Commutative.comm _ (fun a b => a * b)
        (@IsMulCommutative.is_comm _ _ hcx) (⟨s, hsx⟩ : centralizer ({x} : Set G))
        ⟨y, hy⟩)
  · intro y hy
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val
        (@Std.Commutative.comm _ (fun a b => a * b)
          (@IsMulCommutative.is_comm _ _ hcomm) (⟨y, hy⟩ : centralizer (S : Set G))
          ⟨x, hx⟩))

omit localData in
private theorem exists_order_three_normalizing_seven (S : Subgroup G)
    (hS : Nat.card S = 7) (hSN : S ≤ normalizer (h.sylow : Set G)) :
    ∃ x : G, x ∈ normalizer (h.sylow : Set G) ∧
      x ∈ normalizer (S : Set G) ∧ orderOf x = 3 := by
  let NQ := normalizer (h.sylow : Set G)
  let SN : Subgroup NQ := S.subgroupOf NQ
  have hNQcard : Nat.card NQ = 168 := h.sylow_normalizer_card
  have hSNcard : Nat.card SN = 7 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hSN).toEquiv, hS]
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hcardeq : Nat.card SN = 7 ^ (Nat.card NQ).factorization 7 := by
    rw [hSNcard, h.sylow_normalizer_card]
    decide +kernel
  let P : Sylow 7 NQ := Sylow.ofCard SN hcardeq
  have hPcoe : (P : Subgroup NQ) = SN := Sylow.coe_ofCard SN hcardeq
  have hPcard : Nat.card P = 7 := by simpa [hPcoe] using hSNcard
  have hnum : Nat.card (Sylow 7 NQ) = (normalizer (P : Set NQ)).index :=
    Sylow.card_eq_index_normalizer P
  have hd : Nat.card (Sylow 7 NQ) ∣ 168 := by
    rw [hnum]
    have hh := (normalizer (P : Set NQ)).index_dvd_card
    change (normalizer (P : Set NQ)).index ∣ Nat.card NQ at hh
    rw [hNQcard] at hh
    exact hh
  have hm := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hs : (168 : ℕ).divisors =
      {1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} := by decide
  rw [hs] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have hmod := card_sylow_modEq_one 7 NQ
  change Nat.card (Sylow 7 NQ) % 7 = 1 % 7 at hmod
  have hnum_cases : Nat.card (Sylow 7 NQ) = 1 ∨ Nat.card (Sylow 7 NQ) = 8 := by
    omega
  have hprod := (normalizer (P : Set NQ)).index_mul_card
  have hnorm3 : 3 ∣ Nat.card (normalizer (P : Set NQ)) := by
    rcases hnum_cases with hn | hn
    · rw [← hnum, hn] at hprod
      rw [hNQcard] at hprod
      omega
    · rw [← hnum, hn] at hprod
      rw [hNQcard] at hprod
      omega
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨xN, hxN⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (P : Set NQ))
    3 hnorm3
  have hxNQ : (xN : NQ) ∈ normalizer (SN : Set NQ) := by
    rw [← hPcoe]
    exact xN.property
  have hxG : (xN : G) ∈ normalizer (S : Set G) := by
    have hh : (xN : NQ) ∈ (normalizer (S : Set G)).subgroupOf NQ := by
      rw [subgroupOf_normalizer_eq hSN]
      exact hxNQ
    exact hh
  have hxNQorder : orderOf ((xN : normalizer (P : Set NQ)) : NQ) = 3 :=
    (orderOf_coe xN).trans hxN
  exact ⟨(xN : G), (xN : NQ).property, hxG,
    (orderOf_coe (xN : NQ)).trans hxNQorder⟩

private theorem seven_centralizer_self_centralizing (S : Subgroup G)
    (hS : Nat.card S = 7) (hne : centralizer (S : Set G) ≠ S)
    (t : G) (ht : orderOf t = 2) (htN : t ∈ normalizer (S : Set G)) :
    centralizer (centralizer (S : Set G) : Set G) = centralizer (S : Set G) := by
  let A := centralizer (S : Set G)
  obtain ⟨hinv, hcomm⟩ := h.seven_centralizer_inverted localData S hS t ht htN
  have h49 := h.seven_centralizer_card_ge localData S hS hne
  have hAcard : 1 < Nat.card A := by change 1 < Nat.card (centralizer (S : Set G)); omega
  let _ : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp hAcard
  have hCA_le : centralizer (A : Set G) ≤ A := by
    intro y hy
    obtain ⟨x, hx⟩ := exists_ne (1 : A)
    have hxA : (x : G) ∈ A := x.property
    have hxne : (x : G) ≠ 1 := by intro he; exact hx (Subtype.ext he)
    have hyx : y ∈ centralizer ({(x : G)} : Set G) :=
      mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hy (x : G) hxA).symm
    rw [h.seven_regular_centralizer localData S hS t ht htN (x : G) hxA hxne] at hyx
    exact hyx
  apply le_antisymm hCA_le
  intro y hy x hx
  exact congrArg Subtype.val
    (@Std.Commutative.comm _ (fun a b => a * b)
      (@IsMulCommutative.is_comm _ _ hcomm) (⟨y, hy⟩ : A) ⟨x, hx⟩).symm

private theorem seven_normalizer_factorization (S : Subgroup G)
    (hS : Nat.card S = 7) (hne : centralizer (S : Set G) ≠ S)
    (t : G) (ht : orderOf t = 2) (htN : t ∈ normalizer (S : Set G)) :
    ∀ n : G, n ∈ normalizer (centralizer (S : Set G) : Set G) →
      ∃ a ∈ centralizer (S : Set G),
        ∃ c ∈ normalizer (centralizer (S : Set G) : Set G) ⊓ centralizer ({t} : Set G),
          n = a * c := by
  let A := centralizer (S : Set G)
  let H := normalizer (A : Set G)
  obtain ⟨hinv, hcomm⟩ := h.seven_centralizer_inverted localData S hS t ht htN
  have htA : t ∈ H := Subgroup.normalizer_le_normalizer_centralizer S htN
  have hCA := h.seven_centralizer_self_centralizing localData S hS hne t ht htN
  have hAodd : Odd (Nat.card A) :=
    (h.seven_centralizer_coprime localData S hS).of_dvd_right
      (by norm_num : 2 ∣ (120 : ℕ)) |>.odd_of_right
  have hsq : Function.Bijective (fun x : A => x ^ 2) :=
    hAodd.coprime_two_right.pow_left_bijective
  intro n hn
  let nt : G := n * t * n⁻¹
  have hntH : nt ∈ H := by
    exact H.mul_mem (H.mul_mem hn htA) (H.inv_mem hn)
  have hntinv : ∀ x : G, x ∈ A → nt * x * nt⁻¹ = x⁻¹ := by
    intro x hx
    have hniff := (mem_normalizer_iff.mp hn)
    let y : G := n⁻¹ * x * n
    have hy : y ∈ A := by
      apply (hniff y).mpr
      change n * y * n⁻¹ ∈ A
      rw [show y = n⁻¹ * x * n by rfl]
      have heq : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
      rw [heq]
      exact hx
    have hiy := hinv y hy
    calc
      nt * x * nt⁻¹ = n * (t * y * t⁻¹) * n⁻¹ := by
        simp [nt, y]
        group
      _ = n * y⁻¹ * n⁻¹ := by rw [hiy]
      _ = x⁻¹ := by simp [y]
  have hnttA : nt * t ∈ A := by
    have hcentral : nt * t ∈ centralizer (A : Set G) := by
      intro x hx
      have h1 := hntinv (x⁻¹) (A.inv_mem hx)
      have h2 := hinv x hx
      have h1' : nt * x⁻¹ = x * nt := by
        simpa only [inv_inv] using mul_inv_eq_iff_eq_mul.mp h1
      have h2' : t * x = x⁻¹ * t := mul_inv_eq_iff_eq_mul.mp h2
      calc
        x * (nt * t) = (x * nt) * t := by group
        _ = (nt * x⁻¹) * t := by rw [h1']
        _ = nt * (x⁻¹ * t) := by group
        _ = nt * (t * x) := by rw [h2']
        _ = (nt * t) * x := by group
    have hCA' : centralizer (A : Set G) = A := by simpa [A] using hCA
    exact hCA' ▸ hcentral
  obtain ⟨b, hb⟩ := hsq.surjective (⟨nt * t, hnttA⟩ : A)
  let bG : G := b
  have hb2 : bG * bG = nt * t := by
    have hh := congrArg Subtype.val hb
    change ((b ^ 2 : A) : G) = nt * t at hh
    rw [pow_two] at hh
    change (b : G) * (b : G) = nt * t at hh
    simpa [bG] using hh
  let c : G := bG⁻¹ * n
  have hcH : c ∈ H := H.mul_mem (H.inv_mem (A.le_normalizer b.property)) hn
  have hct : c ∈ centralizer ({t} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have ht2 : t * t = 1 := by
      simpa only [pow_two] using (show t ^ 2 = 1 from ht ▸ pow_orderOf_eq_one t)
    have hbt : t * bG⁻¹ = bG * t := by
      have hh := hinv bG⁻¹ (A.inv_mem b.property)
      simpa only [inv_inv] using mul_inv_eq_iff_eq_mul.mp hh
    have hnt : nt = bG * bG * t := by
      calc
        nt = nt * 1 := by simp
        _ = nt * (t * t) := by rw [ht2]
        _ = (nt * t) * t := by group
        _ = (bG * bG) * t := by rw [hb2]
    have hbn : bG⁻¹ * nt = t * bG⁻¹ := by
      rw [hnt]
      calc
        bG⁻¹ * (bG * bG * t) = bG * t := by group
        _ = t * bG⁻¹ := hbt.symm
    calc
      c * t = bG⁻¹ * (n * t) := by simp [c, mul_assoc]
      _ = bG⁻¹ * nt * n := by simp [nt]; group
      _ = (t * bG⁻¹) * n := by rw [hbn]
      _ = t * c := by simp [c, mul_assoc]
  refine ⟨bG, ?_, c, ⟨hcH, hct⟩, ?_⟩
  · exact b.property
  · simp [c]

end CFSG.Quasithin.Janko1CentralizerData

namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {d : ℕ} (localData : BenderPrimeData G d)
include h localData

private theorem seven_complement_unique_involution (S : Subgroup G)
    (hS : Nat.card S = 7) (hne : centralizer (S : Set G) ≠ S)
    (t : G) (ht : orderOf t = 2) (htN : t ∈ normalizer (S : Set G))
    (u : G) (hu : orderOf u = 2)
    (huC : u ∈ normalizer (centralizer (S : Set G) : Set G) ⊓
      centralizer ({t} : Set G)) : u = t := by
  let A := centralizer (S : Set G)
  have hc := h.seven_centralizer_coprime localData S hS
  have hinvt := (h.seven_centralizer_inverted localData S hS t ht htN).1
  have hinvu := (h.involution_inverts_of_coprime A hc u hu huC.1).1
  have hCA := h.seven_centralizer_self_centralizing localData S hS hne t ht htN
  have hdisj : Disjoint A (centralizer ({t} : Set G)) := by
    apply disjoint_of_coprime_natCard
    rw [h.involution_centralizer_card t ht]
    exact hc
  have hprod : u * t ∈ A := by
    change u * t ∈ centralizer (S : Set G)
    rw [← hCA]
    intro x hx
    have hu' := mul_inv_eq_iff_eq_mul.mp (hinvu (x⁻¹) (A.inv_mem hx))
    have ht' := mul_inv_eq_iff_eq_mul.mp (hinvt x hx)
    simp only [inv_inv] at hu'
    calc
      x * (u * t) = (x * u) * t := by group
      _ = (u * x⁻¹) * t := by rw [hu']
      _ = u * (x⁻¹ * t) := by group
      _ = u * (t * x) := by rw [ht']
      _ = (u * t) * x := by group
  have hprodC : u * t ∈ centralizer ({t} : Set G) :=
    mul_mem huC.2 (mem_centralizer_singleton_iff.mpr (Commute.refl t))
  have hut : u * t = 1 := hdisj.le_bot ⟨hprod, hprodC⟩
  have ht2 : t * t = 1 := by
    simpa only [pow_two] using (show t ^ 2 = 1 from ht ▸ pow_orderOf_eq_one t)
  exact mul_right_cancel (hut.trans ht2.symm)

private theorem seven_complement_three_dvd (S : Subgroup G)
    (hS : Nat.card S = 7) (hne : centralizer (S : Set G) ≠ S)
    (t : G) (ht : orderOf t = 2) (htN : t ∈ normalizer (S : Set G))
    (x : G) (hxH : x ∈ normalizer (centralizer (S : Set G) : Set G))
    (hx3 : orderOf x = 3) :
    3 ∣ Nat.card (normalizer (centralizer (S : Set G) : Set G) ⊓
      centralizer ({t} : Set G) : Subgroup G) := by
  let A := centralizer (S : Set G)
  let H := normalizer (A : Set G)
  let C := H ⊓ centralizer ({t} : Set G)
  have hdisj : Disjoint A C := by
    apply Disjoint.mono_right (show C ≤ centralizer ({t} : Set G) from inf_le_right)
    apply disjoint_of_coprime_natCard
    rw [h.involution_centralizer_card t ht]
    exact h.seven_centralizer_coprime localData S hS
  let f : A × C → H := fun ac =>
    ⟨ac.1 * ac.2, H.mul_mem (A.le_normalizer ac.1.property) ac.2.property.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b he
      exact mul_injective_of_disjoint hdisj (congrArg Subtype.val he)
    · intro n
      obtain ⟨a, ha, c, hc, hn⟩ :=
        h.seven_normalizer_factorization localData S hS hne t ht htN n n.property
      exact ⟨(⟨a, ha⟩, ⟨c, hc⟩), Subtype.ext hn.symm⟩
  have hcard : Nat.card A * Nat.card C = Nat.card H :=
    (Nat.card_prod A C).symm.trans (Nat.card_congr (Equiv.ofBijective f hf))
  have h3 : 3 ∣ Nat.card H := hx3 ▸ H.orderOf_dvd_natCard hxH
  rw [← hcard] at h3
  exact (Nat.Prime.dvd_mul (by decide : Nat.Prime 3)).mp h3 |>.resolve_left
    (h.seven_centralizer_small_primes localData S hS).2.1

end CFSG.Quasithin.Janko1CentralizerData


namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) {d : ℕ} (localData : BenderPrimeData G d)
include h localData

private theorem seven_complement_card (S : Subgroup G)
    (hS : Nat.card S = 7) (hne : centralizer (S : Set G) ≠ S)
    (t : G) (ht : orderOf t = 2) (htN : t ∈ normalizer (S : Set G))
    (h3 : 3 ∣ Nat.card (normalizer (centralizer (S : Set G) : Set G) ⊓
      centralizer ({t} : Set G) : Subgroup G)) :
    Nat.card (normalizer (centralizer (S : Set G) : Set G) ⊓
      centralizer ({t} : Set G) : Subgroup G) = 6 := by
  let A := centralizer (S : Set G)
  let C := normalizer (A : Set G) ⊓ centralizer ({t} : Set G)
  have htC : t ∈ C := ⟨normalizer_le_normalizer_centralizer S htN,
    mem_centralizer_singleton_iff.mpr (Commute.refl t)⟩
  obtain ⟨g, hg⟩ := h.involutions_conjugate t ht
  let e := MulAut.conj g
  have he : e t = h.z := hg
  let ec : centralizer ({t} : Set G) ≃* centralizer ({h.z} : Set G) :=
    { e.toEquiv.subtypeEquiv (fun y => by
        rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← he]
        change y * t = t * y ↔ e y * e t = e t * e y
        rw [← map_mul, ← map_mul, e.injective.eq_iff]) with
      map_mul' := by intro x y; apply Subtype.ext; exact e.map_mul x y }
  let f : C →* A5 × C2 := h.alternatingCentralizerEquiv.toMonoidHom.comp
    (ec.toMonoidHom.comp (inclusion (show C ≤ centralizer ({t} : Set G) from inf_le_right)))
  have hf : Function.Injective f := by
    intro x y hxy
    exact inclusion_injective inf_le_right
      (ec.injective (h.alternatingCentralizerEquiv.injective hxy))
  have hft : (f ⟨t, htC⟩).1 = 1 := by
    have hzt : ec ⟨t, htC.2⟩ = ⟨h.z, h.z_mem_centralizer⟩ := Subtype.ext hg
    change (h.alternatingCentralizerEquiv (ec ⟨t, htC.2⟩)).1 = 1
    rw [hzt, h.alternatingCentralizerEquiv_z]
  apply complement_card_of_model f hf (ht ▸ C.orderOf_dvd_natCard htC) h3
  intro u hu
  have hut := h.seven_complement_unique_involution localData S hS hne t ht htN
    u ((orderOf_coe u).trans hu) u.property
  have hue : u = ⟨t, htC⟩ := Subtype.ext hut
  simpa only [hue] using hft

/-- The full local structure used in Bender (4.3), under its contrary-case
assumption. The complement is the literal intersection in the source. -/
public theorem bender_seven_structure (S : Subgroup G)
    (hSN : S ≤ normalizer (h.sylow : Set G)) (hS : Nat.card S = 7)
    (heven : Even (Nat.card (normalizer (S : Set G))))
    (hne : centralizer (S : Set G) ≠ S) : Nonempty (BenderSevenStructure h S) := by
  obtain ⟨tN, htN⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (S : Set G))
    2 (even_iff_two_dvd.mp heven)
  let t : G := tN
  have ht : orderOf t = 2 := (orderOf_coe tN).trans htN
  have htS : t ∈ normalizer (S : Set G) := tN.property
  obtain ⟨x, hxN, hxS, hx3⟩ := h.exists_order_three_normalizing_seven S hS hSN
  have hxH := normalizer_le_normalizer_centralizer S hxS
  have h3 := h.seven_complement_three_dvd localData S hS hne t ht htS x hxH hx3
  have hc := h.seven_complement_card localData S hS hne t ht htS h3
  let C := normalizer (centralizer (S : Set G) : Set G) ⊓ centralizer ({t} : Set G)
  have hcyc : IsCyclic C := by
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 h3
    have htC : t ∈ C := ⟨normalizer_le_normalizer_centralizer S htS,
      mem_centralizer_singleton_iff.mpr (Commute.refl t)⟩
    let tC : C := ⟨t, htC⟩
    have htCo : orderOf tC = 2 := (orderOf_coe tC).symm.trans ht
    have hyt : Commute y tC := by
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp y.property.2
    apply isCyclic_of_orderOf_eq_card (y * tC)
    rw [hyt.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hy, htCo]; decide), hy, htCo]
    exact hc.symm
  exact ⟨{
    t := t
    involution := ht
    normalizes := htS
    centralizers := h.seven_regular_centralizer localData S hS t ht htS
    factorization := h.seven_normalizer_factorization localData S hS hne t ht htS
    complement_card := hc
    complement_cyclic := hcyc
    three_in_sylow_normalizer := ⟨x, hxN, hxH, hx3⟩ }⟩

end CFSG.Quasithin.Janko1CentralizerData
