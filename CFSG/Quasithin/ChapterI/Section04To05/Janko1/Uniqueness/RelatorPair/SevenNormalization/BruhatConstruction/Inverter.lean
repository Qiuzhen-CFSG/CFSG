module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenNormalization.BruhatConstruction.FifthPower
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Localization
public import Theory.GroupTheory.PrimeSubgroupInvolution

/-!
# An inverting involution in the seven-normalizer

The odd-prime centralizer structure bounds every cubic and quintic
centralizer by order thirty. Consequently C_G(Y), for Y = ⟨y⟩ of order
seven, has order coprime to 120. Conjugation embeds N_G(Y)/C_G(Y) into
Aut(Y), of order six. The supplied group order and the Sylow seven
congruence then force |N_G(Y)| = 42 and C_G(Y) = Y.

Inside this normalizer, the normalizer of the marked cubic subgroup has
even order by the Sylow three congruence. It contains an involution w.
The abelian automorphism group of Y shows that conjugation by w fixes u:
the difference lies both in ⟨u⟩ and the action kernel Y. Finally w cannot
centralize Y because its full involution centralizer has order 120; the
prime-subgroup involution dichotomy therefore makes w invert Y.

The sole additional structural premise is OddPrimeCentralizerStructure h,
whose independent producer is the existing odd-prime centralizer task.
No involution counts, recognition, generation, or representation hypotheses
are needed. The proof in fact works for every supplied NormalizerFrame.

Source: Gorenstein, *Finite Groups*, §16.6, pp.482–483, the configuration
preceding equation (6.2); Bender (1974), §4, (4.1) for the odd-prime input.
The numerical Sylow argument here uses the supplied source order 175560.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1RelatorPair.SevenNormalization
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
  (h : Janko1CentralizerData G)
  (s : Janko1CentralizerData.OddPrimeCentralizerStructure h)
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

omit [IsSimpleGroup G] in
include s in
/-- The local cyclic-complement structure bounds every ambient cubic and
quintic centralizer. Sylow conjugacy removes the local restriction. -/
public theorem ambient_prime_centralizer_card_dvd (p : ℕ) (hp : p = 3 ∨ p = 5)
    (x : G) (hx : orderOf x = p) : Nat.card (centralizer ({x} : Set G)) ∣ 30 := by
  obtain ⟨g, hg⟩ := h.exists_conj_mem_centralizer_of_sylow_card p hp (s.sylow_card p hp) x hx
  let e := MulAut.conj g
  have he : Nat.card (centralizer ({x} : Set G)) =
      Nat.card (centralizer ({e x} : Set G)) := by
    apply Nat.card_congr
    exact e.toEquiv.subtypeEquiv (fun y => by
      rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
      change y * x = x * y ↔ e y * e x = e x * e y
      rw [← map_mul, ← map_mul, e.injective.eq_iff])
  rw [he]
  rcases s.centralizer_card_cases p hp (e x) hg ((e.orderOf_eq x).trans hx) with hc | hc
  · rw [hc]
    rcases hp with rfl | rfl <;> decide
  · rw [hc]

include s in
private theorem seven_centralizer_coprime_of_structure (Y : Subgroup G)
    (hY : Nat.card Y = 7) : Nat.Coprime (Nat.card (centralizer (Y : Set G))) 120 := by
  let A := centralizer (Y : Set G)
  have hd (x : A) : 7 ∣ Nat.card (centralizer ({(x : G)} : Set G)) := by
    rw [← hY]
    apply card_dvd_of_le
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (x.property y hy)
  have no (p : ℕ) [Fact p.Prime]
      (hc : ∀ x : G, orderOf x = p → ¬ 7 ∣ Nat.card (centralizer ({x} : Set G))) :
      ¬ p ∣ Nat.card A := by
    intro hp
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) p hp
    exact hc x ((orderOf_injective A.subtype A.subtype_injective x).trans hx) (hd x)
  have h2 : ¬ 2 ∣ Nat.card A := no 2 (by
    intro x hx
    rw [h.involution_centralizer_card x hx]
    decide)
  have h3 : ¬ 3 ∣ Nat.card A := no 3 (by
    intro x hx hx7
    have := hx7.trans (ambient_prime_centralizer_card_dvd h s 3 (Or.inl rfl) x hx)
    norm_num at this)
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h5 : ¬ 5 ∣ Nat.card A := no 5 (by
    intro x hx hx7
    have := hx7.trans (ambient_prime_centralizer_card_dvd h s 5 (Or.inr rfl) x hx)
    norm_num at this)
  have c2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm
  have c3 := ((show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr h3).symm
  have c5 := ((show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr h5).symm
  exact (c2.pow_right 3).mul_right (c3.mul_right c5)

omit [IsSimpleGroup G] in
/-- The marked order-21 subgroup normalizes its actual seven-subgroup. -/
public theorem NormalizerFrame.le_seven_normalizer (D : NormalizerFrame h) :
    D.H ≤ normalizer (zpowers D.y : Set G) := by
  rw [← D.generated]
  apply sup_le (zpowers D.y).le_normalizer
  apply zpowers_le.mpr
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change zpowers (D.u * D.y * D.u⁻¹) = zpowers D.y
  rw [D.action]
  apply le_antisymm (zpowers_le.mpr (pow_mem (mem_zpowers _) _))
  apply zpowers_le.mpr
  rw [mem_zpowers_pow_iff, D.order_y]
  decide

private theorem normalizer_arithmetic : ∀ n ∈ (8778 : ℕ).divisors,
    21 ∣ n → (175560 / n) % 7 = 1 → n = 42 := by decide +kernel

include s in
/-- The source order and the odd-prime centralizer bounds force the
normalizer of the marked seven-subgroup to have order forty-two. -/
public theorem NormalizerFrame.seven_normalizer_card (D : NormalizerFrame h)
    (horder : Nat.card G = 175560) :
    Nat.card (normalizer (zpowers D.y : Set G)) = 42 := by
  let Y := zpowers D.y
  let N := normalizer (Y : Set G)
  have hY : Nat.card Y = 7 := (Nat.card_zpowers D.y).trans D.order_y
  have hCY : Nat.card (centralizer (Y : Set G)) ∣ 1463 := by
    have hc := (centralizer (Y : Set G)).card_subgroup_dvd_card
    rw [horder] at hc
    exact (seven_centralizer_coprime_of_structure h s Y hY).dvd_of_dvd_mul_left hc
  let f := Y.normalizerMonoidHom
  have hrange : Nat.card f.range ∣ 6 := by
    have hd := f.range.card_subgroup_dvd_card
    rwa [IsCyclic.card_mulAut, hY, show Nat.totient 7 = 6 by decide] at hd
  have hker : Nat.card f.ker ∣ 1463 := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (Y : Set G))).toEquiv]
    exact hCY
  have hNdiv : Nat.card N ∣ 8778 := by
    rw [← f.ker.card_mul_index, index_ker]
    exact Nat.mul_dvd_mul hker hrange
  have h21 : 21 ∣ Nat.card N := D.card_H ▸ card_dvd_of_le (D.le_seven_normalizer h)
  have hYmax : Nat.card Y = 7 ^ (Nat.card G).factorization 7 := by
    rw [hY, horder]
    decide +kernel
  let P := Sylow.ofCard Y hYmax
  have hm : N.index % 7 = 1 := by
    have hm := card_sylow_modEq_one 7 G
    rw [P.card_eq_index_normalizer] at hm
    exact hm
  have hindex : N.index = 175560 / Nat.card N := by
    rw [← horder, ← N.card_mul_index, Nat.mul_div_cancel_left _ (Nat.card_pos (α := N))]
  rw [hindex] at hm
  exact normalizer_arithmetic (Nat.card N) (Nat.mem_divisors.mpr ⟨hNdiv, by decide⟩) h21 hm

include s in
/-- The marked seven-subgroup is self-centralizing in the ambient group. -/
public theorem NormalizerFrame.seven_centralizer_eq (D : NormalizerFrame h)
    (horder : Nat.card G = 175560) :
    centralizer (zpowers D.y : Set G) = zpowers D.y := by
  have hY : Nat.card (zpowers D.y) = 7 := (Nat.card_zpowers D.y).trans D.order_y
  have hd := card_dvd_of_le (centralizer_le_normalizer (zpowers D.y : Set G))
  rw [D.seven_normalizer_card h s horder] at hd
  have hc6 : Nat.Coprime (Nat.card (centralizer (zpowers D.y : Set G))) 6 :=
    (seven_centralizer_coprime_of_structure h s (zpowers D.y) hY).of_dvd_right (by decide)
  have hc7 : Nat.card (centralizer (zpowers D.y : Set G)) ∣ 7 :=
    hc6.dvd_of_dvd_mul_left hd
  apply (eq_of_le_of_card_ge (Subgroup.le_centralizer (zpowers D.y)) ?_).symm
  rw [hY]
  exact Nat.le_of_dvd (by decide) hc7

private theorem cubic_normalizer_arithmetic : ∀ n ∈ (42 : ℕ).divisors,
    3 ∣ n → (42 / n) % 3 = 1 → 2 ∣ n := by decide +kernel

include s in
/-- Construct an involution centralizing the marked cubic generator and
inverting the seven-generator. No representation or product relation is assumed. -/
public theorem NormalizerFrame.exists_inverter (D : NormalizerFrame h)
    (horder : Nat.card G = 175560) :
    ∃ w : G, orderOf w = 2 ∧ Commute w D.u ∧ w * D.y * w⁻¹ = D.y⁻¹ := by
  let Y := zpowers D.y
  let N := normalizer (Y : Set G)
  have hY : Nat.card Y = 7 := (Nat.card_zpowers D.y).trans D.order_y
  have hN : Nat.card N = 42 := D.seven_normalizer_card h s horder
  let u : N := ⟨D.u, D.le_seven_normalizer h D.u_mem⟩
  have hu : orderOf u = 3 := (N.orderOf_coe u).symm.trans D.order_u
  let U := zpowers u
  have hU : Nat.card U = 3 := (Nat.card_zpowers u).trans hu
  let M := normalizer (U : Set N)
  have hMdiv : Nat.card M ∣ 42 := hN ▸ M.card_subgroup_dvd_card
  have h3div : 3 ∣ Nat.card M := hU ▸ card_dvd_of_le U.le_normalizer
  have hUmax : Nat.card U = 3 ^ (Nat.card N).factorization 3 := by
    rw [hU, hN]
    decide +kernel
  let P := Sylow.ofCard U hUmax
  have hm : M.index % 3 = 1 := by
    have hm := card_sylow_modEq_one 3 N
    rw [P.card_eq_index_normalizer] at hm
    exact hm
  have hindex : M.index = 42 / Nat.card M := by
    rw [← hN, ← M.card_mul_index, Nat.mul_div_cancel_left _ (Nat.card_pos (α := M))]
  rw [hindex] at hm
  have heven : 2 ∣ Nat.card M := cubic_normalizer_arithmetic (Nat.card M)
    (Nat.mem_divisors.mpr ⟨hMdiv, by decide⟩) h3div hm
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := M) 2 heven
  have hwN : orderOf (w : N) = 2 := (M.orderOf_coe w).trans hw
  have hwG : orderOf ((w : N) : G) = 2 := (N.orderOf_coe (w : N)).trans hwN
  have hinv : (w : N) * u * (w : N)⁻¹ ∈ U :=
    (mem_normalizer_iff.mp w.property u).mp (mem_zpowers u)
  let f := Y.normalizerMonoidHom
  let _ := (IsCyclic.mulAutMulEquiv Y).toMonoidHom.commGroupOfInjective
    (IsCyclic.mulAutMulEquiv Y).injective
  have hf : f ((w : N) * u * (w : N)⁻¹) = f u := by
    rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul]
    exact mul_comm _ _
  have hk : u⁻¹ * ((w : N) * u * (w : N)⁻¹) ∈ f.ker := f.eq_iff.mp hf
  have hdisj : Disjoint U (Y.subgroupOf N) := by
    apply disjoint_of_coprime_natCard
    rw [hU, Nat.card_congr (subgroupOfEquivOfLe Y.le_normalizer).toEquiv, hY]
    decide
  have h1 : u⁻¹ * ((w : N) * u * (w : N)⁻¹) = 1 := by
    apply disjoint_def.mp hdisj (U.mul_mem (U.inv_mem (mem_zpowers u)) hinv)
    have hCY : centralizer (Y : Set G) = Y := D.seven_centralizer_eq h s horder
    simpa only [f, normalizerMonoidHom_ker, hCY] using hk
  have hcomm : Commute ((w : N) : G) D.u := by
    have he := inv_mul_eq_one.mp h1
    have heG := congrArg Subtype.val he
    exact mul_inv_eq_iff_eq_mul.mp heG.symm
  refine ⟨w, hwG, hcomm, ?_⟩
  rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one Y (by rw [hY]; decide)
    w (by simpa only [hwG] using pow_orderOf_eq_one ((w : N) : G)) (w : N).property with hc | hi
  · have hd : 7 ∣ Nat.card (centralizer ({((w : N) : G)} : Set G)) := by
      rw [← hY]
      apply card_dvd_of_le
      intro y hy
      exact mem_centralizer_singleton_iff.mpr (hc y hy).symm.eq
    rw [h.involution_centralizer_card _ hwG] at hd
    norm_num at hd
  · exact hi D.y (mem_zpowers D.y)

end CFSG.Quasithin.Janko1RelatorPair.SevenNormalization
