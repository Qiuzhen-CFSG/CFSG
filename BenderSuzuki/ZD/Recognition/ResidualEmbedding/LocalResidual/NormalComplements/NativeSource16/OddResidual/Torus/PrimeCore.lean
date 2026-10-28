module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.CoprimeGeneration
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.MarkedField
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Prime cores of the actual square-field tori

A cyclic torus of order 2^(2m)-1 has a nontrivial p-core for every prime
p dividing 2^m+1. Its p-core order divides that latter factor. Hence the
square-root field power is inversion on the p-core. Characteristicness
preserves the original actor action, and odd-order squaring shows that the
t-core commutator is the whole p-core when t inverts the torus.

This supplies the literal R₀=Oₚ(D∩F) used in GLS IV, Chapter 2, Proposition
16.5, refs/KGroup/GLS4/Chapter2.tex, lines 2935–2948. Torus cyclicity,
order, normalization and power action are the preceding marked model facts.
-/

noncomputable section
namespace BenderSuzuki.ZD.NativeSource16
open Subgroup Theory.GroupTheory
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]

public theorem prime_dividing_binary_succ_odd {m p : ℕ}
    (hm : 0 < m) (_hp : p.Prime) (hdiv : p ∣ 2 ^ m + 1) : Odd p := by
  have he : Even (2 ^ m) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  exact (he.add_odd (by decide : Odd 1)).of_dvd_nat hdiv

private theorem pCore_ne_bot_of_cyclic (T : Subgroup G) [IsCyclic T]
    {p : ℕ} [Fact p.Prime] (hdiv : p ∣ Nat.card T) : T.pCoreIn p ≠ ⊥ := by
  let : IsMulCommutative T := inferInstance
  let : CommGroup T := IsMulCommutative.instCommGroup
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := T) p hdiv
  have hxp : IsPGroup p (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  have hle : zpowers x ≤ pCore p T := le_sSup ⟨inferInstance, hxp⟩
  intro he
  have hxQ : (x : G) ∈ T.pCoreIn p := ⟨x, hle (mem_zpowers x), rfl⟩
  rw [he, mem_bot] at hxQ
  have hx1 : x = 1 := Subtype.ext hxQ
  have hh := (Fact.out : p.Prime).ne_one
  apply hh
  simpa only [hx1, orderOf_one] using hx.symm

private theorem pCore_card_dvd_succ (T : Subgroup G) {m p : ℕ}
    (hm : 0 < m) (hp : p.Prime) (hpdiv : p ∣ 2 ^ m + 1)
    (hT : Nat.card T = (2 ^ m - 1) * (2 ^ m + 1)) :
    Nat.card (T.pCoreIn p) ∣ 2 ^ m + 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hr : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
  have htwo : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    omega
  have hcop : Nat.Coprime p (2 ^ m - 1) := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    have hd2 : p ∣ 2 := by
      have hh := Nat.dvd_sub hpdiv hd
      convert hh using 1
      omega
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hd2 |>.resolve_left hp.ne_one))
  obtain ⟨k, hk⟩ := (isPGroup_pCoreIn p T).exists_card_eq
  have hdiv : p ^ k ∣ (2 ^ m - 1) * (2 ^ m + 1) := by
    rw [← hk, ← hT]
    exact card_dvd_of_le (pCoreIn_le p T)
  rw [hk]
  exact (hcop.pow_left k).dvd_of_dvd_mul_left hdiv

private theorem full_commutator_of_odd_inverted (Q : Subgroup G)
    (hodd : Odd (Nat.card Q)) (t : G)
    (hinv : ∀ x ∈ Q, t * x * t⁻¹ = x⁻¹) : ⁅Q, zpowers t⁆ = Q := by
  have hn : t ∈ normalizer (Q : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      change t * x * t⁻¹ ∈ Q
      rw [hinv x hx]
      exact Q.inv_mem hx
    · rw [card_map_of_injective (MulAut.conj t).injective]
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hn))
  intro y hy
  obtain ⟨x, hx⟩ := hodd.coprime_two_right.pow_left_bijective.surjective (⟨y, hy⟩ : Q)
  have hc : ⁅(x : G), t⁆ = (x : G) ^ 2 := by
    rw [commutatorElement_def]
    calc
      (x : G) * t * (x : G)⁻¹ * t⁻¹ = (x : G) * (t * (x : G)⁻¹ * t⁻¹) := by group
      _ = (x : G) ^ 2 := by rw [hinv _ (Q.inv_mem x.property), inv_inv, pow_two]
  have hh := commutator_mem_commutator x.property (mem_zpowers t)
  rw [hc] at hh
  have he : (x : G) ^ 2 = y := congrArg (fun a : Q => (a : G)) hx
  rwa [← he]

/-- The actual torus p-core has all the source operator properties used in
16.5. The order and square-root power inputs come from the marked linear model. -/
public theorem torus_pCore_profile
    (D A T : Subgroup G) (t w v : G) {m p : ℕ}
    (hm : 0 < m) (hp : p.Prime) (hpdiv : p ∣ 2 ^ m + 1)
    (hTcyc : IsCyclic T) (hTcard : Nat.card T = 2 ^ (2 * m) - 1)
    (hTD : T ≤ D) (hAT : A ≤ normalizer (T : Set G))
    (hTw : T ≤ centralizer ({w} : Set G))
    (hTv : ∀ x ∈ T, v * x * v⁻¹ = x ^ (2 ^ m))
    (hTt : ∀ x ∈ T, t * x * t⁻¹ = x⁻¹) :
    let Q := T.pCoreIn p
    Q ≠ ⊥ ∧ IsPGroup p Q ∧ Q ≤ D ∧ A ≤ normalizer (Q : Set G) ∧
      Q ≤ centralizer ({w} : Set G) ∧
      (∀ x ∈ Q, v * x * v⁻¹ = x⁻¹) ∧ ⁅Q, zpowers t⁆ = Q := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic T := hTcyc
  have hfac : Nat.card T = (2 ^ m - 1) * (2 ^ m + 1) := by
    rw [hTcard, mul_comm 2 m, pow_mul]
    have hpos : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
    have hsub : 2 ^ m - 1 + 1 = 2 ^ m := Nat.sub_add_cancel hpos
    have hpos2 : 1 ≤ (2 ^ m) ^ 2 := by nlinarith
    have hs2 := Nat.sub_add_cancel hpos2
    nlinarith
  have hdiv : p ∣ Nat.card T := by
    rw [hfac]
    exact dvd_mul_of_dvd_right hpdiv _
  have hQodd : Odd (Nat.card (T.pCoreIn p)) := by
    obtain ⟨k, hk⟩ := (isPGroup_pCoreIn p T).exists_card_eq
    rw [hk]
    exact (prime_dividing_binary_succ_odd hm hp hpdiv).pow
  refine ⟨pCore_ne_bot_of_cyclic T hdiv, isPGroup_pCoreIn p T,
    (pCoreIn_le p T).trans hTD,
    hAT.trans (normalizer_le_normalizer_characteristic_image T (pCore p T)),
    (pCoreIn_le p T).trans hTw, ?_,
    full_commutator_of_odd_inverted _ hQodd t (fun x hx => hTt x (pCoreIn_le p T hx))⟩
  intro x hx
  rw [hTv x (pCoreIn_le p T hx)]
  have hpow : x ^ (2 ^ m + 1) = 1 := by
    have hh : x ^ Nat.card (T.pCoreIn p) = 1 := congrArg Subtype.val
      (pow_card_eq_one' (x := (⟨x, hx⟩ : T.pCoreIn p)))
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_of_pow_eq_one hh).trans (pCore_card_dvd_succ T hm hp hpdiv hfac))
  exact eq_inv_of_mul_eq_one_left (by simpa only [pow_succ] using hpow)

end BenderSuzuki.ZD.NativeSource16
