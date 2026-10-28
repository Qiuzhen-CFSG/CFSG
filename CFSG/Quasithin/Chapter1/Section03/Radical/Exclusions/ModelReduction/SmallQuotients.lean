module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Normalization
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Sylow
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import GorensteinWalter.PSL2Cardinality

/-!
# Excluding the A₅ and L₂(7) quotients in the swapped case

The actual image of XT ∩ K in K/O₂(K) is solvable. It contains a Sylow
two-subgroup and the injective image of P ∩ K, whose order is p > 3.
For quotient order 60 or 168 this forces the solvable subgroup to have
index at most three. The faithful coset action of a simple group excludes
that index. Thus the A₅-block and L₂(7) possibilities are impossible.

Solvability is inherited from the actual product XT = PT = TP, through
`SwappedSylow.local_solvable`; no permutability or small-model exclusion
is assumed. The two concrete corollaries transport the existing A₅ and
PSL₂(7) order formulas through their specified multiplicative equivalences.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.8, printed p.514. The small-index coset argument
uses the attributed ATLAS port `SmallIndexSimple`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open XiEmbedding

private theorem prime_eq_of_dvd {p r a : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hp3 : 3 < p) (hdiv : p ∣ 2 ^ a * 3 * r) : p = r := by
  rcases hp.dvd_mul.mp hdiv with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · have he := (Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
      omega
    · have he := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp h
      omega
  · exact (Nat.prime_dvd_prime_iff_eq hp hr).mp h

private theorem no_small_solvable_sylow_overgroup {Q : Type*} [Group Q] [Finite Q]
    [IsSimpleGroup Q] [Group.IsPerfect Q] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hq : Nat.card Q = 60 ∨ Nat.card Q = 168)
    (S : Sylow 2 Q) (J : Subgroup Q) [Group.IsSolvable J]
    (hSJ : (S : Subgroup Q) ≤ J) (hpJ : p ∣ Nat.card J) : False := by
  have hpQ := hpJ.trans J.card_subgroup_dvd_card
  have hidx : J.index ≤ 3 := by
    have hj := J.card_mul_index
    rcases hq with hq | hq
    · have hp5 : p = 5 := prime_eq_of_dvd (a := 2) hp (by decide) hp3 (by simpa [hq] using hpQ)
      have hfour : 4 ∣ Nat.card J :=
        (S.pow_dvd_card_of_pow_dvd_card (n := 2) (by norm_num [hq])).trans (card_dvd_of_le hSJ)
      have h20 : 20 ∣ Nat.card J :=
        (show Nat.Coprime 4 5 by decide).mul_dvd_of_dvd_of_dvd hfour (hp5 ▸ hpJ)
      have hpos := Nat.card_pos (α := J)
      have hle := Nat.le_of_dvd hpos h20
      rw [hq] at hj
      nlinarith
    · have hp7 : p = 7 := prime_eq_of_dvd (a := 3) hp (by decide) hp3 (by simpa [hq] using hpQ)
      have height : 8 ∣ Nat.card J :=
        (S.pow_dvd_card_of_pow_dvd_card (n := 3) (by norm_num [hq])).trans (card_dvd_of_le hSJ)
      have h56 : 56 ∣ Nat.card J :=
        (show Nat.Coprime 8 7 by decide).mul_dvd_of_dvd_of_dvd height (hp7 ▸ hpJ)
      have hpos := Nat.card_pos (α := J)
      have hle := Nat.le_of_dvd hpos h56
      rw [hq] at hj
      nlinarith
  have he : J = ⊤ := Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt J (by
    have hh := Nat.factorial_le hidx
    norm_num at hh
    rcases hq with hq | hq <;> omega)
  have hsolv : Group.IsSolvable Q := Group.isSolvable_of_surjective
    (f := J.subtype) (by rw [he]; exact topEquiv.surjective)
  exact Group.IsPerfect.not_isSolvable Q hsolv

variable {G : Type*} [Group G] [Finite G]

/-- The actual solvable local image excludes both small simple quotient orders. -/
theorem ComponentCandidate.not_small_quotient_card
    {κ : GroupClass} {p : ℕ} {T X P M H₀ K : Subgroup G}
    (h : ComponentCandidate κ p T X P M H₀ K)
    (hp3 : 3 < p) (hswap : SwappedFactors T P K)
    (hm : SwappedModel p (XiQuotient K)) :
    Nat.card (XiQuotient K) ≠ 60 ∧ Nat.card (XiQuotient K) ≠ 168 := by
  let _ : Fact p.Prime := ⟨h.local_input.prime⟩
  let _ := h.quasisimple
  let _ := swappedModel_simple h.quasisimple hm
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := ((X ⊔ T) ⊓ K).subgroupOf K
  let J := B.map q
  let A := (P ⊓ K).subgroupOf K
  let _ := SwappedSylow.local_solvable h.local_input
  let _ : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := (inclusion (show (X ⊔ T) ⊓ K ≤ X ⊔ T from inf_le_left)).comp
      (subgroupOfEquivOfLe (show (X ⊔ T) ⊓ K ≤ K from inf_le_right)).toMonoidHom)
    ((inclusion_injective inf_le_left).comp (subgroupOfEquivOfLe inf_le_right).injective)
  let _ : Group.IsSolvable J := Group.isSolvable_of_surjective (q.subgroupMap_surjective B)
  obtain ⟨U, hU⟩ := Section02.IndexTwo.isSylowIn_inf_of_subnormal h.sylow_two
    h.component.1 h.component.2.subnormal
  let S := U.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hS : (S : Subgroup (XiQuotient K)) ≤ J := by
    rw [Sylow.coe_mapSurjective]
    apply map_mono
    have hh : (U : Subgroup K) = (T ⊓ K).subgroupOf K := by
      simpa only [Subgroup.subgroupOf, comap_map_eq_self_of_injective K.subtype_injective] using
        congrArg (fun Z : Subgroup G => Z.subgroupOf K) hU
    rw [hh]
    exact comap_mono (inf_le_inf_right K le_sup_right)
  have hA : Nat.card A = p :=
    (Nat.card_congr (subgroupOfEquivOfLe (show P ⊓ K ≤ K from inf_le_right)).toEquiv).trans
      (swapped_intersection_card h.alternatives.1 hswap)
  have hdis : Disjoint A (pCore 2 K) :=
    (h.local_input.odd_complement.isPGroup.to_le inf_le_left).comap_subtype.disjoint_of_coprime
      pCore_isPGroup (Nat.coprime_two_right.mpr h.local_input.odd)
  have hi : Function.Injective (q.comp A.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    have hh : (a : K) ∈ pCore 2 K := (QuotientGroup.eq_one_iff _).mp ha
    exact Subtype.ext (hdis.le_bot ⟨a.property, hh⟩)
  have hcard : Nat.card (A.map q) = p := by
    calc
      Nat.card (A.map q) = Nat.card (q.comp A.subtype).range := by
        rw [MonoidHom.range_comp, range_subtype]
      _ = Nat.card A := (Nat.card_congr (Equiv.ofInjective (q.comp A.subtype) hi)).symm
      _ = p := hA
  have hpJ : p ∣ Nat.card J := by
    rw [← hcard]
    exact card_dvd_of_le (map_mono (comap_mono (inf_le_inf_right K
      (h.local_input.complement_le.trans le_sup_left))))
  have hh : ¬ (Nat.card (XiQuotient K) = 60 ∨ Nat.card (XiQuotient K) = 168) :=
    fun hq => no_small_solvable_sylow_overgroup h.local_input.prime hp3 hq S J hS hpJ
  exact not_or.mp hh


/-- The A₅ natural permutation block cannot occur in the swapped alternative. -/
theorem ComponentCandidate.not_alternatingFiveBlock
    {κ : GroupClass} {p : ℕ} {T X P M H₀ K : Subgroup G}
    (h : ComponentCandidate κ p T X P M H₀ K)
    (hp3 : 3 < p) (hswap : SwappedFactors T P K)
    (hm : SwappedModel p (XiQuotient K)) : ¬ ChapterC.IsAlternatingBlock K 5 := by
  intro hblock
  obtain ⟨e⟩ := hblock.2.2.quotient_iso
  apply (h.not_small_quotient_card hp3 hswap hm).1
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The exceptional overlap L₂(7) = L₃(2) is also impossible. -/
theorem ComponentCandidate.not_linearSeven
    {κ : GroupClass} {p : ℕ} {T X P M H₀ K : Subgroup G}
    (h : ComponentCandidate κ p T X P M H₀ K)
    (hp3 : 3 < p) (hswap : SwappedFactors T P K)
    (hm : SwappedModel p (XiQuotient K)) : ¬ ClassicalGroup.IsPSL (XiQuotient K) 2 7 := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  apply (h.not_small_quotient_card hp3 hswap hm).2
  rw [Nat.card_congr e.toEquiv]
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨7, 1, by decide, by decide, by decide, by simpa using hF⟩
  have hc := GorensteinWalter.psl2_card_formula F hodd
  norm_num [hF] at hc
  exact hc

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
