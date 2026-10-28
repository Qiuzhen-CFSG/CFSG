module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.BorelLift
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.PrimeRankZero

/-!
# The rank-one normalizer input to 13.7.5(5)

The literal K* ≃ PSL₂(4) image has order sixty. Its two-group kernel
preserves the three-part, so every subgroup of K has three-rank at most
one. The local L₁ quotient supplies a factor three in its containing
normalizer. This proves rank exactly one before applying the universal
earlier chapter conclusion; no overlap geometry is assumed.

Source: Aschbacher–Smith, 13.7.5(5), printed p.938, and the last paragraph
of the proof of 13.8.20, printed p.955.
-/

open Subgroup
open CFSG.Quasithin.Chapter13.Section08
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction
open Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction
variable {G : Type*} [Group G] [Finite G]

private theorem nine_not_dvd_component (H K : Subgroup G) (hKH : K ≤ H)
    (e : Source.starImage H K ≃* alternatingGroup (Fin 5)) :
    ¬ 9 ∣ Nat.card K := by
  let f := starHom H K hKH
  obtain ⟨n, hn⟩ := (TorusModels.starHom_ker_isTwoGroup H K hKH).exists_card_eq
  have hc : Nat.card f.range = 60 := by
    rw [range_starHom, Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [← f.ker.card_mul_index, index_ker, hn, hc]
  intro hd
  have hcop : Nat.Coprime 9 (2 ^ n) := (by decide : Nat.Coprime 9 2).pow_right n
  exact (by decide : ¬ 9 ∣ 60) (hcop.dvd_mul_left.mp hd)

private theorem subgroup_rank_one (N : Subgroup G) (h9 : ¬ 9 ∣ Nat.card G)
    (h3 : 3 ∣ Nat.card N) : primeRank 3 N = 1 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 N := Classical.choice inferInstance
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hsmall : n ≤ 1 := by
    by_contra! h
    apply h9
    exact ((hn ▸ pow_dvd_pow 3 h).trans
      (P : Subgroup N).card_subgroup_dvd_card).trans N.card_subgroup_dvd_card
  have hcyc : IsCyclic P := isCyclic_of_card_dvd_prime
    (show Nat.card P ∣ 3 by rw [hn]; simpa using pow_dvd_pow 3 hsmall)
  have hu := P.primeRank_le_one_of_isCyclic hcyc
  have hl : primeRank 3 N ≠ 0 := fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz h3
  omega

/-- The actual PSL₂(4) model and the nontrivial local three-part give the
normalizer rank needed in 13.7.5(5). The normalizer is taken inside K. -/
public theorem linear_two_four_normalizer_rank
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (H K L₁ V₃ : Subgroup G) (hKH : K ≤ H)
    (e : Source.starImage H K ≃* PSL(2,F)) (hL₁K : L₁ ≤ K)
    (hL₁N : L₁ ≤ normalizer (V₃ : Set G))
    (hlocal : Nat.card (L₁ ⧸ pCore 2 L₁) = 3 ∨
      Nat.card (L₁ ⧸ pCore 2 L₁) = 9) :
    primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) = 1 := by
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  have h9 := nine_not_dvd_component H K hKH (e.trans eA)
  have hd : 3 ∣ Nat.card L₁ := by
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 L₁))
    rcases hlocal with h | h
    · rw [h]
    · rw [h]; decide
  let N := (K ⊓ normalizer (V₃ : Set G)).subgroupOf K
  have hr : primeRank 3 N = 1 := subgroup_rank_one N h9 (by
    rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact hd.trans (card_dvd_of_le (le_inf hL₁K hL₁N)))
  rwa [Theory.GroupTheory.primeRank_equiv 3 (subgroupOfEquivOfLe inf_le_left)] at hr

/-- The literal normalizer of V₃/V₁ in the action of K on H/V₁,
returned as a subgroup of the original ambient group. -/
@[expose] public def seedSectionNormalizer (H K V₃ V₁ : Subgroup G) [(V₁.subgroupOf H).Normal] : Subgroup G :=
  ((K.subgroupOf H) ⊓
    (normalizer (((V₃.subgroupOf H).map (QuotientGroup.mk' (V₁.subgroupOf H))) :
      Set (H ⧸ V₁.subgroupOf H))).comap (QuotientGroup.mk' (V₁.subgroupOf H))).map H.subtype

omit [Finite G] in
public theorem seedSectionNormalizer_eq (H K V₃ V₁ : Subgroup G) [(V₁.subgroupOf H).Normal]
    (hKH : K ≤ H) (hV₃H : V₃ ≤ H) (hV₁ : V₁ ≤ V₃) :
    seedSectionNormalizer H K V₃ V₁ = K ⊓ normalizer (V₃ : Set G) := by
  have hker : (QuotientGroup.mk' (V₁.subgroupOf H)).ker ≤ V₃.subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    exact subgroupOf_mono H hV₁
  rw [seedSectionNormalizer, comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
    comap_map_eq_self hker, ← subgroupOf_normalizer_eq hV₃H]
  change ((K ⊓ normalizer (V₃ : Set G)).subgroupOf H).map H.subtype = _
  exact map_subgroupOf_eq_of_le (inf_le_left.trans hKH)

/-- Apply the exact universal earlier 13.7.5(5) conclusion after proving
its rank hypothesis. The denominator remains the intrinsic O₂(L). -/
public theorem ordinary_six_of_contained_linear_two_four
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (H K L L₁ X V₃ V₁ : Subgroup G) [(V₁.subgroupOf H).Normal]
    (hKH : K ≤ H) (hV₃H : V₃ ≤ H) (hV₁ : V₁ ≤ V₃)
    (e : Source.starImage H K ≃* PSL(2,F))
    (hK : (K.subgroupOf H).IsCComponent) (hX : X ≤ K) (hL₁K : L₁ ≤ K)
    (hL₁N : L₁ ≤ normalizer (V₃ : Set G))
    (hlocal : Nat.card (L₁ ⧸ pCore 2 L₁) = 3 ∨
      Nat.card (L₁ ⧸ pCore 2 L₁) = 9)
    (h1375 : ∀ J : Subgroup G, J ≤ H → (J.subgroupOf H).IsCComponent →
      X ≤ J → L₁ ≤ J → primeRank 3 (seedSectionNormalizer H J V₃ V₁) = 1 →
      Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  apply h1375 K hKH hK hX hL₁K
  rw [seedSectionNormalizer_eq H K V₃ V₁ hKH hV₃H hV₁]
  exact linear_two_four_normalizer_rank hF H K L₁ V₃ hKH e hL₁K hL₁N hlocal

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction
