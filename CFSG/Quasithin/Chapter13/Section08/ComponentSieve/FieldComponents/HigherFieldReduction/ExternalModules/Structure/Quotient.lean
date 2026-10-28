module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.PrimeRankHom
public import Theory.Quasithin.Rank

/-!
# External cubic images and the source three-rank bound

The literal star projection retains its two-core kernel. Relative normality
identifies the kernel on X with O₂(X); two-residual monotonicity lifts a
containment X* ≤ K* back to X ≤ K. Thus a two-perfect external X with cubic
quotient remains an external cubic subgroup in H/O₂(H). Its commuting
product with K* consumes one of the ambient SQTK group's two three-ranks.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.20(a), printed p.954 (PDF p.971). The two-perfect residual, relative
normality, and cubic quotient are exact earlier-source inputs. The actual
component possibilities and marked local geometry are not asserted here.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Relative subnormality identifies the intrinsic kernel of the literal star projection. -/
noncomputable def quotientStarEquiv (H X : Subgroup G) (hXH : X ≤ H)
    (hX : (X.subgroupOf H).IsSubnormal) :
    (X ⧸ pCore 2 X) ≃* Source.starImage H X :=
  let e := (subgroupOfEquivOfLe hXH).symm
  (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (hX.quotientCoreImageEquiv 2)

omit [Finite G] in
/-- The full preimage of the star image retains the two-core kernel. -/
theorem star_preimage (H X : Subgroup G) (hXH : X ≤ H) :
    ((Source.starImage H X).comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype =
      X ⊔ Source.QH H := by
  unfold Source.starImage Source.QH
  rw [comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
    map_subgroupOf_eq_of_le hXH]
  rfl

omit [Finite G] in
/-- Two-residuals lift image containment through a two-kernel that normalizes
the target. This also applies to T-invariant Borel residuals when O₂(H) ≤ T. -/
theorem le_of_star_le_of_kernel_normalizes (H K X : Subgroup G) (hKH : K ≤ H) (hXH : X ≤ H)
    (hK : IsPPerfect 2 K) (hX : IsPPerfect 2 X)
    (hnK : Source.QH H ≤ normalizer (K : Set G))
    (h : Source.starImage H X ≤ Source.starImage H K) : X ≤ K := by
  have hle : X ≤ K ⊔ Source.QH H := by
    rw [← star_preimage H K hKH]
    intro x hx
    exact ⟨⟨x,hXH hx⟩, h ⟨⟨x,hXH hx⟩,hx,rfl⟩,rfl⟩
  have hm := embedded_pResidual_mono 2 hle
  rw [(pResidual_eq_top_iff 2 X).mpr hX, ← MonoidHom.range_eq_map,
    range_subtype, embedded_pResidual_join_pGroup K (Source.QH H) hK
      (isPGroup_pCoreIn 2 H) hnK] at hm
  exact hm

omit [Finite G] in
/-- Relative normality supplies the normalization needed to recover the lift. -/
theorem le_of_star_le (H K X : Subgroup G) (hKH : K ≤ H) (hXH : X ≤ H)
    (hK : IsPPerfect 2 K) (hX : IsPPerfect 2 X)
    (hnK : H ≤ normalizer (K : Set G))
    (h : Source.starImage H X ≤ Source.starImage H K) : X ≤ K :=
  le_of_star_le_of_kernel_normalizes H K X hKH hXH hK hX
    ((pCoreIn_le 2 H).trans hnK) h

omit [Finite G] in
/-- The external residual stays external after passage to H/O₂(H). -/
theorem star_not_le (H K X : Subgroup G) (hKH : K ≤ H) (hXH : X ≤ H)
    (hK : IsPPerfect 2 K) (hX : IsPPerfect 2 X) [(K.subgroupOf H).Normal]
    (hne : ¬ X ≤ K) : ¬ Source.starImage H X ≤ Source.starImage H K :=
  fun h => hne (le_of_star_le H K X hKH hXH hK hX
    (le_normalizer_of_normal_subgroupOf hKH) h)

/-- The earlier cubic quotient has order three in the literal star image. -/
theorem star_card_three (H X : Subgroup G) (hXH : X ≤ H) [(X.subgroupOf H).Normal]
    (hc : Nat.card (X ⧸ pCore 2 X) = 3) : Nat.card (Source.starImage H X) = 3 := by
  exact (Nat.card_congr (quotientStarEquiv H X hXH
    (Subgroup.Normal.isSubnormal inferInstance)).toEquiv).symm.trans hc

/-- The extra commuting cubic subgroup uses one of the two available three-ranks. -/
theorem star_threeRank_le_one (κ : GroupClass.{u}) (H K X : Subgroup G)
    (hH : IsSQTK κ H) (hc : Nat.card (Source.starImage H X) = 3)
    (hne : ¬ Source.starImage H X ≤ Source.starImage H K)
    (hcent : Source.starImage H X ≤ centralizer (Source.starImage H K : Set (Source.Hstar H))) :
    primeRank 3 (Source.starImage H K) ≤ 1 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hr : primeRank 3 (Source.Hstar H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
      (hH.stronglyQuasithin 3 Nat.prime_three (by decide))
  let A := Source.starImage H X
  let B := Source.starImage H K
  change Nat.card A = 3 at hc
  change primeRank 3 B ≤ 1
  have hd : Disjoint A B := by
    have hdvd : Nat.card (A ⊓ B : Subgroup (Source.Hstar H)) ∣ 3 := by
      rw [← hc]
      exact card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact disjoint_iff.mpr (card_eq_one.mp h1)
    · have he : A ⊓ B = A := eq_of_le_of_card_ge inf_le_left (by omega)
      exact (hne (he.symm.le.trans inf_le_right)).elim
  have hpos : 0 < primeRank 3 A := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz (by rw [hc])
  have hsum := A.primeRank_sup_eq_add_of_disjoint_commuting B hd hcent 3
  have hle := Theory.GroupTheory.primeRank_le_of_injective 3 (A ⊔ B).subtype (A ⊔ B).subtype_injective
  omega

/-- A two-core quotient preserves three-rank, retaining its actual kernel. -/
theorem threeRank_eq_star (H K : Subgroup G) (hKH : K ≤ H)
    (hnK : (K.subgroupOf H).IsSubnormal) :
    primeRank 3 K = primeRank 3 (Source.starImage H K) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.Coprime 3 (Nat.card (pCore 2 K)) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  have hz : primeRank 3 (pCore 2 K) = 0 :=
    PrimeRank.eq_zero_iff_not_dvd_card.mpr (Nat.prime_three.coprime_iff_not_dvd.mp hc)
  have hl := primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup
  have hu := primeRank_le_ker_add (p := 3) (QuotientGroup.mk' (pCore 2 K))
  rw [QuotientGroup.ker_mk', hz, zero_add] at hu
  exact (Nat.le_antisymm hu hl).trans (primeRank_congr 3 (quotientStarEquiv H K hKH hnK))
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure

end
