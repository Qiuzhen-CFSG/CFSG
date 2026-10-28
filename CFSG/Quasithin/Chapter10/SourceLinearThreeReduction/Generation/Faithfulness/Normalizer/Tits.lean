module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.FiniteClosure
public import Theory.SpecificGroups.Tits.TwoLocalFifteenFree

/-!
# The Tits row in the original odd-kernel normalizer

The actual residual image normalizes the nonzero elementary image of the
full module in the component's central quotient. In the Tits model this
normalizer has order indivisible by fifteen. Its certified order is
squarefree outside two and one odd prime, contradicting the doubled
odd ranks of the original perfect component quotient. Outer solvability
and covering uniqueness discharge residual placement for a normal component.

Source: Aschbacher--Smith 4.4.10--12 and 10.2.3(2), pp.621--623,745.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The Tits component is impossible on the original quotient geometry. -/
theorem source_nonnormal_oddNormalizer_no_placed_tits_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    (e : K ⧸ center K ≃* Tits.ParrottGroup) : False := by
  let S := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
  let N := normalizer (B : Set G)
  let F := ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
  let P := F.subgroupOf K
  let W := (D.fullModule.subgroupOf N).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  let U := W.map q
  let R := P.map q
  let J := normalizer (U.map e.toMonoidHom : Set Tits.ParrottGroup)
  obtain ⟨_,hne,hE,_,hnorm,hr⟩ :=
    source_nonnormal_oddNormalizer_component_quotient_geometry D hn B hBC hodd hBV K hFK
  have hRJ : R.map e.toMonoidHom ≤ J :=
    (map_mono hnorm).trans (U.le_normalizer_map e.toMonoidHom)
  let := hE
  have h15 : ¬ 15 ∣ Nat.card J := Tits.normalizer_fifteen_free _
    (fun he => hne ((map_eq_bot_iff_of_injective U e.injective).mp he))
    ((IsElementaryAbelian.isPGroup 2 U).map _)
  have hd : Nat.card J ∣ 17971200 := by
    simpa only [Tits.parrottGroup_card] using J.card_subgroup_dvd_card
  have hlow : ∀ p : ℕ, p.Prime → Odd p → 2 * primeRank p S ≤ primeRank p J := by
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    have he := hr p hp ho
    change primeRank p R = 2 * primeRank p S at he
    rw [←he,primeRank_congr p (e.subgroupMap R)]
    exact primeRank_mono p hRJ
  by_cases h3 : 3 ∣ Nat.card J
  · have h5 : ¬ 5 ∣ Nat.card J := fun he =>
      h15 ((show Nat.Coprime 3 5 by decide).mul_dvd_of_dvd_of_dvd h3 he)
    have hc : Nat.Coprime (Nat.card J) (5 ^ 2) :=
      ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr h5).symm.pow_right 2
    have hd' : Nat.card J ∣ 2 ^ 11 * 3 ^ 3 * 13 := hc.dvd_mul_left.mp
      (by convert hd using 1; norm_num)
    exact Perfect.no_doubled_odd_ranks_of_order S J Nat.prime_three
      (Nat.prime_iff.mp (by decide : Nat.Prime 13)).squarefree hd' hlow
  · have hc : Nat.Coprime (Nat.card J) (3 ^ 3) :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm.pow_right 3
    have hd' : Nat.card J ∣ 2 ^ 11 * 5 ^ 2 * 13 := hc.dvd_mul_left.mp
      (by convert hd using 1; norm_num)
    exact Perfect.no_doubled_odd_ranks_of_order S J (by decide : Nat.Prime 5)
      (Nat.prime_iff.mp (by decide : Nat.Prime 13)).squarefree hd' hlow

/-- Outer solvability and covering uniqueness discharge Tits residual placement. -/
theorem source_nonnormal_oddNormalizer_no_tits_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (e : K ⧸ center K ≃* Tits.ParrottGroup) : False := by
  exact source_nonnormal_oddNormalizer_no_placed_tits_component D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout
      (.rank_two 1 (.tits rfl ⟨e⟩))) e

end CFSG.Quasithin.Chapter10
