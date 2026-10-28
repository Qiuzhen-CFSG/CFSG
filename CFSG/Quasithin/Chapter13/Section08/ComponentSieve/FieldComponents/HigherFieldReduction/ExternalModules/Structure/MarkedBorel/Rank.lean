module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.Quotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Borel
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.CoveredAlternative

/-!
# The even-field Borel and external cubic have three-rank greater than one

The marked Borel is the intrinsic Sylow normalizer in the actual PSL₂(2ⁿ)
component. Its two-residual has three-rank one when n is even. The external
cubic image is disjoint from it and commutes with it. Their product therefore
has three-rank at least two, also before taking the two-core quotient.
The exact theta identity then excludes the ordinary A₆ marked local quotient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.20(a), printed p.954/PDF p.971, and 13.7.3(9), printed p.936.
-/

public section


open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel
open Components.Swapped.LinearTwo
variable {G : Type*} [Group G] [Finite G]

theorem star_threeRank_le (H A : Subgroup G) (hAH : A ≤ H) :
    primeRank 3 (Source.starImage H A) ≤ primeRank 3 A := by
  let f := (starHom H A hAH).rangeRestrict
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = (starHom H A hAH).ker := by
      ext x
      exact Subtype.ext_iff
    rw [he]
    exact TorusModels.starHom_ker_isTwoGroup H A hAH
  have hc : Nat.Coprime 3 (Nat.card f.ker) := by
    obtain ⟨k,hk⟩ := hk.exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have h := primeRank_le_of_surjective_of_coprime 3 f
    (starHom H A hAH).rangeRestrict_surjective hc
  rwa [range_starHom H A hAH] at h

private theorem cubic_disjoint (A K : Subgroup G) (hc : Nat.card A = 3)
    (hne : ¬ A ≤ K) : Disjoint A K := by
  have hdvd : Nat.card (A ⊓ K : Subgroup G) ∣ 3 := by
    rw [← hc]
    exact card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact disjoint_iff.mpr (card_eq_one.mp h1)
  · have he : A ⊓ K = A := eq_of_le_of_card_ge inf_le_left (by omega)
    exact (hne (he.symm.le.trans inf_le_right)).elim

theorem rank_gt_one_of_external_cubic (H K B X : Subgroup G)
    (hKH : K ≤ H) (hBK : B ≤ K) (hXH : X ≤ H)
    (hc : Nat.card (Source.starImage H X) = 3)
    (hne : ¬ Source.starImage H X ≤ Source.starImage H K)
    (hcent : Source.starImage H X ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)))
    (hB : primeRank 3 (Source.starImage H B) = 1) :
    1 < primeRank 3 (B ⊔ X : Subgroup G) := by
  let A := Source.starImage H X
  let C := Source.starImage H B
  have hCK : C ≤ Source.starImage H K := map_mono (subgroupOf_mono H hBK)
  have hd : Disjoint A C := (cubic_disjoint A _ hc hne).mono_right hCK
  have hp : 0 < primeRank 3 A := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz (by rw [hc])
  have hr := A.primeRank_sup_eq_add_of_disjoint_commuting C hd
    (hcent.trans (centralizer_le hCK)) 3
  have ht := star_threeRank_le H (B ⊔ X) (sup_le (hBK.trans hKH) hXH)
  have he : Source.starImage H (B ⊔ X) = C ⊔ A := by
    unfold Source.starImage
    rw [subgroupOf_sup (hBK.trans hKH) hXH, Subgroup.map_sup]
    rfl
  rw [he, sup_comm C A, hr] at ht
  change primeRank 3 C = 1 at hB
  omega

theorem marked_borel_star_rank (H K : Subgroup G) (hKH : K ≤ H)
    (S : Sylow 2 (Source.starImage H K)) {n : ℕ} (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    (heven : Even n) :
    primeRank 3 (Source.starImage H (borelResidual
      (HigherFieldReduction.borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K) S)))) = 1 := by
  let Ks := Source.starImage H K
  let N := normalizer (S : Set Ks)
  have hperfect : IsPPerfect 2 N := BinaryBorel.factor_twoPerfect (by omega) hmodel S
  have hr : residualIn 2 (SylowBorel.relativeBorel Ks S) = SylowBorel.relativeBorel Ks S := by
    have hp : IsPPerfect 2 (SylowBorel.relativeBorel Ks S) :=
      hperfect.of_surjective (Ks.subtype.subgroupMap N) (Ks.subtype.subgroupMap_surjective N)
    rw [residualIn, (pResidual_eq_top_iff 2 _).mpr hp,
      ← MonoidHom.range_eq_map, range_subtype]
  rw [starImage_borelResidual H K hKH _ (SylowBorel.relativeBorel_le Ks S), hr]
  let e := N.equivMapOfInjective Ks.subtype Ks.subtype_injective
  exact (primeRank_congr 3 e).symm.trans
    (BinaryBorel.factor_threeRank (by omega) hmodel heven S)

theorem covered_of_external_borel_rank (H M L L₁ B X : Subgroup G)
    (hBH : B ≤ H) (hBM : B ≤ M) (hXH : X ≤ H) (hXM : X ≤ M)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (hmodels : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (ha6 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hrank : 1 < primeRank 3 (B ⊔ X : Subgroup G)) :
    (¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))) ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  have hle : primeRank 3 (B ⊔ X : Subgroup G) ≤ primeRank 3 L₁ :=
    threeRank_le_of_contains_threes _ _ (by
      intro x hx ho
      rw [htheta]
      exact subset_closure ⟨⟨sup_le hBH hXH hx, sup_le hBM hXM hx⟩,ho⟩)
  have hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
    intro h
    have hu := rank_le_one_of_cubic_core_quotient L₁ (ha6 h)
    omega
  exact ⟨hnot, hmodels.resolve_left hnot⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel

end
