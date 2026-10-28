module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalBounds

/-!
# The Janko-four obstruction on a fixed local module

The certified order bounds all odd ranks except eleven. The actual local
module embeds in the component with rank at most eleven, whose automorphism
group has eleven-rank at most one. The residual contributes twice each
odd rank, excluding the remaining possibility. Full centers are retained.
Source: Aschbacher--Smith 4.4.10--12 and 10.2.3(2), pp.621--623,745.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.LocalFixed
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem eleven_rank_small_elementary_aut
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hc : Nat.card E ≤ 2 ^ 11) : primeRank 11 (MulAut E) ≤ 1 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  apply primeRank_le_one_of_square_not_dvd
  obtain ⟨d,hd⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hdim : d ≤ 11 := by
    rw [hd] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E d hd]
  interval_cases d <;> norm_num [Fin.prod_univ_succ]

private theorem janko_odd_rank
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hp3 : p ≠ 3) (hp11 : p ≠ 11) :
    primeRank p Janko4.Model ≤ 1 := by
  apply primeRank_le_one_of_square_not_dvd
  rw [Janko4.Cardinality.model_card]
  intro hs
  have hp : p.Prime := Fact.out
  have h2 : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
    subst p
    exact ho.not_two_dvd_nat (dvd_refl 2))
  have h3 : Nat.Coprime p 3 := hp.coprime_iff_not_dvd.mpr
    (fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd))
  have h11 : Nat.Coprime p 11 := hp.coprime_iff_not_dvd.mpr
    (fun hd => hp11 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd))
  have hc : Nat.Coprime (p ^ 2) (2 ^ 21 * 3 ^ 3 * 11 ^ 3) :=
    (((h2.pow_right 21).mul_right (h3.pow_right 3)).mul_right (h11.pow_right 3)).pow_left 2
  have hd : p ^ 2 ∣ 2 ^ 21 * 3 ^ 3 * 11 ^ 3 * (5 * 7 * 23 * 29 * 31 * 37 * 43) := by
    convert hs using 1
    norm_num
  have hsf : Squarefree (5 * 7 * 23 * 29 * 31 * 37 * 43 : ℕ) := by
    have h0 : Squarefree (5 : ℕ) := (Nat.prime_iff.mp (by decide : Nat.Prime 5)).squarefree
    have h1 : Squarefree (5 * 7 : ℕ) :=
      (Nat.squarefree_mul (by decide : Nat.Coprime (5) 7)).mpr
        ⟨h0, (Nat.prime_iff.mp (by decide : Nat.Prime 7)).squarefree⟩
    have h2 : Squarefree (5 * 7 * 23 : ℕ) :=
      (Nat.squarefree_mul (by decide : Nat.Coprime (5 * 7) 23)).mpr
        ⟨h1, (Nat.prime_iff.mp (by decide : Nat.Prime 23)).squarefree⟩
    have h3 : Squarefree (5 * 7 * 23 * 29 : ℕ) :=
      (Nat.squarefree_mul (by decide : Nat.Coprime (5 * 7 * 23) 29)).mpr
        ⟨h2, (Nat.prime_iff.mp (by decide : Nat.Prime 29)).squarefree⟩
    have h4 : Squarefree (5 * 7 * 23 * 29 * 31 : ℕ) :=
      (Nat.squarefree_mul (by decide : Nat.Coprime (5 * 7 * 23 * 29) 31)).mpr
        ⟨h3, (Nat.prime_iff.mp (by decide : Nat.Prime 31)).squarefree⟩
    have h5 : Squarefree (5 * 7 * 23 * 29 * 31 * 37 : ℕ) :=
      (Nat.squarefree_mul (by decide : Nat.Coprime (5 * 7 * 23 * 29 * 31) 37)).mpr
        ⟨h4, (Nat.prime_iff.mp (by decide : Nat.Prime 37)).squarefree⟩
    have h6 : Squarefree (5 * 7 * 23 * 29 * 31 * 37 * 43 : ℕ) :=
      (Nat.squarefree_mul (by decide : Nat.Coprime (5 * 7 * 23 * 29 * 31 * 37) 43)).mpr
        ⟨h5, (Nat.prime_iff.mp (by decide : Nat.Prime 43)).squarefree⟩
    exact h6
  exact (Nat.squarefree_iff_prime_squarefree.mp hsf p hp)
    (by simpa only [pow_two] using hc.dvd_mul_left.mp hd)


/-- The actual fixed local module excludes the Janko-four covering component. -/
theorem source_nonnormal_oddNormalizer_no_placed_jankoFour_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
    (hVX : V = ⁅V,localOrbit T L⁆)
    (hNV : localJoin T L ≤ normalizer (V : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (B : Set G))) (hc : pCore 2 K = ⊥)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    (e : K ⧸ center K ≃* Janko4.Model) : False := by
  let S := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
  obtain ⟨p,hp,ho,hp3,hd⟩ := Perfect.exists_odd_prime_ne_dvd_card S Nat.prime_three
  let : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < primeRank p S := by
    have hne : primeRank p S ≠ 0 := fun hh => PrimeRank.eq_zero_iff_not_dvd_card.mp hh hd
    omega
  by_cases hp11 : p = 11
  · subst p
    let N := normalizer (B : Set G)
    let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype
    let W := (V.subgroupOf N).subgroupOf K
    have hVN : V ≤ N := (le_centralizer_iff.mp hBV).trans (Subgroup.centralizer_le_normalizer _)
    have hVK : V.subgroupOf N ≤ K := by
      obtain ⟨_,_,hVF⟩ := source_local_oddActor_cover D V hVV hVX hNV B hBC hodd hBV
      exact (subgroupOf_mono N (hVF.trans (pCoreIn_le 2 F))).trans hFK
    obtain ⟨_,_,_,_,hW,_,_,_,_⟩ :=
      source_local_oddActor_component_geometry D V hVV hne hVX hNV B hBC hodd hBV K hFK
    have hcard : Nat.card V ≤ 2 ^ 11 := by
      rw [←Nat.card_congr ((subgroupOfEquivOfLe hVK).trans (subgroupOfEquivOfLe hVN)).toEquiv]
      exact elementary_card_le_of_twoCore_eq_bot W hW hc
        ((primeRank_congr 2 e).trans_le Janko4.TwoRank.model_twoRank_le_eleven)
    let := D.fullModule_elementary (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      D.simpleQTKE T D.maximal)
    let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le hVV
    have hlo := source_local_automorphism_rank D hn V hVV hne hVX hNV ho
    change 2 * primeRank 11 S ≤ primeRank 11 (MulAut V) at hlo
    have hup := eleven_rank_small_elementary_aut V hcard
    omega
  · obtain ⟨_,_,_,_,_,hr⟩ :=
      source_local_oddActor_component_quotient_geometry D hn V hVV hne hVX hNV B hBC hodd hBV K hFK
    have hlo : 2 * primeRank p S ≤ primeRank p (K ⧸ center K) :=
      (hr p hp ho).symm.le.trans (primeRank_subgroup_le p _)
    have hup : primeRank p (K ⧸ center K) ≤ 1 := by
      rw [primeRank_congr p e]
      exact janko_odd_rank ho hp3 hp11
    omega

end CFSG.Quasithin.Chapter10.LocalFixed
