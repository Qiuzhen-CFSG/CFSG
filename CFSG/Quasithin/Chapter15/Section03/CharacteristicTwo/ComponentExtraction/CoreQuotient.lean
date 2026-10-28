module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.CoreAction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.PPrimeCoreSurjection
public import Theory.Quasithin.Rank

/-!
# The two-core quotient from the genuine SQTK alternatives

The image of `O₃′(L)` is central in `L/O₂(L)` by `CoreAction`. Taking a
quotient by the two-core commutes with taking the three-prime core. We
transport this centrality through the actual isomorphism from `L/O₂(L)`
to its image in `I/O₂(I)`.

Apply the complete A.3.6 conclusion to that image. The simple and covering
alternatives are quasisimple already. In each other alternative the Fitting
subgroup has order prime to three, by the natural-module coordinates or the
listed prime congruences. It is therefore central. The quasisimple quotient
by the Fitting subgroup lifts through this perfect central cover. No
center–Frattini equality from the problematic 1.2.1(4d) is needed.

The final constructor supplies every field of `ComponentWitness` from a
selected star candidate and the universal A.3.6 theorem. The latter is an
explicit source-theorem parameter, not a proved classification here. The
extraction owner must select the candidate and instantiate A.3.6 before
claiming 15.3.15(2) or 15.3.26(2).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.6,
printed pp.43–45, and 15.3.15(2)/26(2), printed pp.1125 and 1130.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
open Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem quasisimple_of_A36_core_central (L : Subgroup G)
    [Group.IsPerfect L] (hA : A36Conclusion L)
    (hc : pPrimeCore 3 L ≤ center L) : IsQuasisimple L := by
  have hf : IsQuasisimple (L ⧸ fittingSubgroup L) := hA.2.2.1
  have hfc : Nat.Coprime 3 (Nat.card (fittingSubgroup L)) ∨ IsQuasisimple L := by
    rcases hA.1 with ⟨hcomp, _, _⟩ | ⟨hcomp, _, _⟩ | ⟨hdata⟩ | ⟨hdata⟩
    · exact Or.inr hcomp.2
    · exact Or.inr hcomp.2
    · left
      obtain ⟨heq, p, hp, hlarge, F, hF, hfin, hcard, v, _, _⟩ := hdata
      let _ := hF
      let _ := hfin
      have horder : Nat.card (fittingSubgroup L) = p ^ 2 := by
        rw [← heq]
        calc
          Nat.card (generalizedFitting L) = Nat.card (Multiplicative (Fin 2 → F)) :=
            Nat.card_congr v.toEquiv
          _ = p ^ 2 := by
            change Nat.card (Fin 2 → F) = p ^ 2
            simp only [Nat.card_fun, Nat.card_fin, hcard]
      rw [horder]
      exact (Nat.coprime_primes Nat.prime_three hp).mpr (by omega) |>.pow_right 2
    · left
      apply Nat.prime_three.coprime_iff_not_dvd.mpr
      intro hdiv
      have hh := hdata.2.2.2 3 Nat.prime_three (hdata.1 ▸ hdiv)
      norm_num at hh
  rcases hfc with hcop | hq
  · let _ := hf
    let f : PerfectCentralCovering.Cover L (L ⧸ fittingSubgroup L) := {
      toMonoidHom := QuotientGroup.mk' (fittingSubgroup L)
      surjective := QuotientGroup.mk'_surjective _
      isPerfect := inferInstance
      ker_le_center := by
        rw [QuotientGroup.ker_mk']
        exact (show fittingSubgroup L ≤ pPrimeCore 3 L from
          le_sSup ⟨inferInstance, hcop⟩).trans hc }
    exact f.isQuasisimple
  · exact hq

private theorem core_quotient_threePrimeCore_central {L : Subgroup G}
    (hc : (pPrimeCore 3 L).map (QuotientGroup.mk' (pCore 2 L)) ≤
      center (L ⧸ pCore 2 L)) :
    pPrimeCore 3 (L ⧸ pCore 2 L) ≤ center (L ⧸ pCore 2 L) := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let q := QuotientGroup.mk' (pCore 2 L)
  have hker : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have he := congrArg (map q) (pPrimeCore_comap_eq_of_surjective_coprime 3 q
    (QuotientGroup.mk'_surjective _) hker)
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at he
  exact he ▸ hc

namespace StarComponentCandidate
variable {d : LocalData G} {I : Subgroup G}

/-- Upgrade the selected component using the complete earlier classification of its quotient image. -/
theorem core_quotient_quasisimple_of_A36 (c : StarComponentCandidate d I)
    (hI : I ∈ d.Hplus) (hθ : theta (d.MI I) = d.Yplus)
    (hindex : (normalizer (c.L : Set G)).relIndex I ≤ 2)
    (hC : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (hNorm : normalizer (d.starImage I d.Yplus : Set (d.Star I)) = d.starImage I d.M)
    (hY : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus))
    (hA : A36Conclusion ((c.L.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)))) :
    IsQuasisimple (c.L ⧸ pCore 2 c.L) := by
  let B := (c.L.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))
  have hcomp := LocalData.thompson_component_in c.le_thompson c.component
  let _ : Group.IsNilpotent (pCore 2 I) := pCore_isNilpotent
  let _ : Group.IsPerfect B := (hcomp.map_quotient (pCore 2 I)).perfect
  let e₀ := subgroupOfEquivOfLe c.le_overgroup
  let e₁ : ((c.L.subgroupOf I) ⧸ pCore 2 (c.L.subgroupOf I)) ≃*
      (c.L ⧸ pCore 2 c.L) :=
    QuotientGroup.congr _ _ e₀ (pCore_map_iso 2 e₀)
  let e : (c.L ⧸ pCore 2 c.L) ≃* B :=
    e₁.symm.trans (cComponentTwoCoreQuotientEquiv hcomp)
  have hcentral := core_quotient_threePrimeCore_central
    (c.threePrimeCore_image_le_center hI hθ hindex hC hNorm hY)
  have hcentralB : pPrimeCore 3 B ≤ center B := by
    rw [← pPrimeCore_map_iso 3 e]
    rintro x ⟨y, hy, rfl⟩
    exact (Subgroup.centerCongr e ⟨y, hcentral hy⟩).property
  let _ := quasisimple_of_A36_core_central B hA hcentralB
  exact IsQuasisimple.of_mulEquiv e.symm

/-- Instantiate A.3.6 on the actual two-core quotient; its SQTK hypothesis follows from that of `I`. -/
theorem core_quotient_quasisimple_of_source {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ K : Subgroup X,
      K.IsCComponent → A36Conclusion K)
    (c : StarComponentCandidate d I) (hSQTK : IsSQTK 𝒦 I)
    (hI : I ∈ d.Hplus) (hθ : theta (d.MI I) = d.Yplus)
    (hindex : (normalizer (c.L : Set G)).relIndex I ≤ 2)
    (hC : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (hNorm : normalizer (d.starImage I d.Yplus : Set (d.Star I)) = d.starImage I d.M)
    (hY : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus)) :
    IsQuasisimple (c.L ⧸ pCore 2 c.L) := by
  have hQ : IsSQTK 𝒦 (I ⧸ pCore 2 I) := by
    refine ⟨?_, hSQTK.isKGroup.quotient _⟩
    intro p hp ho
    let _ : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho
      (pCore 2 I) pCore_isPGroup).trans (hSQTK.stronglyQuasithin p hp ho)
  exact c.core_quotient_quasisimple_of_A36 hI hθ hindex hC hNorm hY
    (proposition_1_2_1_four_earlier_conclusion hA36 hQ
      (LocalData.thompson_component_in c.le_thompson c.component))

/-- Assemble the requested witness after star selection and instantiation of the universal A.3.6 theorem. -/
noncomputable def componentWitness_of_source {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ K : Subgroup X,
      K.IsCComponent → A36Conclusion K)
    (c : StarComponentCandidate d I) (hSQTK : IsSQTK 𝒦 I)
    (hI : I ∈ d.Hplus) (hθ : theta (d.MI I) = d.Yplus)
    (hindex : (normalizer (c.L : Set G)).relIndex I ≤ 2)
    (hC : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (hNorm : normalizer (d.starImage I d.Yplus : Set (d.Star I)) = d.starImage I d.M)
    (hY : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus)) : ComponentWitness d I where
  L := c.L
  le_thompson := c.le_thompson
  component := c.component
  outside := c.outside
  rank_pos := c.rank_pos
  commutator_eq := d.thompson_component_eq_commutator_of_orbit hI c.le_thompson c.component
    hθ hindex c.outside hC hNorm c.star_quasisimple
  star_quasisimple := c.star_quasisimple
  core_quotient_quasisimple := c.core_quotient_quasisimple_of_source hA36 hSQTK
    hI hθ hindex hC hNorm hY

end StarComponentCandidate
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo

end
