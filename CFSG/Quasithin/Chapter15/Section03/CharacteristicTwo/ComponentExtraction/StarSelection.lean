module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.ThompsonAction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.SymmetricFactors
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.QuotientSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.Lifting

/-!
# Select the outside Thompson component

`ThompsonAction` constructs the B.5.3 actor on the literal J(I)* and
applies the complete conditional FF classification. Here the earlier
Sylow and characteristic-two facts construct the elementary module
instance. `QuotientSelection` handles every classification branch: the
at-most-two bound and the Sylow intersection in the normalizer put the
S₃ factors in M_I*, and an ordinary component must escape. `Lifting`
uses the complete universal A.3.9 input on the component's inverse image
to lift it to a C-component of J(I), without assuming the star kernel
solvable. A.3.8 supplies its normalizer index bound. Subnormal core
inheritance and the actual image equivalence finish the candidate.

`exists_starComponentCandidate_of_characteristicTwo` assembles this
construction for any eligible outside overgroup, in both three-rank
branches. It requires only the earlier Sylow, theta, star-normalizer and
Thompson-escape conclusions, together with V ≤ T and characteristic two.
The genuine Y₊/O₂(Y₊) quotient enters the parent's subsequent core-quotient
upgrade and solvable control; selection needs no exponent assertion.

The complete universal B.5.1/B.5.6 and A.3.8/A.3.9 implications remain
explicit for `qt-15-03-char2-components` to discharge with their source
owners. This is the conditional candidate construction, not the complete
15.3.15 or 15.3.26 assertion. The `CoreQuotient` module provides
`StarComponentCandidate.componentWitness_of_source` for the subsequent
A.3.6 upgrade in the parent assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.8–9,
B.2.5–7, B.5.3/6, and 15.3.15(2)/26(2), printed pp.45–46, 76,
104–105, 1125 and 1130.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {G : Type u} [Group G] [Finite G]
namespace LocalData
variable (d : LocalData G)

/-- The characteristic-two and earlier Sylow conclusions construct the
module instance required by the classification, rather than assuming it. -/
theorem thompsonStar_classification_of_characteristicTwo {I : Subgroup G} {K : GroupClass.{u}}
    (classification : FFAlternatives.CompleteClassificationInput.{u,u} K)
    (hI : IsSQTK K I) (hVT : d.V ≤ (d.T : Subgroup G))
    (hS : Chapter1.IsSylowIn 2 d.S I) (hf : HasCharacteristicTwo I)
    (hJ : ¬ d.thompsonStar I ≤ d.starImage I d.M) :
    ∃ (hZI : d.Z ≤ I) (hU : IsElementaryAbelian 2 ((d.UI I).subgroupOf I)),
      let := hU
      FFAlternatives.SourceAlternative (d.thompsonStarAction I hZI) ∧
        Representation.BinaryOffender.IsFFModule (d.thompsonStarAction I hZI) ∧
        pPrimeCore 3 (d.thompsonStar I) = ⊥ := by
  have hZS := d.Z_le_S hVT
  have hZI := hZS.trans (Chapter1.isSylowIn_iff.mp hS).2.1
  let hU := d.UI_subgroupOf_elementary hS hZS hf
  let := hU
  exact ⟨hZI, hU, d.thompsonStar_sourceAlternative classification hI hZI hS hZS,
    d.thompsonStarAction_isFFModule I hZI hJ,
    d.thompsonStar_threePrimeCore_eq_bot classification hI hZI hS hZS hJ⟩

/-- A specified quotient component and its exact lift give the published
candidate, including the three-prime-core condition. -/
noncomputable def starComponentCandidate_of_lift {I L : Subgroup G}
    (E : Subgroup (d.thompsonStar I))
    (hE : Theory.GroupTheory.IsComponent (d.thompsonStar I) E)
    (houtside : ¬ E.map (d.thompsonStar I).subtype ≤ d.starImage I d.M)
    (hcore : pPrimeCore 3 (d.thompsonStar I) = ⊥)
    (hLJ : L ≤ Stellmacher.elementaryAbelianMaxJ I)
    (hL : (L.subgroupOf (Stellmacher.elementaryAbelianMaxJ I)).IsCComponent)
    (himage : d.starImage I L = E.map (d.thompsonStar I).subtype) :
    StarComponentCandidate d I where
  L := L
  le_thompson := hLJ
  component := hL
  outside := by
    intro hLM
    apply houtside
    rw [← himage]
    exact map_mono (comap_mono hLM)
  star_quasisimple := by
    rw [himage]
    let _ := hE.2
    exact Theory.GroupTheory.IsQuasisimple.of_mulEquiv
      (E.equivMapOfInjective _ (d.thompsonStar I).subtype_injective)
  star_threePrimeCore := by
    rw [himage]
    let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have he := Subgroup.IsSubnormal.pPrimeCore_eq_bot hcore E hE.1
    let e := E.equivMapOfInjective (d.thompsonStar I).subtype (d.thompsonStar I).subtype_injective
    have hh := pPrimeCore_map_iso 3 e
    rw [he, Subgroup.map_bot] at hh
    exact hh.symm

/-- The orbit bound accompanies the candidate without changing the chosen subgroup. -/
theorem exists_starComponentCandidate_of_lift {I L : Subgroup G}
    (E : Subgroup (d.thompsonStar I))
    (hE : Theory.GroupTheory.IsComponent (d.thompsonStar I) E)
    (houtside : ¬ E.map (d.thompsonStar I).subtype ≤ d.starImage I d.M)
    (hcore : pPrimeCore 3 (d.thompsonStar I) = ⊥)
    (hLJ : L ≤ Stellmacher.elementaryAbelianMaxJ I)
    (hL : (L.subgroupOf (Stellmacher.elementaryAbelianMaxJ I)).IsCComponent)
    (himage : d.starImage I L = E.map (d.thompsonStar I).subtype)
    (horbit : (normalizer (L : Set G)).relIndex I ≤ 2) :
    ∃ c : StarComponentCandidate d I, (normalizer (c.L : Set G)).relIndex I ≤ 2 :=
  ⟨d.starComponentCandidate_of_lift E hE houtside hcore hLJ hL himage, horbit⟩

/-- Construct an outside C-component of the actual Thompson subgroup from
the complete earlier classifications and the indicated conclusions of
15.3.11. This works for every eligible overgroup, including the smaller
ones needed for solvable control, and for either three-rank branch. -/
theorem exists_starComponentCandidate_of_characteristicTwo
    {I : Subgroup G} {K : GroupClass.{u}}
    (classification : FFAlternatives.CompleteClassificationInput.{u,u} K)
    (h38 : StarSelection.Lifting.A38Input K) (h39 : StarSelection.Lifting.A39Input K)
    (hSQTK : IsSQTK K I) (hI : I ∈ d.Hplus)
    (hVT : d.V ≤ (d.T : Subgroup G)) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hf : HasCharacteristicTwo I) (hθ : theta (d.MI I) = d.Yplus)
    (hN : normalizer (d.starImage I d.Yplus : Set (d.Star I)) = d.starImage I d.M)
    (hJ : ¬ d.thompsonStar I ≤ d.starImage I d.M) :
    ∃ c : StarComponentCandidate d I, (normalizer (c.L : Set G)).relIndex I ≤ 2 := by
  obtain ⟨hZI, hU, hclass⟩ :=
    d.thompsonStar_classification_of_characteristicTwo classification hSQTK hVT hS hf hJ
  let := hU
  obtain ⟨E, hE, houtside⟩ :=
    d.exists_star_component_of_sourceAlternative hI hS hθ hN hJ hZI hclass.1
  obtain ⟨L, hLJ, hL, himage, horbit⟩ :=
    d.exists_thompsonStar_component_lift h38 h39 hSQTK E hE
  exact d.exists_starComponentCandidate_of_lift E hE houtside hclass.2.2
    hLJ hL himage horbit

end LocalData
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
