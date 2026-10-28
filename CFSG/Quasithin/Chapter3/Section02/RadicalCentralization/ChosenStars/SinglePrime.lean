module
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ChosenStars.Models
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.MaximalFromStars

/-!
# The complete single-prime canonical radical argument

Genuine A.3.6 and Chapter 1 uniqueness construct the radical configuration.
If the Fitting quotient has only one odd prime, the coprime omega argument
controls every nontrivial characteristic subgroup of the literal two-core.
The completed model exclusions then give canonical starred membership,
without A.3.12 or C.2.7 callbacks. The existing primary-radical argument
yields centralization of the actual reduced subgroup in every normal
overgroup, retaining higher homocyclic exponents.

The multiple-prime characteristic-normalizer construction and final
11.4.2 assembly remain with qt-d-1222-comparison-nonquasisimple.
Source: Aschbacher--Smith, 1.3.8, pp.512--514, and 3.2.14, p.585.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars
open Chapter1 Chapter1.Section02 Chapter1.RadicalNormalizers Chapter1.RadicalActions
open Chapter1.RadicalExclusions
universe u
variable {G : Type u} [Group G] [Finite G]

/-- All fields of the actual radical configuration except its characteristic
normalizer bound follow from the original maximal local hypotheses. -/
theorem XiP_mem_XiStar_of_characteristic_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hcontrol : (radicalCore p L T).characteristicNormalizerClosure ≤
      normalizer (L : Set G)) : XiP p L ∈ XiStar G (T : Subgroup G) := by
  let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have hQ := uniqueness_local_quotient_sqtk hG hL.1.2.2
  obtain ⟨hq,hN,hM⟩ := Chapter13.Section01.RadicalConjugateRigidity.maximal_radical_structure
    hG T hL hn ho hd
  let P : Sylow p (XiP p L) := default
  have hc : Configuration p T (XiP p L)
      ((P : Subgroup (XiP p L)).map (XiP p L).subtype) L (normalizer (L : Set G)) :=
    ⟨Fact.out,ho,(XiP_oddQuotient_of_A36 h36 hL.1 hQ hn ho hd).1,
      (Chapter13.Section01.XiP_mem_XiPlus_source hG T hL.1 hn ho hd).1,
      rfl,hL,hq,⟨P,rfl⟩,
      XiP_automizer_not_isCyclic_of_A36 h36 hL.1 hQ hn ho hd P,
      XiP_normalizer_irreducible_of_A36 h36 hL.1 hQ hn ho hd P,
      rfl,hN.symm,hM,hcontrol⟩
  exact configuration_mem_XiStar hG T hc

/-- The complete single-odd-prime branch of 1.3.8, retaining arbitrary
homocyclic exponents and no earlier-source callbacks. -/
theorem XiP_mem_XiStar_of_singlePrime
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hs : ∀ q : ℕ, q.Prime → Odd q →
      q ∣ Nat.card (fittingSubgroup (XiQuotient L)) → q = p) :
    XiP p L ∈ XiStar G (T : Subgroup G) := by
  let hA := fun (A : Type u) [Group A] [Finite A] =>
    ChapterA.Section02.theoremA_knownSimple (G := A)
  let hC := fun (A : Type u) [Group A] [Finite A] =>
    ChapterA.Section02.theoremC_knownSimple (G := A)
  let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC hA hC
  have h38 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → B.Normal ∨ IsQuasisimple B :=
    fun _ _ _ hA hO _ hB => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hA hO hB
  have h127 : ∀ K ∈ LStar G (T : Subgroup G),
      IsMaximalTwoLocal (normalizer (componentOrbit K (T : Subgroup G) : Set G)) ∧
      ∀ M : Subgroup G, IsMaximalTwoLocal M → K ⊔ (T : Subgroup G) ≤ M →
        M = normalizer (componentOrbit K (T : Subgroup G) : Set G) := by
    intro K hK
    have hh := nonsolvable_uniqueness_of_theoremsAC hA hC hG T hK
    exact ⟨hh.normalizer_maximal,hh.normalizer_unique⟩
  exact XiP_mem_XiStar_of_characteristic_control hG T hL hn ho hd
    (radical_singlePrime_normalizers_of_source h36 h38 h127 hL
      (uniqueness_local_quotient_sqtk hG hL.1.2.2) hn ho hd hs).2

/-- Prime-power Fitting order discharges all canonical-star premises. -/
theorem canonicalRadicalsStarred_of_fitting_isPGroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (hf : IsPGroup p (fittingSubgroup (XiQuotient L))) :
    CanonicalRadicalsStarred T L := by
  obtain ⟨n,hcard⟩ := hf.exists_card_eq
  have support {q : ℕ} (hq : q.Prime)
      (hd : q ∣ Nat.card (fittingSubgroup (XiQuotient L))) : q = p := by
    rw [hcard] at hd
    exact (Nat.prime_dvd_prime_iff_eq hq Fact.out).mp (hq.dvd_of_dvd_pow hd)
  intro q hq ho hd
  exact XiP_mem_XiStar_of_singlePrime hG T hL hn ho hd
    (fun r hr _ hd' => (support hr hd').trans (support hq.out hd).symm)

/-- Maximal-local 3.2.14 in the complete prime-power Fitting branch, on
any normal overgroup with its literal inclusion map. -/
theorem maximal_solvableRadical_centralizes_reduced_of_fitting_isPGroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (hf : IsPGroup p (fittingSubgroup (XiQuotient L)))
    (J : Subgroup G) (hLJ : L ≤ J) (hJn : J ≤ normalizer (L : Set G)) :
    (solvableRadical L).map L.subtype ≤
      centralizer ((reducedTwoSubgroup J).map J.subtype : Set G) :=
  maximal_solvableRadical_centralizes_reduced_of_stars hG T hmany hL hn
    (canonicalRadicalsStarred_of_fitting_isPGroup hG T hL hn hf) J hLJ hJn

/-- The literal Sylow-join specialization needed in 11.4.2. -/
theorem maximal_solvableRadical_centralizes_sylowJoin_of_fitting_isPGroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {J : Subgroup G} (hJ : J ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient J)) {p : ℕ} [Fact p.Prime]
    (hf : IsPGroup p (fittingSubgroup (XiQuotient J))) :
    (solvableRadical J).map J.subtype ≤
      centralizer ((reducedTwoSubgroup (J ⊔ (T : Subgroup G) : Subgroup G)).map
        (J ⊔ (T : Subgroup G)).subtype : Set G) :=
  maximal_solvableRadical_centralizes_sylowJoin_of_stars hG T hmany hJ hn
    (canonicalRadicalsStarred_of_fitting_isPGroup hG T hJ hn hf)

end CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars
