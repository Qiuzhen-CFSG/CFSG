module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersSixSourceRigidity
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ChosenStars.Complete
public import Theory.GroupTheory.ReducedNormal.SylowCenter

/-!
# Excluding nonquasisimple escaping overcomponents

An odd prime in the Fitting subgroup of the actual two-core quotient
supplies a canonical starred radical. The proved 3.2.14 centralization
places it in the weight-six centralizer. Its unique maximal two-local
normalizer therefore equals the original component normalizer, controlling
the full maximal overcomponent. This route retains all odd-radical exponents.

LocalAnalysisCentralizersTwoSourceComponents applies the result to the
literal weight-two residual. Source: Aschbacher–Smith, 3.2.14 and 12.3.8,
printed pp.585,809–810.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
namespace Setup.NaturalCoordinates
variable (E : S.NaturalCoordinates)

include E in
theorem many_maximal_overgroups
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.hypothesis.simpleQTKE T S.hypothesis.maximal_faithful.1
  have hm : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [S.chosen.localOrbit_eq] using hu.normalizer_maximal
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (E.hasMaximalOutside structural escape)
  have hHN : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  obtain ⟨N,hNN,hN⟩ := Finite.exists_le_maximal
    (show IsTwoLocal (normalizer (H.pCoreIn 2 : Set G)) from
      ⟨_,hH.1.1.1,isPGroup_pCoreIn 2 H,rfl⟩)
  have hTN : (T : Subgroup G) ≤ N := hH.1.1.2.trans (hHN.trans hNN)
  have hn : ¬ N ≤ normalizer (L : Set G) :=
    fun h => hH.1.2 (hHN.trans (hNN.trans h))
  apply Set.one_lt_ncard_iff_nontrivial_and_finite.mpr
  exact ⟨⟨N,⟨hN,hTN⟩,normalizer (L : Set G),
    ⟨hm,S.chosen.sylow_normalizes_component⟩,fun he => hn he.le⟩,Set.toFinite _⟩

include S in
private theorem omega_le_join_reduced {Y : Subgroup G}
    (hY : Y ∈ Chapter1.L G (T : Subgroup G)) :
    omegaCenterIn (T : Subgroup G) ≤ (reducedTwoSubgroup (Y ⊔ (T : Subgroup G) : Subgroup G)).map
      (Y ⊔ (T : Subgroup G)).subtype := by
  let J := Y ⊔ (T : Subgroup G)
  let U : Sylow 2 J := T.subtype le_sup_right
  have hc := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (S.hypothesis.simpleQTKE.evenCharacteristic T)
      ⟨hY.2.2, show (T : Subgroup G) ≤ J from le_sup_right⟩)
  have hh := map_mono (f := J.subtype) (sylow_omegaCenter_le_reduced U hc)
  change (Stellmacher.omegaOneCenterAmbient (U : Subgroup J)).map J.subtype ≤ _ at hh
  rw [← Stellmacher.omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective] at hh
  change Stellmacher.omegaOneCenterAmbient (((T : Subgroup G).subgroupOf J).map J.subtype) ≤ _ at hh
  rwa [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)] at hh

private theorem fitting_map_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  apply map_le_iff_le_comap.mp
  let := hnil
  exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩

private theorem common_odd_prime {A : Type*} [Group A] [Finite A]
    (h : A36Common A) (hn : ¬ IsQuasisimple A) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card (fittingSubgroup A) := by
  have hne : Nat.card (fittingSubgroup A) ≠ 1 := by
    intro he
    have hb : fittingSubgroup A = ⊥ := (card_le_one_iff_eq_bot _).mp he.le
    let := h.2.1
    exact hn (IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot))
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hne
  refine ⟨p, hp, ?_, hd⟩
  rcases hp.eq_two_or_odd' with rfl | ho
  · have hc := pPrimeCore_coprime_card (p := 2) (G := A)
    rw [← h.1] at hc
    have hh := Nat.dvd_gcd (dvd_refl 2) hd
    rw [hc] at hh
    norm_num at hh
  · exact ho

private theorem fitting_prime_transport {A B : Type*} [Group A] [Group B] [Finite B]
    (e : A ≃* B) {p : ℕ} (hd : p ∣ Nat.card (fittingSubgroup A)) :
    p ∣ Nat.card (fittingSubgroup B) := by
  rw [Nat.card_congr (e.subgroupMap (fittingSubgroup A)).toEquiv] at hd
  exact hd.trans (card_dvd_of_le (fitting_map_le e))

private theorem exists_odd_radical_prime
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h36 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ →
      ∀ C : Subgroup A, C.IsCComponent → A36Conclusion C)
    {Y : Subgroup G} (hY : Y ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (Y ⧸ pCore 2 Y)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card (fittingSubgroup (XiQuotient Y)) := by
  have hQ := uniqueness_local_quotient_sqtk hG hY.2.2
  let e := radicalLocalQuotientEquiv hY
  have hc := proposition_1_2_1_four_earlier_conclusion h36 hQ hY.1
  have hn' : ¬ IsQuasisimple (radicalLocalImage T Y) := by
    intro h
    let := h
    exact hn (IsQuasisimple.of_mulEquiv e.symm)
  obtain ⟨p,hp,ho,hd⟩ := common_odd_prime hc.2 hn'
  exact ⟨p,hp,ho,fitting_prime_transport e.symm hd⟩

include E in
/-- The canonical odd radical excludes nonquasisimple escaping overcomponents. -/
theorem nonquasisimple_overgroup_le_normalizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    {Y : Subgroup G} (hY : Y ∈ Chapter1.LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (Y ⧸ pCore 2 Y)) :
    Y ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  obtain ⟨p,hp,ho,hd⟩ := exists_odd_radical_prime S.hypothesis.simpleQTKE h36 hY.1 hn
  let : Fact p.Prime := ⟨hp⟩
  have hstar := Chapter3.RadicalCentralization.ChosenStars.XiP_mem_XiStar
    S.hypothesis.simpleQTKE T hY hn ho hd
  have hrad := Chapter3.RadicalCentralization.ChosenStars.maximal_solvableRadical_centralizes_sylowJoin
    S.hypothesis.simpleQTKE T (E.many_maximal_overgroups structural escape) hY hn
  have hXiZ : XiP p Y ≤ centralizer (omegaCenterIn (T : Subgroup G) : Set G) :=
    ((Chapter3.RadicalCentralization.XiP_le_solvableRadical Y p).trans hrad).trans
      (centralizer_le (omega_le_join_reduced (S := S) hY.1))
  have hXiM : XiP p Y ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le (hXiZ.trans (E.omega_center_centralizer_le_of_weight_six structural (fun z _ hz => E.source_weight_six_centralizer structural z hz)))
      S.chosen.sylow_normalizes_component
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
    S.hypothesis.simpleQTKE T S.hypothesis.maximal_faithful.1
  have hmax : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [S.chosen.localOrbit_eq] using hu.normalizer_maximal
  have he : normalizer (L : Set G) = normalizer (XiP p Y : Set G) := by
    have hh : normalizer (L : Set G) ∈
        {M : Subgroup G | IsMaximalTwoLocal M ∧ XiP p Y ⊔ (T : Subgroup G) ≤ M} :=
      ⟨hmax,hXiM⟩
    rw [(Chapter1.XiEmbedding.normalizer_unique_of_XiStar_knownSimple
      S.hypothesis.simpleQTKE T hstar).2] at hh
    exact Set.mem_singleton_iff.mp hh
  rw [he]
  exact sup_le (Y.le_normalizer.trans (normalizer_le_normalizer_XiP p Y)) hstar.1.invariant


end Setup.NaturalCoordinates
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
