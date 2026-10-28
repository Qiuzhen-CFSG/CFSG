module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawNormalizerQuotient
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.ClassicalNormality
public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even

/-!
# Original local core centers, normalization and exact classical covers

A.3.6 bounds the center of each actual local two-core quotient by one or
three. Odd rank two then forces normalization by the original marked Sylow.
The same bound and native classical-cover recognition make the actual
surjective central comparison map bijective for SL3 and Sp4. No component
record, M-generation, prior residual normalization or splitting is assumed.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- A.3.6 applies to the literal local two-core quotient. -/
theorem PreparedChosenModule.raw_local_core_center_card
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 K : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ≤ centralizer (Z1 : Set G)) (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    Nat.card (center (K ⧸ pCore 2 K)) = 1 ∨ Nat.card (center (K ⧸ pCore 2 K)) = 3 := by
  let := h.elementary
  let := hq
  let Q := K ⧸ pCore 2 K
  have hsq := caseI_centralizer_sqtk hG Z1 hZne
    ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
  have hKsq := (IsSQTK.equiv (subgroupOfEquivOfLe hK)).mp (hsq.subgroup (K.subgroupOf (centralizer (Z1 : Set G))))
  have hQsq : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_,hKsq.isKGroup.quotient (pCore 2 K)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 K) pCore_isPGroup).trans
      (hKsq.stronglyQuasithin p hp ho)
  have htop : (⊤ : Subgroup Q).IsCComponent :=
    (show IsComponent Q ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  have hc := (ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    Q hQsq (pCore_quotient_pCore_eq_bot 2) ⊤ htop).2
  let : IsQuasisimple (⊤ : Subgroup Q) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have hh := ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.center_card_of_common hc
  simpa only [Nat.card_congr (centerCongr (topEquiv : (⊤ : Subgroup Q) ≃* Q)).toEquiv] using hh

/-- The actual marked Sylow normalizes every local member of odd rank two. -/
theorem PreparedChosenModule.raw_local_normalizes_of_oddRank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 K : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 2 ≤ primeRank p (K ⧸ pCore 2 K)) :
    ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ normalizer (K : Set G) := by
  let := h.elementary
  let J := K ⊔ ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
  have hJG : J ≤ (centralizer (Z1 : Set G)) := sup_le hK.1 (show ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ centralizer (Z1 : Set G) from inf_le_right)
  have hsq := caseI_centralizer_sqtk hG Z1 hZne
    ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
  have hsqJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJG)).mp (hsq.subgroup (J.subgroupOf (centralizer (Z1 : Set G))))
  let ec : K.subgroupOf J ≃* K := subgroupOfEquivOfLe le_sup_left
  let eq := QuotientGroup.congr _ _ ec (pCore_map_iso 2 ec)
  let : IsQuasisimple ((K.subgroupOf J) ⧸ pCore 2 (K.subgroupOf J)) :=
    IsQuasisimple.of_mulEquiv eq.symm
  have hc : Nat.card (center ((K.subgroupOf J) ⧸ pCore 2 (K.subgroupOf J))) = 1 ∨
      Nat.card (center ((K.subgroupOf J) ⧸ pCore 2 (K.subgroupOf J))) = 3 := by
    rw [Nat.card_congr (centerCongr eq).toEquiv]
    exact h.raw_local_core_center_card hG T hZ hZne hK.1 hq
  have hr' : 2 ≤ primeRank p ((K.subgroupOf J) ⧸ pCore 2 (K.subgroupOf J)) := by
    rwa [primeRank_equiv p eq]
  have hn : (K.subgroupOf J).Normal := by
    by_cases h3 : p = 3
    · subst p
      exact hK.2.1.normal_of_cubic_core_center_threeRank
        (by
          rcases hc with hc | hc
          · exact hc.le.trans (by decide)
          · exact hc.le) hr'
        (hsqJ.stronglyQuasithin 3 Nat.prime_three (by decide))
    · let : Fact p.Prime := ⟨hp⟩
      apply hK.2.1.normal_of_coprime_core_center_primeRank ho _ hr'
        (hsqJ.stronglyQuasithin p hp ho)
      rcases hc with hc | hc
      · rw [hc]; exact Nat.coprime_one_right p
      · rw [hc]
        exact hp.coprime_iff_not_dvd.mpr (fun hd => h3
          ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd))
  exact (show ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ J from le_sup_right).trans
    ((normal_subgroupOf_iff_le_normalizer (show K ≤ J from le_sup_left)).mp hn)

/-- Every actual central comparison to SL3 is injective, including field four. -/
theorem PreparedChosenModule.raw_local_linearThree_cover_bijective
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 K : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ≤ centralizer (Z1 : Set G)) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type*} [Field F] [Finite F] (hF : 4 ≤ Nat.card F)
    (f : (K ⧸ pCore 2 K) →* SL(3,F)) (hf : Function.Surjective f)
    (hk : f.ker ≤ center (K ⧸ pCore 2 K)) : Function.Bijective f := by
  let := hq
  let c : PerfectCentralCovering.Cover (K ⧸ pCore 2 K) SL(3,F) :=
    ⟨f,hf,hq.toIsPerfect,hk⟩
  have hc : Nat.card (center (K ⧸ pCore 2 K)) ≤ Nat.card (center SL(3,F)) := by
    by_cases hfour : Nat.card F = 4
    · have hc : Nat.card (center SL(3,F)) = 3 := by
        rw [←Matrix.PSL3.projection_ker,Matrix.PSL3.card_projectionKernel,hfour]
        decide
      rw [hc]
      rcases h.raw_local_core_center_card hG T hZ hZne hK hq with he | he <;> omega
    · have hh := Matrix.PSL3.OrdinaryCenterRecognition.center_card_dvd
        (by omega : Nat.card F ≠ 2) hfour c.quotientCenterEquiv
      rw [←Matrix.PSL3.card_projectionKernel,Matrix.PSL3.projection_ker] at hh
      exact Nat.le_of_dvd Nat.card_pos hh
  have he := Nat.card_congr c.quotientCenterEquiv.toEquiv
  exact hf.bijective_of_nat_card_le (by
    calc
      Nat.card (K ⧸ pCore 2 K) =
          Nat.card ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) *
            Nat.card (center (K ⧸ pCore 2 K)) := card_eq_card_quotient_mul_card_subgroup _
      _ ≤ Nat.card (SL(3,F) ⧸ center SL(3,F)) * Nat.card (center SL(3,F)) := by
        rw [he]
        exact Nat.mul_le_mul_left _ hc
      _ = Nat.card SL(3,F) := (card_eq_card_quotient_mul_card_subgroup _).symm)

/-- Native even symplectic cover recognition applies to the literal core map. -/
theorem raw_local_symplectic_cover_bijective
    {K : Type*} [Group K] [Finite K] (hq : IsQuasisimple K)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    (f : K →* Theory.SpecificGroups.SymplecticFour.Sp F) (hf : Function.Surjective f)
    (hk : f.ker ≤ center K) : Function.Bijective f := by
  let c : PerfectCentralCovering.Cover K (Theory.SpecificGroups.SymplecticFour.Sp F) :=
    ⟨f,hf,hq.toIsPerfect,hk⟩
  exact ⟨Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.cover_injective (by omega) c,hf⟩

end CFSG.Quasithin.Chapter15.Section01
