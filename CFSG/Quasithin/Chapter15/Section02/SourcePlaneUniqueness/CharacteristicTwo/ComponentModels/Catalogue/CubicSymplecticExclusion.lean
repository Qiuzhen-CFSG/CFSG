module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.CubicSevenExclusion
public import Theory.GroupTheory.Fitting.CentralCorePreimage

/-!
# The final cubic symplectic exclusion on the original component

The same selected A₆ component is normal in I. The original no-chi
hypothesis and C.2.6 put the Fitting preimage of I inside NI = M ∩ I.
Normal-inclusion functoriality therefore puts the full preimage of the
cubic center of X/O₂(X) inside NI.

The original K has three-rank two. Its image in X/O₂(X) contains that
center, since the ambient three-rank is at most two. Consequently the
cubic center is an image of K intersected with its central preimage.
This intersection lies in K ∩ M = O₂(K), a contradiction.

The source consumer applies this argument to the marked binary symplectic
row on the same X and full moved section supplied by CubicSevenExclusion.
It completes the component contradiction, retaining the original quotient,
Kc orbit, restricted action, plane inverter, no-chi and NI escape premises.
The final Source module discharges the latter two from the preliminary
block exclusions. No MS classification premise is used.

Source: Aschbacher--Smith, original 15.2.23, pp.1115--1117, C.2.6--7,
pp.145--147, and A.3.18; refs/quasithin.pdf.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
open Stellmacher Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree TerminalLinear
open ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include hsource in
/-- C.2.6 places the central core preimage of the same normal component
in the original NI = M ∩ I. Relative normality is inside I. -/
theorem normal_component_central_preimage_le_intersection
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) :
    centralCorePreimage X ≤ M ⊓ I := by
  let A := X.subgroupOf I
  let : A.Normal := normal_subgroupOf_of_le_normalizer hn
  let e : X ≃* A := (subgroupOfEquivOfLe hXI).symm
  let q := QuotientGroup.congr (pCore 2 X) (pCore 2 A) e (pCore_map_iso 2 e)
  have hF := (centralPreimage_twoCore_map_le_twoFittingCore A).trans
    (fittingCore_le_intersection_of_no_chi (hsource := hsource) hI hfit hcore hno)
  rintro x ⟨y,hy,rfl⟩
  change (⟨y,hXI y.property⟩ : I) ∈ (M ⊓ I).subgroupOf I
  apply hF
  refine ⟨e y,?_,rfl⟩
  change QuotientGroup.mk' (pCore 2 A) (e y) ∈ center (A ⧸ pCore 2 A)
  rw [←QuotientGroup.congr_mk' (pCore 2 X) (pCore 2 A) e (pCore_map_iso 2 e) y]
  exact (centerCongr q ⟨QuotientGroup.mk' (pCore 2 X) y,hy⟩).property

include d in
/-- The cubic A₆ cover contradicts the original two-group K ∩ M.
Rank two puts its center in the image of K, while C.2.6 puts the full
central preimage in M. -/
theorem normalized_cubicSix_false_of_no_chi
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (s : Normalized H M I X)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* alternatingGroup (Fin 6))
    (hz : Nat.card (center (X ⧸ pCore 2 X)) = 3) : False := by
  have hn : I ≤ normalizer (X : Set G) :=
    alternating_component_normalized (hsource := hsource) hI s.toSelected (by omega)
      (Or.inl rfl) (alternatingStarCoreCenterEquiv
        (normalized_component_input (hsource := hsource) hI hcore s) (by decide) e)
  let C := centralCorePreimage X
  let K := (pResidual 2 H).map H.subtype
  have hCM : C ≤ M :=
    (normal_component_central_preimage_le_intersection (hsource := hsource)
      hI hfit hcore hno s.component.1 hn).trans inf_le_left
  let q := QuotientGroup.mk' (pCore 2 X)
  have hKX : K ≤ X :=
    (alternating_star_residual_le_M1 d hI hcore s (Or.inl rfl) e).trans inf_le_left
  have hKrank : primeRank 3 ((K.subgroupOf X).map q) = 2 := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q
      (by rw [show q.ker = pCore 2 X from QuotientGroup.ker_mk' _]; exact pCore_isPGroup),
      primeRank_congr 3 (subgroupOfEquivOfLe hKX),residual_rank_two d]
  have hXrank : primeRank 3 (X ⧸ pCore 2 X) ≤ 2 := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup]
    exact (primeRank_mono 3 s.component.1).trans
      ((Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
        3 Nat.prime_three (by decide))
  have hcenter := cubic_center_le_of_three_rank_two _ hKrank.ge hXrank hz
  have ht : IsPGroup 2 (K ⊓ C : Subgroup G) := by
    apply (isPGroup_pCoreIn 2 K).to_le
    rw [←residual_intersection_eq_core d]
    exact inf_le_inf_left K hCM
  have hzle : center (X ⧸ pCore 2 X) ≤ ((K ⊓ C).subgroupOf X).map q := by
    intro z hz'
    obtain ⟨x,hx,he⟩ := hcenter hz'
    refine ⟨x,⟨hx,⟨x,?_,rfl⟩⟩,he⟩
    change q x ∈ center (X ⧸ pCore 2 X)
    rwa [he]
  have hzTwo : IsPGroup 2 (center (X ⧸ pCore 2 X)) :=
    ((ht.comap_subtype (K := X)).map q).to_le hzle
  obtain ⟨k,hk⟩ := hzTwo.exists_card_eq
  rw [hz] at hk
  have hd : 3 ∣ 2 ^ k := by rw [←hk]
  exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
include d in
/-- The last marked component row is excluded with all local premises discharged. -/
theorem source_component_false
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS) : False := by
  obtain ⟨X,s,hCJ,c,hc,⟨a⟩,hz,hr⟩ := exists_source_marked_cubicSymplectic_component
    d hquotient horbit hI hfit hno hNI ha hi
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  let eA := ((subgroupOfEquivOfLe hCJ).symm.trans a.subgroupEquiv).trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (F := ZMod 2) (by simp))
  exact normalized_cubicSix_false_of_no_chi d hI hfit hcore hno s eA hz

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue

