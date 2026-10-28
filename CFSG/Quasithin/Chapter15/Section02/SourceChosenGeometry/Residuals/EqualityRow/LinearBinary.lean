module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.LinearRecognition
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.LinearOrthogonal
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.BinaryMarked

/-!
# The actual binary linear component exclusions in the equality row

Construct the marked positive-rank parabolic from the original star model.
Its component is O^{3′}(I), so it contains the actual rank-two wreath
residual. B.5 classifies the original moved module; LinearRows and
LinearOrthogonal exclude all four alternatives. The repeated-natural and
exterior endpoints are eliminated inside Mc by solvable cubic closure.

This proves the literal normalized L₄(2)/L₅(2) source branches without the
partner residual identity, any small-action packet, or an assumed module
classification. The earlier equality-row and no-chi producers retain
those exact inputs. Source: Aschbacher--Smith 15.2.23, pp.1116--1117.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRow.Linear
open Section01 PlaneUniquenessPreceding TerminalLinear ComponentCatalogue
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B0 I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : ResidualInput hsource H B0)

include d in
private theorem original_star_sylow
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I)
    (h : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X) :
    ∃ Q : Sylow 2 (starImage X ((M ⊓ I).pCoreIn 2) X),
      (Q : Subgroup _) ≤ (starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
        (starImage X ((M ⊓ I).pCoreIn 2) X) := by
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (d.sylow_in_escape_for_blocks hI) h.component.1 h.component.2.subnormal
  let R := (M ⊓ I).pCoreIn 2
  refine ⟨P.mapSurjective (toStarImage_surjective X R),?_⟩
  rintro y ⟨x,hx,rfl⟩
  have hxS : (x : G) ∈ planeSylow T ⁅V,B0⁆ :=
    (hP.le.trans inf_le_left) (mem_map_of_mem X.subtype hx)
  have hxM : (x : G) ∈ M := hsource.maximal.1.2 hxS.1
  exact mem_map_of_mem (QuotientGroup.mk' (starKernel X R))
    (show (x : G) ∈ (M ⊓ I) ⊓ X from ⟨⟨hxM,h.component.1 x.property⟩,x.property⟩)

include hsource in
private theorem binary_model_marking_not_two
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I)
    (h : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X)
    (hno : ¬ ChapterC.IsChiBlock X)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* SL(n,ZMod 2))
    (Q : Sylow 2 (starImage X ((M ⊓ I).pCoreIn 2) X))
    (hQ : (Q : Subgroup _) ≤ (starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
      (starImage X ((M ⊓ I).pCoreIn 2) X)) :
    ¬ IsPGroup 2 ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
      (starImage X ((M ⊓ I).pCoreIn 2) X)) := by
  intro hp
  let R := (M ⊓ I).pCoreIn 2
  let C := starImage X R X
  let P := (starM X R (M ⊓ I)).subgroupOf C
  let D := (M ⊓ I) ⊓ X
  let q := toStarImage X R
  have hinj := binary_model_coreToStar_injective h hn e
  have hker : q.ker = pCore 2 X := by
    ext x
    change q x = 1 ↔ x ∈ pCore 2 X
    constructor
    · intro hx
      apply (QuotientGroup.eq_one_iff x).mp
      change QuotientGroup.mk' (pCore 2 X) x = 1
      apply hinj
      rw [map_one,coreToStar_mk]
      exact hx
    · intro hx
      have he : QuotientGroup.mk' (pCore 2 X) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      change toStarImage X R x = 1
      rw [←coreToStar_mk h.normalizes,he,map_one]
  have hkp : IsPGroup 2 q.ker := by rw [hker]; exact pCore_isPGroup
  have hpre : IsPGroup 2 (P.comap q) := hp.comap_of_ker_isPGroup q hkp
  let j : D →* P.comap q := (inclusion (show D ≤ X from inf_le_right)).codRestrict _ (by
    intro x
    exact mem_map_of_mem (QuotientGroup.mk' (starKernel X R)) x.property)
  have hD : IsPGroup 2 D := hpre.of_injective j (by
    intro a b hab
    exact Subtype.ext (congrArg (fun y : P.comap q => (y.val : G)) hab))
  have hX : I ≤ normalizer (X : Set G) := by
    rw [binary_model_eq_threeResidual (hsource := hsource) hI h hn e]
    exact I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (primeToResidual 3 I))
  have hDnorm : M ⊓ I ≤ normalizer (D : Set G) :=
    (le_inf (M ⊓ I).le_normalizer (inf_le_right.trans hX)).trans
      inf_normalizer_le_normalizer_inf
  have hDR : D ≤ R := le_pCoreIn_of_normalizes hD inf_le_left hDnorm
  have hPR : P ≤ (starImage X R R).subgroupOf C := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hx
    exact ⟨y,hDR hy,he⟩
  let : (X.subgroupOf (X ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  obtain ⟨S,hS⟩ := radical_sylow_of_star_component_sylow (source_join_input h) Q
    (map_le_iff_le_comap.mpr (hQ.trans hPR))
  apply hno
  apply (source_chiZero_of_sylow_input h ?_).2.chi
  exact ⟨S,by rw [hS,map_subgroupOf_eq_of_le le_sup_right]⟩

include d in
/-- Construct the actual positive-rank marked binary parabolic from the original
Sylow intersection and the source no-chi conclusion. -/
theorem binary_model_marked_parabolic
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I)
    (h : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X)
    (hno : ¬ ChapterC.IsChiBlock X)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* SL(n,ZMod 2)) :
    IsBinaryPositiveRankParabolic
      ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
        (starImage X ((M ⊓ I).pCoreIn 2) X)) n := by
  obtain ⟨Q,hQ⟩ := original_star_sylow d hI h
  have hp := binary_model_marking_not_two (hsource := hsource) hI h hno hn e Q hQ
  have hproper : (starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
      (starImage X ((M ⊓ I).pCoreIn 2) X) ≠ ⊤ := by
    intro ht
    exact (star_thompson_intersection_from_source h).2.not_ge (subgroupOf_eq_top.mp ht)
  rcases hn with rfl | rfl
  · exact binaryPositiveRank_of_sylow_overgroup (m := 3) e _ Q hQ hproper hp
  · exact binaryPositiveRank_of_sylow_overgroup (m := 4) e _ Q hQ hproper hp


/-- All four literal original-U alternatives are impossible in the equality row. -/
theorem moduleRow_false_of_eq
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hKX : (pResidual 2 H).map H.subtype ≤ X) :
    letI := U_elementary d hI hfit hXI
    ModuleRow (U_representation d hI hfit hXI hn) → False := by
  let := U_elementary d hI hfit hXI
  intro hrow
  cases hrow with
  | repeatedNatural n r hd hp _ e =>
    rcases hd with rfl | rfl
    · exact not_repeatedNatural_four_canonical d hI hfit hXI hn hKX r hp ⟨e⟩
    · exact not_repeatedNatural_five_canonical_of_eq d he hI hfit hXI hn r hp ⟨e⟩
  | naturalDual n hd e =>
    exact not_naturalDual_canonical d hI hfit hXI hn hKX n hd e
  | orthogonalSix C hc e =>
    exact not_orthogonalSix_canonical d hI hfit hXI hn hout hKX C hc ⟨e⟩
  | exteriorFive r hr _ _ e =>
    exact not_exteriorFive_canonical_of_eq d he hI hfit hXI hn hr ⟨e⟩

include d in
/-- The marked binary branch has no remaining original-module alternative. -/
theorem binaryBranch_false_of_eq
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    {n : ℕ} (b : BinaryBranch M I X n) : False := by
  have hn := binary_normalized (hsource := hsource) hI b
  have hout := d.binary_linear_component_not_le_partner_of_eq he b
  have hKX : (pResidual 2 H).map H.subtype ≤ X := by
    rw [binary_eq_threeResidual (hsource := hsource) hI b]
    exact d.residual_le_threeResidual hI
  exact moduleRow_false_of_eq d he hI hfit b.source.component.1 hn hout hKX
    (moduleRow_of_binaryBranch d hI hfit hn hout b)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRow.Linear

namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 ComponentCatalogue PlaneUniquenessPreceding TerminalLinear
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B0 I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

/-- Original 15.2.23's normalized binary star rows, retaining the actual
selected X and radical O₂(M ∩ I), are excluded directly from ResidualInput. -/
theorem ResidualInput.normalized_binary_false_of_eq
    (d : ResidualInput hsource H B0) (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B0⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* SL(n,ZMod 2)) : False := by
  let hs := normalized_component_input (hsource := hsource) hI hcore s
  let b : BinaryBranch M I X n :=
    ⟨hs,hn,EqualityRow.Linear.binary_model_marked_parabolic d hI hs
      (s.toSelected.not_chi hno) hn e⟩
  exact EqualityRow.Linear.binaryBranch_false_of_eq d he hI hfit b

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
