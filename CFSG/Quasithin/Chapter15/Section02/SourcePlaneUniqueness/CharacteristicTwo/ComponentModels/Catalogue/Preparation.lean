module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Preparation
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.CharacteristicTwo
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface

/-!
# The selected component and the remaining marked catalogue in 15.2.23

The literal C.2.4(2) dichotomy is applied to R = O₂(M ∩ I). The
full-Sylow alternative is removed conditionally on the chi-zero implication
of C.2.4(1), using the independent no-chi-block conclusion in I. This gives
one component normalized by both R and the original K = O²(H).

For this same component, the proved unrestricted C.2.7 extraction supplies
the kernel and offender conclusions, the full B.5.1 moved section, and
actual star-group identifications. The original core-to-star map and the
proper marked Thompson-normalizer overgroup are retained. In particular,
no Sylow-order bound is introduced.

The terminal `LinearAlternative` records exactly C.2.7(3)(g) and (h), with
their parabolic and MS clauses. No theorem here asserts its exhaustiveness.
The source-specific elimination of the other rows still requires the
marked C.2.7 catalogue. Its family projection is insufficient. The
chi-zero implication used by the conditional selection also remains an
upstream obligation; it is not a consequence of C.2.4(2).

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.2.23,
printed pp.1116--1117; C.2.4 and C.2.7, pp.144--147; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06
open Chapter1.RadicalExclusions
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

namespace ComponentCatalogue

variable {G : Type*} [Group G]

/-- The source component, with normality relative to I and with the original
embedded two-residual of H. No model alternative is a field. -/
structure Selected (H M I X : Subgroup G) : Prop where
  component : X ∈ Chapter1.cComponentsIn I
  quasisimple : IsQuasisimple (X ⧸ pCore 2 X)
  fitting : generalizedFitting X = pCore 2 X
  outside : ¬ X ≤ M ⊓ I
  residual_normalizes : (pResidual 2 H).map H.subtype ≤ normalizer (X : Set G)

/-- The extra conclusion needed before applying C.2.7. -/
structure Normalized (H M I X : Subgroup G) : Prop extends Selected H M I X where
  radical_normalizes : (M ⊓ I).pCoreIn 2 ≤ normalizer (X : Set G)

/-- The full-Sylow implication of C.2.4(1), specialized to this actual I and
NI. This is an explicit unproved premise of the conditional connector below. -/
@[expose] def FullSylowBlocks (M I : Subgroup G) : Prop :=
  ∀ X : Subgroup I, X.IsCComponent → IsQuasisimple (X ⧸ pCore 2 X) →
    generalizedFitting X = pCore 2 X → ¬ X ≤ (M ⊓ I).subgroupOf I →
    (∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype =
      ((M ⊓ I).pCoreIn 2).subgroupOf I ⊓ X) → ChapterC.IsChiZeroBlockIn X

/-- Exactly the two desired marked rows; the star quotient is never replaced
by the quotient of X by its two-core. -/
inductive LinearAlternative (X R N : Subgroup G) : Prop
  | linearThree (n : ℕ) (F : Type) [field : Field F] [finite : Finite F]
      (positive : 1 ≤ n) (field_card : Nat.card F = 2 ^ n)
      (parabolic : IsLinearMaximalParabolic
        ((starM X R N).subgroupOf (starImage X R X)) 3 F)
      (ms : MSDescription KnownSimple.IsKnownSimple X R n F)
  | binaryLinear (n : ℕ) (degree : n = 4 ∨ n = 5)
      (parabolic : IsBinaryPositiveRankParabolic
        ((starM X R N).subgroupOf (starImage X R X)) n)

/-- This adapter preserves every clause when the final reduction is consumed
by an existing C.2.7 case analysis. It is not a classification theorem. -/
theorem LinearAlternative.to_alternatives {X R N I : Subgroup G}
    (h : LinearAlternative X R N) :
    Alternatives KnownSimple.IsKnownSimple I X R N := by
  cases h with
  | linearThree n F hn hF hp hm => exact .linearThree n F hn hF hp hm
  | binaryLinear n hn hp => exact .binaryLinear n hn hp

variable [Finite G]

/-- Transport an intrinsic forbidden block back to the literal subgroup of I.
Subnormality comes from the selected component, not from ambient G. -/
theorem Selected.not_chi {H M I X : Subgroup G} (s : Selected H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y) : ¬ ChapterC.IsChiBlock X := by
  intro hc
  let e : X.subgroupOf I ≃* X := subgroupOfEquivOfLe s.component.1
  have hc' : ChapterC.IsChiBlock (X.subgroupOf I) := ChapterC.RankOne.ChiProduct.chi_of_equiv e.symm hc
  exact hno (X.subgroupOf I) ⟨⟨inferInstance,hc'.short,s.component.2.subnormal⟩,hc'⟩

/-- The non-chi subcases of the ordinary alternating row are precisely the
even degrees six and eight. The exceptional seven row is a different block. -/
theorem Selected.alternating_degree {H M I X : Subgroup G} (s : Selected H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    {n : ℕ} (hn : 5 ≤ n) (hu : n ≤ 8) (hb : ChapterC.IsAlternatingBlock X n) :
    n = 6 ∨ n = 8 := by
  have h5 : n ≠ 5 := by
    intro he
    exact s.not_chi hno (Or.inr ⟨n,by subst n; decide,hb⟩)
  have h7 : n ≠ 7 := by
    intro he
    exact s.not_chi hno (Or.inr ⟨n,by subst n; decide,hb⟩)
  omega

end ComponentCatalogue

namespace PlaneUniquenessPreceding
open ComponentCatalogue
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

omit [Finite G] in
private theorem normal_twoGroup_sylow_closure {A N : Subgroup G}
    (hAN : A ≤ N) (hn : N ≤ normalizer (A : Set G)) (hp : IsPGroup 2 A) :
    ChapterC.IsSylowInNormalClosure A N := by
  let B := A.subgroupOf N
  let : B.Normal := normal_subgroupOf_of_le_normalizer hn
  let C := normalClosure (B : Set N)
  have hC : C = B := Subgroup.normalClosure_eq_self B
  have hpC : IsPGroup 2 C := hC ▸ hp.comap_subtype
  have hpTop : IsPGroup 2 (⊤ : Subgroup C) :=
    hpC.of_injective (⊤ : Subgroup C).subtype (⊤ : Subgroup C).subtype_injective
  let P : Sylow 2 C := hpTop.toSylow (by simp)
  refine ⟨P,?_⟩
  change ((⊤ : Subgroup C).map C.subtype).map N.subtype = A
  rw [← MonoidHom.range_eq_map,range_subtype,hC,map_subgroupOf_eq_of_le hAN]

omit [Finite G] in
/-- The normal-closure convention in C.2.3 is checked inside I. The radical
is the core of NI, so its normal closure inside NI is itself. -/
theorem intersection_core_sylow_closure (M I : Subgroup G) :
    ChapterC.IsSylowInNormalClosure (((M ⊓ I).pCoreIn 2).subgroupOf I)
      ((M ⊓ I).subgroupOf I) := by
  have hRI : (M ⊓ I).pCoreIn 2 ≤ I := (pCoreIn_le 2 _).trans inf_le_right
  apply normal_twoGroup_sylow_closure
    (A := ((M ⊓ I).pCoreIn 2).subgroupOf I) (N := (M ⊓ I).subgroupOf I)
    (fun _ hx => pCoreIn_le 2 (M ⊓ I) hx) ?_ (isPGroup_pCoreIn 2 (M ⊓ I)).comap_subtype
  rw [← subgroupOf_normalizer_eq hRI]
  exact fun _ hx => ((M ⊓ I).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (M ⊓ I) (pCore 2 (M ⊓ I : Subgroup G)))) hx

include hsource in
/-- C.2.4(2) on the exact source radical, without any assumed normalization. -/
theorem component_sylow_intersection_or_normalizes
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Selected H M I X) :
    (∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = (M ⊓ I).pCoreIn 2 ⊓ X) ∨
      (M ⊓ I).pCoreIn 2 ≤ normalizer (X : Set G) := by
  have hs := intersection_pushingUpSetup (hsource := hsource) hI hcore
  let := s.quasisimple
  apply ChapterC.Section02Source.sylow_intersection_or_normalizes_in_of_characteristicTwo
    I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X hs.sqtk hs.radical_le s.component.1
    hs.radical hs.characteristic_control ?_ s.component.2
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
  exact intersection_core_sylow_closure M I

include d in
/-- The selected component and the actual C.2.4 dichotomy. No C.2.4(1)
premise is used to produce this disjunction. -/
theorem escaping_component_sylow_or_normalized
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y) :
    ∃ X : Subgroup G, Selected H M I X ∧
      ((∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = (M ⊓ I).pCoreIn 2 ⊓ X) ∨
        (M ⊓ I).pCoreIn 2 ≤ normalizer (X : Set G)) := by
  obtain ⟨X,hX,hq,hfX,hout,hn⟩ :=
    d.escaping_component_with_residual_normalization hI hfit f hf hker hno
  let s : Selected H M I X := ⟨hX,hq,hfX,hout,hn⟩
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  exact ⟨X,s,component_sylow_intersection_or_normalizes (hsource := hsource) hI hfit hcore s⟩

include hsource in
/-- Eliminate the full-Sylow branch using precisely the outstanding C.2.4(1)
chi-zero implication, followed by the independently produced block exclusion. -/
theorem component_normalized_of_fullSylow_blocks
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (hfull : FullSylowBlocks M I)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (s : Selected H M I X) : Normalized H M I X := by
  let Y := X.subgroupOf I
  let e : Y ≃* X := subgroupOfEquivOfLe s.component.1
  let := s.quasisimple
  have hq : IsQuasisimple (Y ⧸ pCore 2 Y) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hfitY : generalizedFitting Y = pCore 2 Y := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv, pCore_map_iso, s.fitting]
  have hout : ¬ Y ≤ (M ⊓ I).subgroupOf I := by
    intro hh
    exact s.outside (fun x hx => hh (show (⟨x,s.component.1 hx⟩ : I) ∈ Y from hx))
  have hs := intersection_pushingUpSetup (hsource := hsource) hI hcore
  let := hq
  have hnorm : ((M ⊓ I).pCoreIn 2).subgroupOf I ≤ normalizer (Y : Set I) := by
    rcases ChapterC.Section02Source.sylow_intersection_or_normalizes_of_characteristicTwo
      hs.sqtk _ _ Y hs.radical hs.characteristic_control
      (intersection_core_sylow_closure M I) s.component.2
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit) with hsy | hn
    · exact (hno Y (hfull Y s.component.2 hq hfitY hout hsy).chi).elim
    · exact hn
  refine ⟨s,?_⟩
  rw [← subgroupOf_normalizer_eq s.component.1] at hnorm
  intro r hr
  exact hnorm (show (⟨r,hs.radical_le hr⟩ : I) ∈
    ((M ⊓ I).pCoreIn 2).subgroupOf I from hr)

include d in
/-- The complete normalized selection conditional on the missing full-Sylow
block theorem. The action quotient still has its exact centralizer kernel. -/
theorem escaping_normalized_component_of_fullSylow_blocks
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hfull : FullSylowBlocks M I) :
    ∃ X : Subgroup G, Normalized H M I X := by
  obtain ⟨X,hX,hq,hfX,hout,hn⟩ :=
    d.escaping_component_with_residual_normalization hI hfit f hf hker hno
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  exact ⟨X,component_normalized_of_fullSylow_blocks (hsource := hsource) hI hfit hcore
    hfull hno ⟨hX,hq,hfX,hout,hn⟩⟩

include hsource in
/-- Construct the actual C.2.7 input from the normalized component. -/
theorem normalized_component_input (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X) :
    Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X :=
  ⟨intersection_pushingUpSetup (hsource := hsource) hI hcore,
    s.component,s.quasisimple,s.fitting,s.outside,s.radical_normalizes⟩

include hsource in
/-- Once normalization is established, the radical is not Sylow in XR:
C.1.29 would make the original component a forbidden chi-zero block. This
is the non-Sylow premise used in the marked C.2.7 source argument. -/
theorem normalized_component_not_sylow (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y) :
    ¬ Chapter1.IsSylowIn 2 ((M ⊓ I).pCoreIn 2) (X ⊔ (M ⊓ I).pCoreIn 2) := by
  intro hs
  have hb := ChapterC.C27Source.source_chiZero_of_sylow_input
    (normalized_component_input (hsource := hsource) hI hcore s) hs
  exact s.toSelected.not_chi hno hb.2.chi

include hsource in
/-- The unrestricted moved-section source applied to the selected component.
No upper bound on Sylow order and no model certificate is assumed. -/
theorem normalized_component_moved_section (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X) :
    let R := (M ⊓ I).pCoreIn 2
    let ρ := starRepresentation X R
    let J := Representation.BinaryOffender.offenderSubgroup ρ
    starImage X R X ≤ J ∧
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp J.subtype) ((starImage X R X).subgroupOf J)) :=
  ChapterC.C27Source.star_moved_section_from_source
    (normalized_component_input (hsource := hsource) hI hcore s)

include hsource in
/-- The source kernel and offender clauses for the same literal star map. -/
theorem normalized_component_kernel_offenders (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X) :
    KernelConclusion X ((M ⊓ I).pCoreIn 2) ∧ OffenderConclusion X ((M ⊓ I).pCoreIn 2) :=
  ChapterC.C27Source.kernel_offender_from_source
    (normalized_component_input (hsource := hsource) hI hcore s)

include hsource in
/-- Actual group isomorphisms from the full moved-section classification.
This family projection does not provide the missing marked parabolics. -/
theorem normalized_component_star_model (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X) :
    ChapterC.C27Source.StarModels.Model (starImage X ((M ⊓ I).pCoreIn 2) X) :=
  ChapterC.C27Source.star_model_from_source
    (normalized_component_input (hsource := hsource) hI hcore s)

include hsource in
/-- The core-to-star kernel is central; it is not silently set equal to one. -/
theorem normalized_component_coreToStar_central (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X) :
    (coreToStar s.radical_normalizes).ker ≤ center (X ⧸ pCore 2 X) :=
  ChapterC.C27Source.coreToStar_ker_central_from_source
    (normalized_component_input (hsource := hsource) hI hcore s)

include hsource in
/-- The source marked subgroup is proper and contains the actual Thompson
normalizer. These are consequences, not inputs to the catalogue. -/
theorem normalized_component_star_marking (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X) :
    let R := (M ⊓ I).pCoreIn 2
    starImage X R X ⊓ normalizer
      (starImage X R (elementaryAbelianMaxJ R) : Set (StarQuotient X R)) ≤ starM X R (M ⊓ I) ∧
      starM X R (M ⊓ I) < starImage X R X :=
  ChapterC.C27Source.star_thompson_intersection_from_source
    (normalized_component_input (hsource := hsource) hI hcore s)

end PlaneUniquenessPreceding
end CFSG.Quasithin.Chapter15.Section02
