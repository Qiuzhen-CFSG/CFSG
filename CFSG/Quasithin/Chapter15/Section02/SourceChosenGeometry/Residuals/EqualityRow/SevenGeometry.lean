module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.LinearRecognition
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.OriginalSeven

/-!
# The original moved subgroup inside the actual star module

The actual source radical geometry places U inside the star commutator.
Its noncentrality and the retained Irr⁺ conclusion force equality with that
whole moved subgroup.  These direct residual-input statements supply both
seven-letter terminal actions without a partner-residual identity.

Source: Aschbacher--Smith, proof of 15.2.23, printed pp.1116--1117,
refs/quasithin.pdf. The original U, QI and star markings are retained.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 ComponentCatalogue PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree TerminalLinear
open ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

/-- The original source moved subgroup retains its literal star embedding. -/
theorem ResidualInput.original_U_le_star_moved
    (r : ResidualInput hsource H B)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (h : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X) :
    (U X ⁅V,B⁆).subgroupOf (X ⊔ (M ⊓ I).pCoreIn 2) ≤
      ⁅starV X ((M ⊓ I).pCoreIn 2), X.subgroupOf (X ⊔ (M ⊓ I).pCoreIn 2)⁆ := by
  let R := (M ⊓ I).pCoreIn 2
  let J := X ⊔ R
  let W := (U X ⁅V,B⁆).subgroupOf J
  have hr := (EqualityRow.Linear.U_reduced_in_component_radical r hI hfit hXI hn hout h).1
  let := hr.elementary
  have hW : W ≤ starV X R := by
    intro w hw
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hr.le_pCore hw, ?_, hr.le_centralizer_pCore hw⟩
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) (⟨w,hw⟩ : W)
    exact congrArg W.subtype hh
  have hUJ : U X ⁅V,B⁆ ≤ J := (EqualityRow.Linear.U_le_intersection_radical r hI hfit hXI).trans le_sup_right
  have hm : ⁅W,X.subgroupOf J⁆ = W := by
    apply map_injective J.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hUJ,
      map_subgroupOf_eq_of_le (show X ≤ J from le_sup_left), EqualityRow.Linear.U_fully_moved r hI hfit h.component]
  exact hm.symm.le.trans (commutator_mono hW le_rfl)

/-- The original source moved subgroup retains its literal star embedding. -/
theorem ResidualInput.original_U_eq_star_moved
    (r : ResidualInput hsource H B)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (h : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hi : IsIrrPlus ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) s.space.toSubmodule) :
    (U X ⁅V,B⁆).subgroupOf (X ⊔ (M ⊓ I).pCoreIn 2) =
      ⁅starV X ((M ⊓ I).pCoreIn 2), X.subgroupOf (X ⊔ (M ⊓ I).pCoreIn 2)⁆ := by
  let R := (M ⊓ I).pCoreIn 2
  let J := X ⊔ R
  let C := X.subgroupOf J
  let Joff := offenderSubgroup (starRepresentation X R)
  let L := (starImage X R X).subgroupOf Joff
  let W := (U X ⁅V,B⁆).subgroupOf J
  let A : Submodule (ZMod 2) (Additive (starV X R)) :=
    AddSubgroup.toZModSubmodule 2 (W.subgroupOf (starV X R)).toAddSubgroup
  let ρ := (starRepresentation X R).comp Joff.subtype
  have hW := r.original_U_le_star_moved hI hfit hXI hn hout h
  have hs : s.space.toSubmodule = NormalElementaryQuotient.commutatorSpace (starV X R) C := by
    rw [NormalElementaryQuotient.commutatorSpace_eq (starV X R)
      (QuotientGroup.mk' (starKernel X R)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _), s.space_eq]
    change subspaceCommutator ρ ⊤ L = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCJ]
    rfl
  have hAS : A ≤ s.space.toSubmodule := by
    rw [hs]
    exact fun _ hu => hW hu
  have hstab : L ≤ subspaceStabilizer ρ A := by
    apply le_subspaceStabilizer
    intro l hl v hv
    obtain ⟨x,hx,he⟩ := hl
    have hlq : (l : StarQuotient X R) =
        QuotientGroup.mk' (starKernel X R) ⟨x,mem_sup_left hx⟩ := he.symm
    change ((starRepresentation X R l.val v).toMul : G) ∈ U X ⁅V,B⁆
    rw [hlq,starRepresentation_apply]
    exact (mem_normalizer_iff.mp
      (EqualityRow.Linear.U_normalized r hI hn (mem_sup_left hx)) _).mp hv
  have hnon : ¬ A ≤ fixedSpace ρ L := by
    intro hfix
    have hcentral : X ≤ centralizer (U X ⁅V,B⁆ : Set G) := by
      intro x hx u hu
      let uJ : J := ⟨u,(EqualityRow.Linear.U_le_intersection_radical r hI hfit hXI hu |> mem_sup_right)⟩
      let v : Additive (starV X R) := Additive.ofMul
        ⟨uJ,commutator_le_left _ _ (hW hu)⟩
      let l : L := (subgroupOfEquivOfLe hCJ).symm (toStarImage X R ⟨x,hx⟩)
      have hh := congrArg (fun w : Additive (starV X R) => (w.toMul.val : G))
        (hfix (show v ∈ A from hu) l)
      change (((starRepresentation X R
        (QuotientGroup.mk' (starKernel X R) ⟨x,mem_sup_left hx⟩) v).toMul : J) : G) = u at hh
      rw [starRepresentation_apply] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hred := EqualityRow.Linear.U_reduced_in_component_radical r hI hfit hXI hn hout h
    exact hred.2.2 (by
      rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
      intro x hx u hu
      exact Subtype.ext (hcentral hx u hu))
  have he : A = s.space.toSubmodule :=
    (hi.eq_or_le_fixedSpace ρ hstab hAS).resolve_right hnon
  apply le_antisymm hW
  intro w hw
  let v : Additive (starV X R) := Additive.ofMul ⟨w,commutator_le_left _ _ hw⟩
  have hv : v ∈ s.space.toSubmodule := by rw [hs]; exact hw
  exact (show v ∈ A from he ▸ hv)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
