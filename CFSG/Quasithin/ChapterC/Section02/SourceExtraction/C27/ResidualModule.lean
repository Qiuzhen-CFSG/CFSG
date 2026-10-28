module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Quotients
public import Theory.GroupTheory.PCoreOmegaMovement
public import Theory.GroupTheory.GeneralizedFitting.ResidualOvergroups

/-!
# Moving the ambient omega-center into the literal star module

For C=O²(I) and J=CR, a C-moved I-module in Ω₁Z(O₂(I)) lies in C.
The overgroup J is subnormal, so O₂(J) lies in O₂(I). Normality and
centrality then put the same module in Ω₁Z(O₂(J)), the star module used
by C.2.7. Taking commutators retains the original C-action.

This is used by the generated-parabolic argument of 14.6.10(5), printed
p.1029, to apply B.5 directly to its plane span.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction
variable {G : Type*} [Group G] [Finite G]

/-- A moved central core module restricts to the star module of any
residual overgroup; subnormality supplies the needed core comparison. -/
theorem residual_moved_omegaCore_le_star_module (I R U : Subgroup G)
    (hRI : R ≤ I)
    (hIU : I ≤ normalizer (U : Set G))
    (hU : U ≤ omegaOneCenterAmbient (I.pCoreIn 2))
    (hm : ⁅U,(pResidual 2 I).map I.subtype⁆ = U) :
    let C := (pResidual 2 I).map I.subtype
    U ≤ (⁅starV C R, C.subgroupOf (C ⊔ R)⁆).map (C ⊔ R : Subgroup G).subtype := by
  let C := (pResidual 2 I).map I.subtype
  let J := C ⊔ R
  have hCI : C ≤ I := map_subtype_le _
  have hJI : J ≤ I := sup_le hCI hRI
  have hIC : I ≤ normalizer (C : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  have hUI : U ≤ I := fun x hx => pCoreIn_le 2 I
    ((mem_omegaOneCenterAmbient_iff _ x).mp (hU hx)).1
  have hUC : U ≤ C := hm ▸ le_normalizer_iff_commutator_le_right.mp (hUI.trans hIC)
  have hUJ : U ≤ J := hUC.trans le_sup_left
  have hJsub : (J.subgroupOf I).IsSubnormal :=
    residual_overgroup_subnormal _ (fun x hx => mem_sup_left (mem_map_of_mem I.subtype hx))
  have hQ : J.pCoreIn 2 ≤ I.pCoreIn 2 := by
    have hh := map_mono (f := I.subtype) (pCoreIn_le_of_subnormal 2 hJsub)
    rw [map_pCoreIn_of_injective 2 _ I.subtype I.subtype_injective,
      map_subgroupOf_eq_of_le hJI] at hh
    exact hh
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (I.pCoreIn 2)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  have hp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 _).to_le hU
  have hUQ : U ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes hp hUJ (hJI.trans hIU)
  have hUΩ : U ≤ omegaOneCenterAmbient (J.pCoreIn 2) := by
    intro x hx
    obtain ⟨_,h2,hc⟩ := (mem_omegaOneCenterAmbient_iff _ x).mp (hU hx)
    exact (mem_omegaOneCenterAmbient_iff _ x).mpr
      ⟨hUQ hx,h2,fun q hq => hc q (hQ hq)⟩
  have he : (starV C R).map J.subtype = omegaOneCenterAmbient (J.pCoreIn 2) := by
    change (omegaOneCenterAmbient (pCore 2 J)).map J.subtype = _
    exact (omegaOneCenterAmbient_map_injective _ J.subtype_injective (pCore 2 J)).symm
  dsimp only
  rw [map_commutator,map_subgroupOf_eq_of_le (show C ≤ J from le_sup_left)]
  exact hm ▸ commutator_mono (hUΩ.trans_eq he.symm) le_rfl

end CFSG.Quasithin.ChapterC.C27Source
