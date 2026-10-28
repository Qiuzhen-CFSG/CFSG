module

public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RankOneGeometry
public import Theory.GroupTheory.SylowNormalSupplementRecognition

/-!
# Lifting the rank-one Sylow conclusion through the odd central kernel

A component Sylow in the image of J(R) makes R* Sylow in K*R* by the
normal-supplement criterion. Extend the original R to a Sylow P. Their
images coincide, and P meets the star kernel exactly in O₂(KR), already
inside R. Every element of P therefore lies in R. This retains the possible
odd central kernel and proves Sylow status for the original subgroup.

Source: Aschbacher–Smith C.2.7(3)(a), printed p.146.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

theorem radical_sylow_of_thompson_sylow
    (h : Input κ H R M K) [(K.subgroupOf H).Normal]
    (S : Sylow 2 (starImage K R K))
    (hS : (S : Subgroup _).map (starImage K R K).subtype = starImage K R (elementaryAbelianMaxJ R)) :
    ∃ P : Sylow 2 (K ⊔ R : Subgroup G),
      (P : Subgroup _) = R.subgroupOf (K ⊔ R) := by
  let D := K ⊔ R
  let R₀ := R.subgroupOf D
  let C := starImage K R K
  let q := QuotientGroup.mk' (starKernel K R)
  let : (K.subgroupOf D).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  let : C.Normal := (inferInstance : (K.subgroupOf D).Normal).map q
    (QuotientGroup.mk'_surjective _)
  have hR : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  have hSle : (S : Subgroup C).map C.subtype ≤ starImage K R R := by
    rw [hS]
    exact map_mono (comap_mono (sSup_le fun _ hA => hA.1))
  obtain ⟨T,hT⟩ := exists_sylow_eq_of_normal_supplement C (starImage K R R)
    (hR.comap_subtype.map q) (starImage_sup_eq_top K R) S hSle
  obtain ⟨P,hRP⟩ := hR.comap_subtype.exists_le_sylow (P := R₀)
  have hTP : (T : Subgroup (StarQuotient K R)) ≤ (P : Subgroup D).map q := by
    rw [hT]
    exact map_mono hRP
  have hPm : (P : Subgroup D).map q = R₀.map q :=
    (T.is_maximal' (P.isPGroup'.map q) hTP).trans hT
  have hQR : pCore 2 D ≤ R₀ := fun x hx => source_joinCore_le_radical h
    (mem_map_of_mem D.subtype hx)
  have hPN := twoSubgroup_inf_starKernel_of_normal_input h (P : Subgroup D)
    P.isPGroup' (hQR.trans hRP)
  refine ⟨P,le_antisymm ?_ hRP⟩
  intro x hx
  have hximage : q x ∈ R₀.map q := hPm ▸ mem_map_of_mem q hx
  obtain ⟨r,hr,he⟩ := hximage
  have hxn : x*r⁻¹ ∈ starKernel K R := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (x*r⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hxQ : x*r⁻¹ ∈ pCore 2 D := hPN ▸
    (show x*r⁻¹ ∈ (P : Subgroup D) ⊓ starKernel K R from
      ⟨P.mul_mem hx (P.inv_mem (hRP hr)),hxn⟩)
  simpa only [inv_mul_cancel_right] using R₀.mul_mem (hQR hxQ) hr

open Representation Representation.BinaryOffender ChapterB.QuasisimpleSource
open scoped IsMulCommutative MatrixGroups

theorem rankOne_source_geometry
    (h : Input κ H R M K) [(K.subgroupOf H).Normal]
    (hCJ : starImage K R K ≤ offenderSubgroup (starRepresentation K R))
    (s : MovedSection ((starRepresentation K R).comp (offenderSubgroup (starRepresentation K R)).subtype)
      ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))))
    (F : BinaryField) (e : starImage K R K ≃* SL(2,F.Carrier))
    (hratio : quadraticRatio s.action = 1)
    (hoff : ∀ B, IsBestOffender s.action B →
      ∃ S : Sylow 2 ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))),
        B = (S : Subgroup _).map
          ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))).subtype) :
    Chapter1.IsSylowIn 2 (starImage K R (elementaryAbelianMaxJ R)) (starImage K R K) ∧
      IsRankOneBorel (starImage K R K) (starM K R M) ∧ Chapter1.IsSylowIn 2 R (K ⊔ R) := by
  obtain ⟨S,hS⟩ := rankOne_thompson_sylow_of_row h hCJ s hratio hoff
  obtain ⟨P,hP⟩ := radical_sylow_of_thompson_sylow h S hS
  refine ⟨⟨S,hS⟩,rankOne_borel_of_thompson_sylow h F e S hS,⟨P,?_⟩⟩
  rw [hP,map_subgroupOf_eq_of_le (show R ≤ K ⊔ R from le_sup_right)]

theorem rankOne_row_geometry
    (h : Input κ H R M K) [(K.subgroupOf H).Normal]
    (hCJ : starImage K R K ≤ offenderSubgroup (starRepresentation K R))
    (s : MovedSection ((starRepresentation K R).comp (offenderSubgroup (starRepresentation K R)).subtype)
      ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))))
    (F : BinaryField)
    (natural : ActionEquiv
      (s.action.comp ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))).subtype)
      (linearNatural F 2))
    (hratio : quadraticRatio s.action = 1)
    (hoff : ∀ B, IsBestOffender s.action B →
      ∃ S : Sylow 2 ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))),
        B = (S : Subgroup _).map
          ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))).subtype) :
    Chapter1.IsSylowIn 2 (starImage K R (elementaryAbelianMaxJ R)) (starImage K R K) ∧
      IsRankOneBorel (starImage K R K) (starM K R M) ∧ Chapter1.IsSylowIn 2 R (K ⊔ R) := by
  let e : starImage K R K ≃* SL(2,F.Carrier) :=
    (subgroupOfEquivOfLe hCJ).symm.trans natural.groupEquiv
  exact rankOne_source_geometry h hCJ s F e hratio hoff

end CFSG.Quasithin.ChapterC.C27Source

