module

public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.StarRadical
public import CFSG.Quasithin.ChapterC.Section02.RankOneOffenders
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry
public import Theory.SpecificGroups.SL2.ResidualSylowGeneration

/-!
# The marked Sylow and Borel in the rank-one B.5 row

Apply the original ratio-one best-offender row to the maximum elementary
subgroups of R. Their images generate the literal J(R)* and coincide with
a Sylow subgroup of K*. The source normalizer restriction then places its
normalizer inside the proper marked intersection M_K*. The rank-one matrix
overgroup theorem identifies that intersection with the Borel normalizer.
The possible odd central star kernel is retained throughout.

Source: Aschbacher–Smith C.2.7(3)(a)(i), printed p.146. The row data are
supplied by the genuine B.5 source conclusion; block reconstruction is separate.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

theorem rankOne_thompson_sylow_of_row
    (h : Input κ H R M K) [(K.subgroupOf H).Normal]
    (hCJ : starImage K R K ≤ offenderSubgroup (starRepresentation K R))
    (s : MovedSection ((starRepresentation K R).comp (offenderSubgroup (starRepresentation K R)).subtype)
      ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))))
    (hratio : quadraticRatio s.action = 1)
    (hoff : ∀ B, IsBestOffender s.action B →
      ∃ S : Sylow 2 ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))),
        B = (S : Subgroup _).map
          ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))).subtype) :
    ∃ S : Sylow 2 (starImage K R K),
      (S : Subgroup _).map (starImage K R K).subtype = starImage K R (elementaryAbelianMaxJ R) := by
  let D := K ⊔ R
  let R₀ := R.subgroupOf D
  let q := QuotientGroup.mk' (starKernel K R)
  have hR : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  have hQR : pCore 2 D ≤ R₀ := fun x hx => source_joinCore_le_radical h
    (mem_map_of_mem D.subtype hx)
  have hVR : starV K R ≤ R₀ := (map_subtype_le _).trans hQR
  have hn : ¬elementaryAbelianMaxJ R₀ ≤ q.ker := by
    simpa only [q,QuotientGroup.ker_mk'] using thompson_not_le_starKernel_of_normal_input h
  have hs := thompson_image_sylow_of_bestOffenders (starV K R) R₀ hR.comap_subtype hVR q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hn (starImage K R K)
    (fun _ ha => bestOffender_sylow_of_ratio_one_row
      (starRepresentation K R) (starImage K R K) hCJ s hratio hoff ha)
  have hJR : elementaryAbelianMaxJ R ≤ D :=
    (sSup_le fun _ hA => hA.1).trans (show R ≤ D from le_sup_right)
  have hJ : elementaryAbelianMaxJ R₀ = (elementaryAbelianMaxJ R).subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [←elementaryAbelianMaxJ_map_injective D.subtype D.subtype_injective,
      map_subgroupOf_eq_of_le (show R ≤ D from le_sup_right),map_subgroupOf_eq_of_le hJR]
  simpa only [hJ,starImage] using hs

private theorem rankOne_normalizer_overgroup
    {A : Type*} [Group A] [Finite A] (F : BinaryField)
    (e : A ≃* SL(2,F.Carrier)) (S : Sylow 2 A)
    (P : Subgroup A) (hP : P ≠ ⊤) (hn : normalizer (S : Set A) ≤ P) :
    P = normalizer (S : Set A) := by
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hSP : (S' : Subgroup SL(2,F.Carrier)) ≤ P.map e.toMonoidHom :=
    map_mono ((S : Subgroup A).le_normalizer.trans hn)
  have hproper : P.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hP
    have hh := congrArg (comap e.toMonoidHom) he
    simpa only [comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective,comap_top] using hh
  have hh := Matrix.SpecialLinearGroup.overgroup_le_sylowNormalizer S' hSP hproper
  have he : normalizer (S' : Set SL(2,F.Carrier)) =
      (normalizer (S : Set A)).map e.toMonoidHom :=
    (map_normalizer_eq_of_bijective _ e.bijective).symm
  rw [he] at hh
  exact le_antisymm ((map_le_map_iff_of_injective e.injective).mp hh) hn

theorem rankOne_borel_of_thompson_sylow
    (h : Input κ H R M K) [(K.subgroupOf H).Normal]
    (F : BinaryField) (e : starImage K R K ≃* SL(2,F.Carrier))
    (S : Sylow 2 (starImage K R K))
    (hS : (S : Subgroup _).map (starImage K R K).subtype = starImage K R (elementaryAbelianMaxJ R)) :
    IsRankOneBorel (starImage K R K) (starM K R M) := by
  let C := starImage K R K
  let P := (starM K R M).subgroupOf C
  have hm := star_thompson_intersection_of_normal_input h
  have hproper : P ≠ ⊤ := by
    intro he
    exact hm.2.not_ge (subgroupOf_eq_top.mp he)
  have hn : normalizer (S : Set C) ≤ P := by
    intro x hx
    have hxN : (x : StarQuotient K R) ∈ normalizer
        (starImage K R (elementaryAbelianMaxJ R) : Set (StarQuotient K R)) := by
      rw [←hS]
      exact (S : Subgroup C).le_normalizer_map C.subtype ⟨x,hx,rfl⟩
    exact hm.1 ⟨x.property,hxN⟩
  refine ⟨S,?_⟩
  have he := congrArg (map C.subtype) (rankOne_normalizer_overgroup F e S P hproper hn)
  rwa [map_subgroupOf_eq_of_le (starM_le K R M)] at he

end CFSG.Quasithin.ChapterC.C27Source
