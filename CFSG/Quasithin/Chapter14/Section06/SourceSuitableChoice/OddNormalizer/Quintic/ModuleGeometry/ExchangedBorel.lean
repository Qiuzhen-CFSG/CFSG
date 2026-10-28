module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ResidualExclusion
public import Theory.SpecificGroups.SL2.SolvableSylowCore
public import Theory.GroupTheory.SylowNormalJoinIntersection
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The actual Borel intersections in the exchanged quintic branch

The primitive residual makes the original H solvable. Each exchanged
PSL₂(16) component meets H in a solvable overgroup of its prescribed
Sylow intersection, whose two-core is exactly that intersection. Its
relative normalizer in H preserves this subgroup.

The closure K_z lies in O²(Mc), hence normalizes both components because
their Mc-normalizers have index two. The Sylow intersection with K_z
therefore splits into the two component intersections. O²(H) normalizes
both, and T normalizes their join; H = O²(H)T normalizes that join and
places it inside O₂(H). The final theorem constructs these facts for the
actual exchanged factors after the checked residual exclusion.

This supplies Borel placement for qt-e-14615-quintic-exclusion. The
support alignment, opposite-support centralization, conjugated point
centralizer and final p=3 proof remain with that owner. The original
14.6.12 factor-join index is retained as an earlier-source premise, owned
by qt-e-14612-singleton; earlier 14.6.13--14 inputs retain their stated
source owners and final discharge in the suitable-choice assembly.
Source: Aschbacher--Smith 14.6.15, printed pp.1033--1034.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentExclusion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)

include s in
private theorem original_H_le_partner : H ≤ Mc := by
  have he := (Section02.source_lemma_14_2_3 s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action H s.outside.1 s.outside.2).1
  exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2

include s in
/-- The elementary odd residual gives solvability of the original H. -/
theorem source_quintic_outside_solvable : Group.IsSolvable H := by
  let := s.primitive.elementary
  let Q := H ⧸ pCore 2 H
  let : Group.IsNilpotent (Q ⧸ pResidual 2 Q) :=
    (isPGroup_quotient_pResidual 2).isNilpotent
  let : Group.IsSolvable Q := (Group.isSolvable_iff_subgroup_quotient
    (pResidual 2 Q)).mpr ⟨inferInstance,inferInstance⟩
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 H)).mpr
    ⟨inferInstance,inferInstance⟩

private theorem sixteen_sl_not_solvable : ¬ Group.IsSolvable SL(2,GaloisField 2 4) := by
  let := Theory.PSL2.SixteenWreathComponents.perfect
  let := Theory.PSL2.SixteenWreathComponents.simple
  intro hs
  let := hs
  apply Group.IsPerfect.not_isSolvable Theory.PSL2.SixteenWreathComponents.L
  exact Group.isSolvable_of_surjective
    (f := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := GaloisField 2 4)).toMonoidHom)
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := GaloisField 2 4)).surjective

include s in
/-- The prescribed component Sylow intersection is the entire two-core of K ∩ H. -/
theorem source_exchanged_component_intersection_core {K : Subgroup G}
    (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.SixteenWreathComponents.L)) :
    (K ⊓ H).pCoreIn 2 = K ⊓ (T : Subgroup G) := by
  let HM := H.subgroupOf Mc
  let KM := K.subgroupOf Mc
  let hHM := original_H_le_partner s
  let hTM := s.outside.1.2.trans hHM
  let eK := subgroupOfEquivOfLe hKM
  let e := em.some.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL
    (F := GaloisField 2 4)).symm
  let q : KM →* SL(2,GaloisField 2 4) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 K)).comp eK.toMonoidHom)
  have hq : Function.Surjective q :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp eK.surjective)
  have hk : q.ker = (pCore 2 K).comap eK.toMonoidHom := by
    rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,
      ←MonoidHom.comap_ker,QuotientGroup.ker_mk']
  have hkp : IsPGroup 2 q.ker := by
    rw [hk]
    exact pCore_isPGroup.comap_of_injective _ eK.injective
  let : Group.IsSolvable H := source_quintic_outside_solvable s
  let eH := subgroupOfEquivOfLe hHM
  let : Group.IsSolvable HM := Group.isSolvable_of_isSolvable_injective
    (f := eH.toMonoidHom) eH.injective
  have hc := Matrix.SpecialLinearGroup.solvable_intersection_core
    (T.subtype hTM) KM HM hK.subnormal q hq hkp sixteen_sl_not_solvable
    (fun x hx => s.outside.1.2 hx)
  have hh := congrArg (Subgroup.map Mc.subtype) hc
  rw [map_pCoreIn_of_injective 2 _ _ Mc.subtype_injective,
    Subgroup.map_inf _ _ _ Mc.subtype_injective,
    Subgroup.map_inf _ _ _ Mc.subtype_injective,
    map_subgroupOf_eq_of_le hKM,map_subgroupOf_eq_of_le hHM,
    show ((T.subtype hTM : Sylow 2 Mc) : Subgroup Mc) =
      (T : Subgroup G).subgroupOf Mc from rfl,
    map_subgroupOf_eq_of_le hTM] at hh
  exact hh

include s in
/-- The relative component normalizer in H preserves the same Sylow intersection. -/
theorem source_exchanged_component_borel_control {K : Subgroup G}
    (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.SixteenWreathComponents.L)) :
    H ⊓ normalizer (K : Set G) ≤
      normalizer ((K ⊓ (T : Subgroup G) : Subgroup G) : Set G) := by
  rw [←source_exchanged_component_intersection_core s hKM hK em]
  exact ((le_inf inf_le_right (inf_le_left.trans H.le_normalizer)).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (K ⊓ H) (pCore 2 (K ⊓ H : Subgroup G)))

include s in
private theorem closure_le_partner_residual : residualClosure H Mc ≤ residual Mc := by
  apply conjugateSpanBy_le (embedded_pResidual_mono 2 (original_H_le_partner s))
  exact Mc.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Mc (pResidual 2 Mc))

variable (b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T))

include s in
/-- The actual closure normalizes both components, using their relative index two. -/
theorem source_exchanged_closure_normalizes_factors :
    residualClosure H Mc ≤ normalizer (b.K1 : Set G) ∧
      residualClosure H Mc ≤ normalizer (b.K2 : Set G) := by
  constructor
  · exact (closure_le_partner_residual s).trans
      ((residual_le_of_index_two (Mc ⊓ normalizer (b.K1 : Set G)) inf_le_left
        b.first_index).trans inf_le_right)
  · exact (closure_le_partner_residual s).trans
      ((residual_le_of_index_two (Mc ⊓ normalizer (b.K2 : Set G)) inf_le_left
        b.second_index).trans inf_le_right)

include s in
/-- The original Sylow intersection splits along the actual component pair. -/
theorem source_exchanged_closure_sylow_split :
    (T : Subgroup G) ⊓ residualClosure H Mc =
      (b.K1 ⊓ (T : Subgroup G)) ⊔ (b.K2 ⊓ (T : Subgroup G)) := by
  let Kz := residualClosure H Mc
  have hKM : Kz ≤ Mc := by
    change residualClosure H Mc ≤ Mc
    rw [←b.join_eq]
    exact sup_le b.first_le b.second_le
  have hn := source_exchanged_closure_normalizes_factors s b
  have h1 : b.K1 ≤ Kz := (le_sup_left : b.K1 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq
  have h2 : b.K2 ≤ Kz := (le_sup_right : b.K2 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq
  let KM := Kz.subgroupOf Mc
  let K1M := b.K1.subgroupOf Mc
  let K2M := b.K2.subgroupOf Mc
  let : KM.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let : (K1M.subgroupOf KM).Normal := normal_subgroupOf_of_le_normalizer (by
    intro x hx
    have hxN : (x : G) ∈ normalizer (b.K1 : Set G) := hn.1 hx
    have hh : x ∈ (normalizer (b.K1 : Set G)).subgroupOf Mc := hxN
    rwa [subgroupOf_normalizer_eq b.first_le] at hh)
  let : (K2M.subgroupOf KM).Normal := normal_subgroupOf_of_le_normalizer (by
    intro x hx
    have hxN : (x : G) ∈ normalizer (b.K2 : Set G) := hn.2 hx
    have hh : x ∈ (normalizer (b.K2 : Set G)).subgroupOf Mc := hxN
    rwa [subgroupOf_normalizer_eq b.second_le] at hh)
  have hj : K1M ⊔ K2M = KM := by
    rw [←subgroupOf_sup b.first_le b.second_le,b.join_eq]
  have hTM := s.outside.1.2.trans (original_H_le_partner s)
  have hh := (T.subtype hTM).inf_sup_eq_sup_inf_relative KM K1M K2M
    (fun x hx => h1 hx) (fun x hx => h2 hx) hj
  have hm := congrArg (Subgroup.map Mc.subtype) hh
  dsimp only [KM,K1M,K2M] at hm
  have hTm : ((T.subtype hTM : Sylow 2 Mc) : Subgroup Mc).map Mc.subtype =
      (T : Subgroup G) := map_subgroupOf_eq_of_le hTM
  simp only [Subgroup.map_sup,Subgroup.map_inf _ _ _ Mc.subtype_injective,
    hTm,map_subgroupOf_eq_of_le hKM,
    map_subgroupOf_eq_of_le b.first_le,map_subgroupOf_eq_of_le b.second_le] at hm
  simpa only [inf_comm] using hm

include s in
/-- The original residual preserves both component Sylow intersections. -/
theorem source_exchanged_residual_normalizes_sylow_factors :
    residual H ≤ normalizer ((b.K1 ⊓ (T : Subgroup G) : Subgroup G) : Set G) ∧
      residual H ≤ normalizer ((b.K2 ⊓ (T : Subgroup G) : Subgroup G) : Set G) := by
  have hn := source_exchanged_closure_normalizes_factors s b
  exact ⟨(le_inf (residual_le H) ((le_conjugateSpanBy _ _).trans hn.1)).trans
      (source_exchanged_component_borel_control s b.first_le b.first_component b.first_model),
    (le_inf (residual_le H) ((le_conjugateSpanBy _ _).trans hn.2)).trans
      (source_exchanged_component_borel_control s b.second_le b.second_component b.second_model)⟩

include s b in
/-- The original H normalizes its prescribed Sylow intersection with K_z. -/
theorem source_exchanged_closure_sylow_normalized :
    H ≤ normalizer (((T : Subgroup G) ⊓ residualClosure H Mc : Subgroup G) : Set G) := by
  have hRT : residual H ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (Subgroup.map H.subtype)
      (pResidual_sup_sylow_eq_top (T.subtype s.outside.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change residual H ⊔ (((T : Subgroup G).subgroupOf H).map H.subtype) = H at hh
    rwa [map_subgroupOf_eq_of_le s.outside.1.2] at hh
  have hR : residual H ≤
      normalizer (((T : Subgroup G) ⊓ residualClosure H Mc : Subgroup G) : Set G) := by
    rw [source_exchanged_closure_sylow_split s b]
    exact (le_inf (source_exchanged_residual_normalizes_sylow_factors s b).1
      (source_exchanged_residual_normalizes_sylow_factors s b).2).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hT : (T : Subgroup G) ≤
      normalizer (((T : Subgroup G) ⊓ residualClosure H Mc : Subgroup G) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      ((s.outside.1.2.trans (original_H_le_partner s)).trans
        (le_normalizer_conjugateSpanBy _ _))).trans inf_normalizer_le_normalizer_inf
  exact hRT.ge.trans (sup_le hR hT)

include s b in
/-- The actual product Sylow lies in O₂(H), without an additional Borel premise. -/
theorem source_exchanged_closure_sylow_le_core :
    (T : Subgroup G) ⊓ residualClosure H Mc ≤ H.pCoreIn 2 :=
  le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
    (inf_le_left.trans s.outside.1.2) (source_exchanged_closure_sylow_normalized s b)

include s in
/-- Construct the Borel geometry from Context and the checked residual exclusion. -/
theorem source_exchanged_borel_geometry :
    ∃ b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T),
      (b.K1 ⊓ H).pCoreIn 2 = b.K1 ⊓ (T : Subgroup G) ∧
      (b.K2 ⊓ H).pCoreIn 2 = b.K2 ⊓ (T : Subgroup G) ∧
      (T : Subgroup G) ⊓ residualClosure H Mc =
        (b.K1 ⊓ (T : Subgroup G)) ⊔ (b.K2 ⊓ (T : Subgroup G)) ∧
      H ≤ normalizer (((T : Subgroup G) ⊓ residualClosure H Mc : Subgroup G) : Set G) ∧
      (T : Subgroup G) ⊓ residualClosure H Mc ≤ H.pCoreIn 2 := by
  obtain ⟨b⟩ := source_exchanged_factor_data s
  exact ⟨b,source_exchanged_component_intersection_core s b.first_le b.first_component b.first_model,
    source_exchanged_component_intersection_core s b.second_le b.second_component b.second_model,
    source_exchanged_closure_sylow_split s b,source_exchanged_closure_sylow_normalized s b,
    source_exchanged_closure_sylow_le_core s b⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
