module


public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.QuasisimpleAction
public import Theory.GroupTheory.CComponent.RadicalStabilizer
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents

/-!
# Relative C.2.7 restriction to the original `KR`

The C.2.3 source only gives `R ≤ N_H(K)`; it does not make `K` normal in the
larger ambient local group `H`.  This file therefore restricts the source to
`J = K ⊔ R`.  The component stabilizer-radical identity proves that the
restricted radical remains 2-radical, and all Sylow, characteristic-closure,
SQTK, fitting, outside, and normalizer fields transport to `J`.  Consequently
the proved C.2.7(1)--(2) kernel/offender and B.5 moved-section theorems can be
applied without adding an ambient-normality premise.

This is the literal relative normalizer step used before the C.2.7(3)
classification; no model tags or parabolic alternatives are inferred here.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

theorem source_relative_radical (h : Input κ H R M K) : IsPRadical 2 (R.subgroupOf (K ⊔ R)) := by
  let KH := K.subgroupOf H
  let RH := R.subgroupOf H
  let J := K ⊔ R
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  let : IsQuasisimple (KH ⧸ pCore 2 KH) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe h.component.1)
      (pCore_map_iso 2 (subgroupOfEquivOfLe h.component.1))).symm
  have hn : RH ≤ normalizer (KH : Set H) := by
    intro r hr
    apply mem_normalizer_iff.mpr
    intro k
    exact mem_normalizer_iff.mp (h.normalizes hr) (k : G)
  have hc := h.component.2.stabilizer_radical h.setup.radical
  change ((KH ⊔ (RH ⊓ normalizer (KH : Set H))) ⊓
    normalizer ((RH ⊓ normalizer (KH : Set H) : Subgroup H) : Set H)).pCoreIn 2 = _ at hc
  rw [inf_eq_left.mpr hn] at hc
  have hm := congrArg (map H.subtype) hc
  have hKR : (KH ⊔ RH).map H.subtype = J := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le h.component.1,
      map_subgroupOf_eq_of_le h.setup.radical_le]
  have he : ((KH ⊔ RH) ⊓ normalizer (RH : Set H)).map H.subtype =
      J ⊓ normalizer (R : Set G) := by
    rw [Subgroup.map_inf _ _ H.subtype H.subtype_injective,hKR,
      ←subgroupOf_normalizer_eq h.setup.radical_le,subgroupOf_map_subtype]
    exact le_antisymm (inf_le_inf_left _ inf_le_left)
      (fun x hx => ⟨hx.1,hx.2,h.join_le hx.1⟩)
  rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,he,
    map_subgroupOf_eq_of_le h.setup.radical_le] at hm
  refine ⟨?_,?_⟩
  · intro hb
    have hRbot : R = ⊥ := by
      have hh := congrArg (map J.subtype) hb
      change map J.subtype (R.subgroupOf J) = map J.subtype ⊥ at hh
      rw [map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right),Subgroup.map_bot] at hh
      exact hh
    exact h.setup.radical.1 (by rw [hRbot,bot_subgroupOf])
  · change (normalizer (R.subgroupOf J : Set J)).pCoreIn 2 = R.subgroupOf J
    apply map_injective J.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ J.subtype J.subtype_injective,
      ←subgroupOf_normalizer_eq (show R ≤ J from le_sup_right),subgroupOf_map_subtype,
      inf_comm,hm,map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right)]

theorem source_join_input (h : Input κ H R M K) : Input κ (K ⊔ R) R (M ⊓ (K ⊔ R)) K := by
  let J := K ⊔ R
  let M' := M ⊓ J
  have hRM : R ≤ M := (Chapter1.isSylowIn_iff.mp h.setup.sylow).2.1.trans (map_subtype_le _)
  have hRM' : R ≤ M' := le_inf hRM le_sup_right
  have hRmap : (R.subgroupOf J).map (inclusion h.join_le) = R.subgroupOf H := by
    ext r
    constructor
    · rintro ⟨s,hs,rfl⟩; exact hs
    · intro hr; exact ⟨⟨r,mem_sup_right hr⟩,hr,rfl⟩
  have hcontrol : (R.subgroupOf J).characteristicNormalizerClosure ≤ M'.subgroupOf J := by
    intro x hx
    have hh := map_characteristicNormalizerClosure_le (inclusion h.join_le)
      (inclusion_injective h.join_le) (R.subgroupOf J)
    rw [hRmap] at hh
    exact ⟨h.setup.characteristic_control (hh (mem_map_of_mem _ hx)),x.property⟩
  have hsy : Chapter1.IsSylowIn 2 R ((normalClosure (R.subgroupOf M' : Set M')).map M'.subtype) := by
    apply h.setup.sylow.restrict
    · calc
        R = (R.subgroupOf M').map M'.subtype := (map_subgroupOf_eq_of_le hRM').symm
        _ ≤ _ := map_mono le_normalClosure
    · let f := inclusion (show M' ≤ M from inf_le_left)
      have hh := map_normalClosure_le (R.subgroupOf M' : Set M') f
      have hs : f '' (R.subgroupOf M' : Set M') ⊆ (R.subgroupOf M : Set M) := by
        rintro _ ⟨r,hr,rfl⟩; exact hr
      have ht := map_mono (f := M.subtype) (hh.trans (normalClosure_mono hs))
      rw [Subgroup.map_map] at ht
      exact ht
  refine ⟨⟨?_,le_sup_right,inf_le_right,source_relative_radical h,hcontrol,hsy⟩,
    ⟨le_sup_left,h.component.2.subgroupOf_of_le le_sup_left h.join_le⟩,
    h.quasisimple,h.fitting,fun hh => h.outside (hh.trans inf_le_left),h.normalizes⟩
  exact (IsSQTK.equiv (subgroupOfEquivOfLe h.join_le)).mp (h.setup.sqtk.subgroup _)

theorem kernel_offender_from_source (h : Input κ H R M K) :
    KernelConclusion K R ∧ OffenderConclusion K R := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  exact kernel_offender_of_normal_input (source_join_input h)

theorem star_moved_section_from_source (h : Input KnownSimple.IsKnownSimple H R M K) :
    let ρ := starRepresentation K R
    let J := Representation.BinaryOffender.offenderSubgroup ρ
    starImage K R K ≤ J ∧
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp J.subtype) ((starImage K R K).subgroupOf J)) := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  simpa only using (star_moved_section_conclusion (source_join_input h))
end CFSG.Quasithin.ChapterC.C27Source
