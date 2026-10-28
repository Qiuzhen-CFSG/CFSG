module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Preparation
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedAlternative
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Input

/-!
# C.2.4 on the fixed original centralizer

The original Q₁ is normal in M_Z, so it is Sylow in its M_Z-normal closure.
Restrict the original radical and characteristic-normalizer controls to G₁
and apply the intrinsic constrained-component alternative. The proof does
not infer characteristic two for G₁ from that property of the component:
the C.2.4 producer establishes characteristic two only in the required join.

Mapping the Sylow witness and normalizer back through G₁'s inclusion gives
the literal ambient alternative. Since Q₁ lies in S, the full-Sylow branch
is exactly S∩L ≤ Q₁. Excluding this branch supplies Q₁-normalization and
hence C.2.7, both before and after exchanged-plane selection.

The branch exclusion is deliberately still explicit. This module proves no
block reconstruction or exhaustiveness by assuming it in a certificate.
Source: Aschbacher--Smith C.2.4(2), p.144, and 15.1.20(2), pp.1094--1095.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

omit [Finite G] in
private theorem normal_core_sylow_closure (R N : Subgroup G)
    (hRN : R ≤ N) (hp : IsPGroup 2 R) (hn : N ≤ normalizer (R : Set G)) :
    IsSylowInNormalClosure R N := by
  let : (R.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hn
  unfold IsSylowInNormalClosure
  rw [normalClosure_eq_self]
  have hpR : IsPGroup 2 (R.subgroupOf N) := hp.comap_subtype
  let hp' : IsPGroup 2 (⊤ : Subgroup (R.subgroupOf N)) :=
    hpR.of_equiv topEquiv.symm
  let P : Sylow 2 (R.subgroupOf N) :=
    ⟨⊤, hp', fun _ htop => le_antisymm le_top htop⟩
  refine ⟨P, ?_⟩
  change ((⊤ : Subgroup (R.subgroupOf N)).map (R.subgroupOf N).subtype).map N.subtype = R
  rw [← MonoidHom.range_eq_map, range_subtype, map_subgroupOf_eq_of_le hRN]

/-- Apply C.2.4 to any constrained C-component in the original G₁. -/
theorem constrained_component_sylow_or_normalizes_of_radical_control
    (d : CaseIComponentData T M Mc V) (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hodd : pPrimeCore 2 d.G1 = ⊥)
    (hQne : d.Q1 ≠ ⊥)
    (hcontrol : d.Q1.characteristicNormalizerClosure ≤ Mc)
    (hnormalizer : d.G1 ⊓ normalizer (d.Q1 : Set G) = d.MZ)
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn d.G1)
    (hq : IsQuasisimple (B ⧸ pCore 2 B))
    (hfit : generalizedFitting B = pCore 2 B) :
    Chapter1.IsSylowIn 2 (d.Q1 ⊓ B) B ∨ d.Q1 ≤ normalizer (B : Set G) := by
  let := h.elementary
  let K := B.subgroupOf d.G1
  let R := d.Q1.subgroupOf d.G1
  let N := d.MZ.subgroupOf d.G1
  have hQG := d.Q1_le_MZ.trans (show d.MZ ≤ d.G1 from inf_le_left)
  have hRN : R ≤ N := fun _ hx => d.Q1_le_MZ hx
  have hn : N ≤ normalizer (R : Set d.G1) := by
    rw [← subgroupOf_normalizer_eq hQG]
    exact fun x hx => (d.MZ.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image d.MZ (pCore 2 d.MZ))) hx
  have hr := caseI_intrinsic_core_radical d.G1 d.MZ inf_le_left
    hQne hnormalizer
  have hsy := normal_core_sylow_closure R N hRN hr.isPGroup hn
  let e : K ≃* B := subgroupOfEquivOfLe hB.1
  let : IsQuasisimple (B ⧸ pCore 2 B) := hq
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hf : generalizedFitting K = pCore 2 K := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv, pCore_map_iso, hfit]
  have hqK : IsQuasisimple (K ⧸ pCore 2 K) := inferInstance
  rcases @Section04Constrained.sylow_intersection_or_normalizes_of_constrained
      d.G1 inferInstance inferInstance KnownSimple.IsKnownSimple
      (caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
        ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left)))
      R N K hr (caseI_intrinsic_characteristic_control d.G1 Mc d.Q1 hQG hcontrol)
      hsy hB.2 hqK hodd hf with ⟨P,hP⟩ | hnorm
  · left
    refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
    change ((P : Subgroup K).map e.toMonoidHom).map B.subtype = _
    have hm := congrArg (map d.G1.subtype) hP
    rw [map_map] at hm ⊢
    have he : B.subtype.comp e.toMonoidHom = d.G1.subtype.comp K.subtype := by
      ext x; rfl
    rw [he, hm]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact hy
    · rintro ⟨hxQ,hxL⟩
      exact ⟨⟨x,hQG hxQ⟩,⟨hxQ,hxL⟩,rfl⟩
  · right
    change d.Q1.subgroupOf d.G1 ≤ normalizer (B.subgroupOf d.G1 : Set d.G1) at hnorm
    rw [← subgroupOf_normalizer_eq hB.1] at hnorm
    intro x hx
    exact hnorm (show (⟨x,hQG hx⟩ : d.G1) ∈ R from hx)

/-- The literal Q₁ lies in S, using the singleton centralizer overgroup. -/
theorem catalogue_radical_le_sylow (d : CaseIComponentData T M Mc V)
    (hs : Chapter1.IsSylowIn 2 d.S d.G1)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    d.Q1 ≤ d.S := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hSM : d.S ≤ d.MZ := le_inf d.S_le_G1 (d.S_le_T.trans hTMc)
  obtain ⟨P,hP⟩ := hs.restrict hSM inf_le_left
  have hh := map_mono (f := d.MZ.subtype) (pCore_isPGroup.le_sylow_of_normal P)
  rwa [hP] at hh

private theorem not_sylow_intersection_of_not_contains
    (d : CaseIComponentData T M Mc V) (hQS : d.Q1 ≤ d.S)
    (B : Subgroup G) (hn : ¬ d.S ⊓ B ≤ d.Q1) :
    ¬ Chapter1.IsSylowIn 2 (d.Q1 ⊓ B) B := by
  intro hs
  have he := (Chapter1.isSylowIn_iff.mp hs).2.2 (d.S ⊓ B)
    (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T))
    (inf_le_inf_right B hQS) inf_le_right
  exact hn (he ▸ inf_le_left)

/-- The full-Sylow obstruction or actual Q₁-normalization, before row exclusions. -/
theorem PreExclusionSource.constrained_radical_alternative
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfit : generalizedFitting d.L = pCore 2 d.L) :
    d.SL ≤ d.Q1 ∨ d.Q1 ≤ normalizer (d.L : Set G) := by
  rcases d.constrained_component_sylow_or_normalizes_of_radical_control h hG
      s.odd_core s.core_nontrivial s.characteristic_control s.core_normalizer
      d.L_component s.quasisimple hfit with hs | hn
  · left
    by_contra hc
    exact not_sylow_intersection_of_not_contains d
      (d.catalogue_radical_le_sylow s.centralizer_sylow hu) d.L hc hs
  · exact Or.inr hn

/-- Removing the full-Sylow obstruction gives C.2.7 on the original component. -/
theorem PreExclusionSource.constrained_input_of_not_contains_sylow
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfit : generalizedFitting d.L = pCore 2 d.L)
    (hproper : ¬ d.SL ≤ d.Q1) :
    Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L :=
  s.constrained_input_of_normalizes (h := h) hG hfit
    ((s.constrained_radical_alternative (h := h) hG hu hfit).resolve_left hproper)

/-- The same normalization reduction applies to both exchanged-plane sizes. -/
theorem ExchangedSource.constrained_input_of_not_contains_sylow
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfit : generalizedFitting d.L = pCore 2 d.L)
    (hproper : ¬ d.SL ≤ d.Q1) :
    Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L := by
  have hn := (d.constrained_component_sylow_or_normalizes_of_radical_control h hG
    s.odd_core s.core_nontrivial s.characteristic_control s.core_normalizer
    d.L_component s.quasisimple hfit).resolve_left
      (not_sylow_intersection_of_not_contains d
        (d.catalogue_radical_le_sylow s.centralizer_sylow hu) d.L hproper)
  exact s.constrained_input_of_normalizes hG h hfit hn

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
