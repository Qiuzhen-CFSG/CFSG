module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.PushingUpModuleControl
public import Theory.SpecificGroups.Janko4.Model.LinearFiveRadicalBound
/-!
# The original radical splits over the exterior module

Project the full component through its center. The actual PSL₅(2) section
bounds the image of R intersect K by 1024, and the original exterior
module embeds with exactly that order. Equality lifts with the full
covering center retained. Combining this with radical saturation yields
R = V times C_R(K), with trivial intersection and nontrivial second factor.
This is the direct product needed to select a fixed involution modulo V.

Source: Aschbacher--Smith 4.2.13, printed p.612.
-/
public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Subgroup Theory.GroupTheory
open Chapter4 Chapter4.Section04 Chapter12.Section02
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The literal component-radical intersection projects exactly onto the
original exterior module through the full covering center. -/
theorem exterior_pushingUp_radical_quotient_eq
    (s : SylowExteriorMarking D) {A J H W : Subgroup G}
    (hw : Witness L V A J H W) (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let Kg := K.map H.subtype
    let q := (centerQuotientCongr
      (K.equivMapOfInjective H.subtype H.subtype_injective).symm).trans e
    let π := q.toMonoidHom.comp (QuotientGroup.mk' (center Kg))
    let U := ((J.pCoreIn 2).subgroupOf Kg).map π
    let E := (V.subgroupOf Kg).map π
    U = E ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 1024 := by
  let R := J.pCoreIn 2
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let Kg := K.map H.subtype
  let eq := (centerQuotientCongr
      (K.equivMapOfInjective H.subtype H.subtype_injective).symm).trans e
  let π := eq.toMonoidHom.comp (QuotientGroup.mk' (center Kg))
  let U := (R.subgroupOf Kg).map π
  let E := (V.subgroupOf Kg).map π
  have hc := hw.2.2.2.2.2.2.1
  let := hc.ordinary_component_normal K hK
  let := hK.2
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFK : F ≤ Kg := by
    have hh := map_mono (f := H.subtype) (hc.ordinary_component_contains_original K hK)
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  have hVF : V ≤ F := hw.2.2.2.2.2.2.2.2.2.2.1
  have hVK := hVF.trans hFK
  have hFL : F ≤ L := (map_subtype_le _).trans inf_le_left
  have hVR : V ≤ R := hw.2.2.2.2.2.1
  have hFR : F ≤ normalizer (R : Set G) :=
    (le_conjugateSpanBy _ _).trans hc.span_normalizes_radical
  have hZK : IsPGroup 2 (center K) := by
    rw [IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)]
    exact pCore_isPGroup
  have hZ : IsPGroup 2 (center Kg) :=
    hZK.of_equiv (centerCongr (K.equivMapOfInjective H.subtype H.subtype_injective))
  have hkπ : π.ker = center Kg :=
    (MonoidHom.ker_comp_of_injective _ _ eq.injective).trans (QuotientGroup.ker_mk' _)
  let f := π.comp (inclusion hFK)
  have hker : IsPGroup 2 f.ker := by
    change IsPGroup 2 (π.ker.comap (inclusion hFK))
    rw [hkπ]
    exact hZ.comap_of_injective _ (inclusion_injective hFK)
  obtain ⟨⟨eF,_⟩,_⟩ := s.marking.cover_quotient hFL hw.2.2.2.2.2.2.2.1.subset
  have hFn : f.range ≤ normalizer (U : Set Janko4.Model) := by
    rintro _ ⟨a,rfl⟩
    apply (R.subgroupOf Kg).le_normalizer_map π
    apply mem_map_of_mem
    intro r
    exact hFR a.property (r : G)
  have hU : IsPGroup 2 U := (isPGroup_pCoreIn 2 J).comap_subtype.map π
  have hbound := Janko4.linearFive_normalized_twoGroup_card_le_1024 f hker eF U hU hFn
  have hEU : E ≤ U := map_mono (subgroupOf_mono Kg hVR)
  have hE : IsElementaryAbelian 2 E := by
    let := D.elementary
    let : IsElementaryAbelian 2 (V.subgroupOf Kg) :=
      IsElementaryAbelian.of_injective (subgroupOfEquivOfLe hVK).toMonoidHom
        (subgroupOfEquivOfLe hVK).injective
    exact IsElementaryAbelian.map π
  have hfix : V ⊓ centralizer (F : Set G) = ⊥ := by
    have hh := exterior_pushingUp_conjugate_cover_fixed_eq_bot s
      hw.2.2.2.2.2.2.2.1 1 (one_mem _)
    rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G from by ext; simp,
      Subgroup.map_id] at hh
    exact hh
  have hVin : Function.Injective (π.comp (inclusion hVK)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro v hv
    have hz : inclusion hVK v ∈ center Kg := hkπ ▸ hv
    have hvF : (v : G) ∈ centralizer (F : Set G) := by
      intro a ha
      exact congrArg Kg.subtype (mem_center_iff.mp hz (inclusion hFK ⟨a,ha⟩))
    apply Subtype.ext
    exact (show (v : G) ∈ (⊥ : Subgroup G) from hfix ▸ ⟨v.property,hvF⟩)
  have hEin : Function.Injective (π.comp (V.subgroupOf Kg).subtype) := by
    intro a b he
    have he' : (π.comp (inclusion hVK)) ((subgroupOfEquivOfLe hVK) a) =
        (π.comp (inclusion hVK)) ((subgroupOfEquivOfLe hVK) b) := he
    exact (subgroupOfEquivOfLe hVK).injective (hVin he')
  have hcard : Nat.card E = 1024 := by
    have he : (π.comp (V.subgroupOf Kg).subtype).range = E := by
      rw [MonoidHom.range_comp,range_subtype]
    rw [←he,←Nat.card_congr (MonoidHom.ofInjective hEin).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hVK).toEquiv,s.marking.card_module]
  have heq : E = U := eq_of_le_of_card_ge hEU (by rw [hcard]; exact hbound)
  change U = E ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 1024
  exact ⟨heq.symm,heq ▸ hE,heq ▸ hcard⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Subgroup Theory.GroupTheory
open Chapter4 Chapter4.Section04 Chapter12.Section02
open Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The source core is the direct product of the original exterior module
with its component centralizer. The central kernel of the full cover is
absorbed by the latter factor, not discarded. -/
theorem exterior_pushingUp_radical_module_split
    (s : SylowExteriorMarking D) {A J H W : Subgroup G}
    (hw : Witness L V A J H W) (K : Subgroup H) (hK : IsComponent H K)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    let R := J.pCoreIn 2
    let C := R ⊓ centralizer (K.map H.subtype : Set G)
    R = V ⊔ C ∧ V ⊓ C = ⊥ ∧ C ≠ ⊥ ∧ V ≤ centralizer (C : Set G) := by
  let R := J.pCoreIn 2
  let Kg := K.map H.subtype
  let C := R ⊓ centralizer (Kg : Set G)
  let q := (centerQuotientCongr
      (K.equivMapOfInjective H.subtype H.subtype_injective).symm).trans e
  let π := q.toMonoidHom.comp (QuotientGroup.mk' (center Kg))
  obtain ⟨heq,_,_⟩ := exterior_pushingUp_radical_quotient_eq s hw K hK e
  change (R.subgroupOf Kg).map π = (V.subgroupOf Kg).map π at heq
  obtain ⟨hs,hd,hne⟩ := exterior_pushingUp_radical_split s hw K hK e
  have hVR : V ≤ R := hw.2.2.2.2.2.1
  have hc := hw.2.2.2.2.2.2.1
  have hFH : (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype ≤ H :=
    (map_subtype_le _).trans inf_le_right
  have hFK : (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype ≤ Kg := by
    have hh := map_mono (f := H.subtype) (hc.ordinary_component_contains_original K hK)
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  have hVK : V ≤ Kg := hw.2.2.2.2.2.2.2.2.2.2.1.trans hFK
  have hKC : R ⊓ Kg ≤ V ⊔ C := by
    intro x hx
    have hm : π (⟨x,hx.2⟩ : Kg) ∈ (V.subgroupOf Kg).map π :=
      heq ▸ mem_map_of_mem π hx.1
    obtain ⟨v,hv,hev⟩ := hm
    have hz : (⟨x,hx.2⟩ : Kg) * v⁻¹ ∈ center Kg := by
      apply (QuotientGroup.eq_one_iff _).mp
      apply q.injective
      change π ((⟨x,hx.2⟩ : Kg)*v⁻¹) = q 1
      rw [map_mul,map_inv,hev,map_one,mul_inv_cancel]
    have hzC : x * (v : G)⁻¹ ∈ C := by
      refine ⟨R.mul_mem hx.1 (R.inv_mem (hVR hv)),?_⟩
      intro k hk
      exact congrArg Kg.subtype (mem_center_iff.mp hz ⟨k,hk⟩)
    have hh := (V ⊔ C).mul_mem (mem_sup_right hzC) (mem_sup_left hv)
    change x * (v : G)⁻¹ * (v : G) ∈ V ⊔ C at hh
    simpa only [inv_mul_cancel_right] using hh
  have hRC : R = V ⊔ C := le_antisymm
    (hs.le.trans (sup_le hKC le_sup_right)) (sup_le hVR inf_le_left)
  exact ⟨hRC,hd,hne,le_centralizer_iff.mp
    (inf_le_right.trans (centralizer_le hVK))⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
