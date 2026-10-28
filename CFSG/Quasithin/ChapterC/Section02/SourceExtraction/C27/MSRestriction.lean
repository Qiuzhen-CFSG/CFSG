module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.MSInputs
public import Theory.GroupTheory.PCoreSubnormalSupplement
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The full MS2(a) condition on the original component-radical product

An odd-index two-core witness in H restricts to KR because K is subnormal
in H and R normalizes K. The restricted witness has exactly the same
embedded two-core, and remains proper by characteristic-normalizer control.
All subgroup equivalences use the actual inclusions into H.

The generalized Fitting condition also passes to KR, since adjoining a
normalizing two-subgroup preserves a self-centralizing two-core. Together
with the existing MS3 theorem these discharge the non-model hypotheses
of C.1.31 on the literal product used in C.2.7.

Source: Aschbacher--Smith C.1.31 and C.2.7, pp.135 and 146--147.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem ms_map {A B : Type*} [Group A] [Group B] {R : Subgroup A}
    (h : MSOddIndexRadical R) (e : A ≃* B) : MSOddIndexRadical (R.map e.toMonoidHom) := by
  obtain ⟨P,hp,ho,he⟩ := h
  refine ⟨P.map e.toMonoidHom,?_,?_,?_⟩
  · apply lt_top_iff_ne_top.mpr
    intro ht
    apply hp.ne
    apply map_injective (f := e.toMonoidHom) e.injective
    rwa [map_top_of_surjective _ e.surjective]
  · rwa [index_map_of_bijective e.bijective]
  · change (P.map e.toMonoidHom).pCoreIn 2 = R.map e.toMonoidHom
    change P.pCoreIn 2 = R at he
    rw [←map_pCoreIn_of_injective 2 _ _ e.injective,he]

private theorem ms_join {K R M : Subgroup G} (hK : K.IsSubnormal)
    (hn : R ≤ normalizer K) (hR : MSOddIndexRadical R)
    (hc : normalizer (R : Set G) ≤ M) (hout : ¬ K ≤ M) :
    MSOddIndexRadical (R.subgroupOf (K ⊔ R)) := by
  obtain ⟨P,hP,hodd,hRP⟩ := hR
  change P.pCoreIn 2 = R at hRP
  have hcore := pCoreIn_subnormal_core_supplement K P hK (hRP ▸ hn)
  have hindex := odd_index_subnormal_core_supplement K P hK (hRP ▸ hn) hodd
  rw [hRP] at hcore hindex
  have hPN : P ≤ normalizer (R : Set G) := by
    rw [←hRP]
    exact P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  refine ⟨P.subgroupOf (K ⊔ R),?_,hindex,hcore⟩
  apply lt_top_iff_ne_top.mpr
  intro ht
  exact hout (le_sup_left.trans ((subgroupOf_eq_top.mp ht).trans (hPN.trans hc)))

variable {κ : GroupClass} {H K R M : Subgroup G}
theorem msOddIndexRadical_join_from_source (h : Input κ H R M K)
    (hr : MSOddIndexRadical (R.subgroupOf H)) :
    MSOddIndexRadical (R.subgroupOf (K ⊔ R)) := by
  let K0 := K.subgroupOf H
  let R0 := R.subgroupOf H
  let J0 := K0 ⊔ R0
  let J := K ⊔ R
  have hnorm : R0 ≤ normalizer (K0 : Set H) := by
    intro r hr
    apply mem_normalizer_iff.mpr
    intro k
    exact mem_normalizer_iff.mp (h.normalizes hr) (k : G)
  have hcontrol : normalizer (R0 : Set H) ≤ M.subgroupOf H :=
    (normalizer_le_characteristicNormalizerClosure_self R0 h.setup.radical.1).trans
      h.setup.characteristic_control
  have hout : ¬ K0 ≤ M.subgroupOf H := by
    intro hh
    apply h.outside
    intro k hk
    exact hh (show (⟨k,h.component.1 hk⟩ : H) ∈ K0 from hk)
  have hi := ms_join h.component.2.subnormal hnorm hr hcontrol hout
  have hmap : J0.map H.subtype = J := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le h.component.1,
      map_subgroupOf_eq_of_le h.setup.radical_le]
  let e : J0 ≃* J := (J0.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hmap)
  have hRmap : (R0.subgroupOf J0).map e.toMonoidHom = R.subgroupOf J := by
    ext r
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact hs
    · intro hr
      refine ⟨⟨⟨r,h.join_le r.property⟩,mem_sup_right hr⟩,hr,?_⟩
      rfl
  exact hRmap ▸ ms_map hi e

/-- Adjoining the original normalizing radical retains characteristic two. -/
theorem source_join_fitting (h : Input κ H R M K) :
    generalizedFitting (K ⊔ R : Subgroup G) = pCore 2 (K ⊔ R : Subgroup G) := by
  have hp : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply centralizer_pCore_sup_le 2 K R _ hp h.normalizes
  rw [←h.fitting]
  exact centralizer_generalizedFitting_le K

end CFSG.Quasithin.ChapterC.C27Source
