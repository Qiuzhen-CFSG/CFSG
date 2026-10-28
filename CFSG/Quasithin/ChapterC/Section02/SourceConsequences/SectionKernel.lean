module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Restriction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Theory.GroupTheory.Commutator.SimpleSubnormal
import Mathlib.Tactic
/-!
# The section centralizer in the C.2.12 normalizer argument

C.2.8 restricts to N_H(M0). The section centralizer is normal there, so
its odd core is trivial. An ordinary component of the section centralizer
lifts to that normalizer and centralizes O2(N_H(M0)). Its first commutator
with M0 lies in this core; perfection removes the second commutator.
It would then centralize the source module and lie in M, contradicting
C.2.10(2). Thus the section centralizer has characteristic two, precisely
the prerequisite for applying the actual local C(G,T) theorem in C.2.12.

Source: Aschbacher–Smith, proof of C.2.12, printed p.148.
-/
public section
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Subgroup Theory.GroupTheory ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H M L R V : Subgroup G}

/-- The original C.2.8 hypothesis holds inside the actual normalizer of M0. -/
theorem normalizer_restriction (h : HypothesisC28 κ H M L R V) :
    HypothesisC28 κ (H ⊓ normalizer (conjugateSpanBy L M : Set G)) M L R V :=
  h.restrict (le_inf h.local_le (le_normalizer_conjugateSpanBy L M)) inf_le_left

omit [Finite G] in
private theorem section_normal (_h : HypothesisC28 κ H M L R V) :
    ((twoSectionCentralizer (conjugateSpanBy L M) H).subgroupOf
      (H ⊓ normalizer (conjugateSpanBy L M : Set G))).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer
    (le_inf (twoSectionCentralizer_le _ _) (twoSectionCentralizer_le_normalizer _ _))).mpr
  exact normalizer_twoSectionCentralizer _ _

/-- The section centralizer has no odd core; its normalizer has the inherited
source configuration, and the section centralizer is normal there. -/
theorem section_oddCore_eq_bot (h : HypothesisC28 κ H M L R V) :
    pPrimeCore 2 (twoSectionCentralizer (conjugateSpanBy L M) H) = ⊥ := by
  let X := twoSectionCentralizer (conjugateSpanBy L M) H
  let N := H ⊓ normalizer (conjugateSpanBy L M : Set G)
  have hXN : X ≤ N := le_inf (twoSectionCentralizer_le _ _) (twoSectionCentralizer_le_normalizer _ _)
  have ho := Subgroup.IsSubnormal.pPrimeCore_eq_bot h.normalizer_restriction.oddCore_eq_bot
    (X.subgroupOf N) h.section_normal.isSubnormal
  have he := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hXN)
  rw [ho,Subgroup.map_bot] at he
  exact he.symm

omit [Finite G] in
private theorem component_of_inclusion {A N : Subgroup G} (hAN : A ≤ N)
    (hn : (A.subgroupOf N).Normal) (K : Subgroup A) (hK : IsComponent A K) :
    IsComponent N (K.map (inclusion hAN)) := by
  let e := (subgroupOfEquivOfLe hAN).symm
  have hs := (hK.1.map (f := e.toMonoidHom) e.surjective).trans' hn.isSubnormal
  have he : (A.subgroupOf N).subtype.comp e.toMonoidHom = inclusion hAN := by
    ext x
    rfl
  rw [map_map,he] at hs
  let := hK.2
  exact ⟨hs,IsQuasisimple.of_mulEquiv
    (equivMapOfInjective K (inclusion hAN) (inclusion_injective hAN))⟩

private theorem no_component_inside_section (h : HypothesisC28 κ H M L R V)
    (J : Subgroup (H ⊓ normalizer (conjugateSpanBy L M : Set G) : Subgroup G))
    (hJ : IsComponent (H ⊓ normalizer (conjugateSpanBy L M : Set G) : Subgroup G) J)
    (hJX : J ≤ (twoSectionCentralizer (conjugateSpanBy L M) H).subgroupOf
      (H ⊓ normalizer (conjugateSpanBy L M : Set G))) : False := by
  let A := conjugateSpanBy L M
  let N := H ⊓ normalizer (A : Set G)
  have hAH : A ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  have hAN : A ≤ N := le_inf hAH A.le_normalizer
  have hVN : V ≤ N := h.module_le.trans hAN
  let A' := A.subgroupOf N
  let : A'.Normal := (normal_subgroupOf_iff_le_normalizer hAN).mpr inf_le_right
  let := hJ.2
  have hJC : ⁅J,pCore 2 N⁆ = ⊥ := by
    rcases hJ.normal_dichotomy (pCore 2 N) with hj | hc
    · let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
      let : Nontrivial J := (QuotientGroup.mk'_surjective (center J)).nontrivial
      exact (Group.IsPerfect.not_isNilpotent J (pCore_isPGroup.to_le hj).isNilpotent).elim
    · exact hc
  have hAQ : A'.pCoreIn 2 ≤ pCore 2 N :=
    le_sSup ⟨inferInstanceAs ((pCore 2 A').map A'.subtype).Normal,isPGroup_pCoreIn 2 A'⟩
  have hAJ : ⁅A',J⁆ ≤ A'.pCoreIn 2 := by
    apply (map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_commutator,map_pCoreIn_of_injective 2 A' N.subtype N.subtype_injective,
      map_subgroupOf_eq_of_le hAN]
    have hj : J.map N.subtype ≤ twoSectionCentralizer A H := by
      rintro x ⟨j,hj,rfl⟩
      exact hJX hj
    exact ((le_twoSectionCentralizer_iff A H _).mp hj).2.2
  have hz : ⁅A',J⁆ = ⊥ := by
    apply commutator_eq_bot_of_iterated_eq_bot
    exact le_bot_iff.mp ((commutator_mono (hAJ.trans hAQ) le_rfl).trans_eq
      ((commutator_comm _ _).trans hJC))
  have hJV : J ≤ centralizer (V.subgroupOf N : Set N) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    exact (commutator_mono le_rfl (show V.subgroupOf N ≤ A' from fun x hx => h.module_le hx)).trans_eq
      ((commutator_comm _ _).trans hz)
  have hN : normalizer (V.subgroupOf N : Set N) ≤ M.subgroupOf N := by
    rw [← subgroupOf_normalizer_eq hVN]
    intro x hx
    exact h.module_normalizer ⟨x.property.1,hx⟩
  exact h.normalizer_restriction.component_not_le J hJ
    ((hJV.trans (Subgroup.centralizer_le_normalizer _)).trans hN)

/-- Every ordinary component is excluded from the actual section centralizer. -/
theorem section_no_component (h : HypothesisC28 κ H M L R V)
    (K : Subgroup (twoSectionCentralizer (conjugateSpanBy L M) H)) :
    ¬ IsComponent (twoSectionCentralizer (conjugateSpanBy L M) H) K := by
  intro hk
  have hXN := le_inf (twoSectionCentralizer_le (conjugateSpanBy L M) H)
    (twoSectionCentralizer_le_normalizer (conjugateSpanBy L M) H)
  have hj := component_of_inclusion hXN h.section_normal K hk
  apply no_component_inside_section h _ hj
  rintro x ⟨k,hk,rfl⟩
  exact k.property

/-- The characteristic-two section-centralizer reduction in C.2.12, with
both its odd core and all ordinary components eliminated from source data. -/
theorem section_fitting_eq_core (h : HypothesisC28 κ H M L R V) :
    generalizedFitting (twoSectionCentralizer (conjugateSpanBy L M) H) =
      pCore 2 (twoSectionCentralizer (conjugateSpanBy L M) H) := by
  have he : componentLayer (twoSectionCentralizer (conjugateSpanBy L M) H) = ⊥ := by
    apply sSup_eq_bot.mpr
    intro K hK
    exact (h.section_no_component K hK).elim
  rw [generalizedFitting,he,sup_bot_eq,Fitting_eq_pcore _ 2 h.section_oddCore_eq_bot]
end CFSG.Quasithin.ChapterC.HypothesisC28
