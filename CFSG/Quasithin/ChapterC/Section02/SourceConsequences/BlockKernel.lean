module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.SectionKernel
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ShortAction
import Mathlib.Tactic
/-!
# The characteristic-two section kernel in the original C.2.12 reduction

The actual C.2.8 data restricts to the normalizer of M0. Its section
centralizer has no odd core and no ordinary component. The C.1.29 source
then excludes any chi-block outside M; perfect-action transport supplies the
needed commutator vanishing without assuming a new block classifier.

Source: Aschbacher–Smith, C.2.10–12, printed pp.147–149.
-/
public section
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Subgroup Theory.GroupTheory ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H M L R V : Subgroup G}

/-- Every actual chi-block in the section centralizer centralizes M0. The
perfect actor fixes the at-most-two block family and then the short-group
core-quotient action; no block-normalization certificate is assumed. -/
theorem section_chi_commutator_eq_bot (h : HypothesisC28 κ H M L R V)
    (K : Subgroup (twoSectionCentralizer (conjugateSpanBy L M) H))
    (hK : IsChiBlockIn K) :
    ⁅K.map (twoSectionCentralizer (conjugateSpanBy L M) H).subtype,
      conjugateSpanBy L M⁆ = ⊥ := by
  let A := conjugateSpanBy L M
  let X := twoSectionCentralizer A H
  let N := H ⊓ normalizer (A : Set G)
  have hAN : A ≤ N := le_inf ((conjugateSpanBy_le_self h.component_le).trans h.local_le)
    A.le_normalizer
  have hXN : X ≤ N := le_inf (twoSectionCentralizer_le _ _) (twoSectionCentralizer_le_normalizer _ _)
  let A' := A.subgroupOf N
  let X' := X.subgroupOf N
  let : A'.Normal := (normal_subgroupOf_iff_le_normalizer hAN).mpr inf_le_right
  let : X'.Normal := (normal_subgroupOf_iff_le_normalizer hXN).mpr
    (normalizer_twoSectionCentralizer _ _)
  let := h.span_perfect
  let : Group.IsPerfect A' := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hAN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hAN).symm.surjective
  let e : X' ≃* X := subgroupOfEquivOfLe hXN
  let K' := K.map e.symm.toMonoidHom
  have hk' : IsChiBlockIn K' := RankOne.ChiProduct.chi_map_equiv e.symm hK
  have hf : generalizedFitting X' = pCore 2 X' := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,h.section_fitting_eq_core]
  let f : X' →* H := (inclusion (show N ≤ H from inf_le_left)).comp X'.subtype
  have hfi : Function.Injective f := (inclusion_injective inf_le_left).comp X'.subtype_injective
  have hr : primeRank 3 X' ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 f hfi).trans
      (h.sqtk.stronglyQuasithin 3 Nat.prime_three (by decide))
  let J := K'.map X'.subtype
  have hAJN : A' ≤ normalizer (J : Set N) :=
    SourceShortAction.perfect_normalizes_chi X' A' hf hr K' hk'
  have hJmap : J.map N.subtype = K.map X.subtype := by
    change ((K.map e.symm.toMonoidHom).map X'.subtype).map N.subtype = _
    rw [map_map,map_map]
    rfl
  have hAJ : ⁅A',J⁆ ≤ A'.pCoreIn 2 := by
    apply (map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_commutator,map_pCoreIn_of_injective 2 A' N.subtype N.subtype_injective,
      map_subgroupOf_eq_of_le hAN,hJmap]
    exact ((le_twoSectionCentralizer_iff A H _).mp (map_subtype_le K)).2.2
  have hAcore : (A'.pCoreIn 2).Normal := inferInstanceAs ((pCore 2 A').map A'.subtype).Normal
  let := hAcore
  have hi : A'.pCoreIn 2 ⊓ J ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 A').to_le inf_le_left) inf_le_right
    ((le_inf le_normalizer_of_normal J.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  have hJA : ⁅J,A'⁆ ≤ J.pCoreIn 2 := by
    apply le_trans (le_inf ?_ (le_normalizer_iff_commutator_le_left.mp hAJN)) hi
    rwa [commutator_comm]
  have hshort : IsShort J := RankOne.Solvable.isShort_of_equiv
    (equivMapOfInjective K' X'.subtype X'.subtype_injective) hk'.1.short
  have hz := SourceShortAction.perfect_centralizes_short_of_normalizes J A' hshort hAJN hJA
  have hm := congrArg (map N.subtype) hz
  rw [map_commutator,hJmap] at hm
  have hAmap : A'.map N.subtype = A := map_subgroupOf_eq_of_le hAN
  rw [hAmap] at hm
  simpa only [Subgroup.map_bot] using hm

/-- Consequently all such blocks already lie in M; the source module and
normalizer bound give the contradiction to a C.1.29 outside block. -/
theorem section_chi_le_local (h : HypothesisC28 κ H M L R V)
    (K : Subgroup (twoSectionCentralizer (conjugateSpanBy L M) H))
    (hK : IsChiBlockIn K) : K ≤ M.subgroupOf (twoSectionCentralizer (conjugateSpanBy L M) H) := by
  have hc : K.map (twoSectionCentralizer (conjugateSpanBy L M) H).subtype ≤
      centralizer (V : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp (h.section_chi_commutator_eq_bot K hK)).trans
      (centralizer_le h.module_le)
  intro k hk
  have him := mem_map_of_mem (twoSectionCentralizer (conjugateSpanBy L M) H).subtype hk
  exact h.module_normalizer ⟨k.property.1,(Subgroup.centralizer_le_normalizer _ (hc him))⟩
end CFSG.Quasithin.ChapterC.HypothesisC28
