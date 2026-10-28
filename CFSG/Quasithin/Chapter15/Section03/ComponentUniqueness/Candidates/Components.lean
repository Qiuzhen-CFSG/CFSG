module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.LocalSetup
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CComponent.Basic

/-!
# Ordinary components for the outside-overgroup argument

From `O(I) = 1` and `F*(I) ≠ O₂(I)` we obtain an ordinary quasisimple
component. Its odd core is trivial, its center equals its two-core, and
it cannot lie in a subgroup of characteristic two. Subnormality is retained
throughout; no component is assumed normal in the ambient group.

The source notation `C(I)` means minimal nontrivial perfect subnormal
subgroups, not ordinary components. We prove the implication from ordinary
components to C-components. The reverse implication is deliberately absent:
trivial odd core alone does not establish it.

These are the setup deductions preceding Aschbacher--Smith 15.3.33,
combined manuscript of 1 March 2004, printed p.1134. The C-component
convention is Definition A.3.1, printed p.41.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]

private theorem oddCore_map_le_of_subnormal {K : Subgroup G} (hK : K.IsSubnormal) :
    (pPrimeCore 2 K).map K.subtype ≤ pPrimeCore 2 G := by
  induction hK with
  | top =>
    exact (pPrimeCore_map_iso 2 (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)).le
  | step K H hKH hH hN ih =>
    let := hN
    have hn := pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 (K.subgroupOf H)
    have he : (pPrimeCore 2 K).map K.subtype =
        ((pPrimeCore 2 (K.subgroupOf H)).map (K.subgroupOf H).subtype).map H.subtype := by
      rw [← pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hKH), map_map, map_map]
      rfl
    rw [he]
    exact (map_mono hn).trans ih

/-- An ordinary component inherits the trivial odd core of the ambient group. -/
theorem component_oddCore_eq_bot {K : Subgroup G}
    (hK : IsComponent G K) (hodd : pPrimeCore 2 G = ⊥) : pPrimeCore 2 K = ⊥ := by
  apply ((pPrimeCore 2 K).map_eq_bot_iff_of_injective K.subtype_injective).mp
  exact le_bot_iff.mp ((oddCore_map_le_of_subnormal hK.1).trans hodd.le)

omit [Finite G] in
private theorem component_nontrivial {K : Subgroup G} (hK : IsComponent G K) :
    Nontrivial K := by
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  exact (QuotientGroup.mk'_surjective (center K)).nontrivial

/-- In an odd-core-free group the center of a component is exactly its two-core. -/
theorem component_center_eq_twoCore {K : Subgroup G}
    (hK : IsComponent G K) (hodd : pPrimeCore 2 G = ⊥) :
    center K = pCore 2 K := by
  let := hK.2
  let := component_nontrivial hK
  have ho := component_oddCore_eq_bot hK hodd
  apply le_antisymm
  · have hc : center K ≤ fittingSubgroup K := le_sSup ⟨inferInstance, inferInstance⟩
    exact hc.trans (Fitting_eq_pcore K 2 ho).le
  · rcases IsQuasisimple.normal_le_center_or_eq_top (pCore 2 K) with hc | ht
    · exact hc
    · have hp : IsPGroup 2 K := by
        have hp : IsPGroup 2 (⊤ : Subgroup K) := ht ▸ pCore_isPGroup
        exact hp.of_surjective (Subgroup.topEquiv : (⊤ : Subgroup K) ≃* K).toMonoidHom
          (Subgroup.topEquiv : (⊤ : Subgroup K) ≃* K).surjective
      let := hp.isNilpotent
      exact (Group.IsPerfect.not_isSolvable K inferInstance).elim

/-- An ordinary component cannot be contained in a characteristic-two subgroup. -/
theorem component_not_le_characteristicTwo {K H : Subgroup G}
    (hK : IsComponent G K) (hH : generalizedFitting H = pCore 2 H) : ¬ K ≤ H := by
  intro hKH
  have hc := hK.subgroupOf hKH
  let := hc.2
  let := component_nontrivial hc
  have hle : K.subgroupOf H ≤ pCore 2 H :=
    (component_le_generalizedFitting H (K.subgroupOf H) hc).trans hH.le
  have hp : IsPGroup 2 (K.subgroupOf H) := pCore_isPGroup.to_le hle
  let := hp.isNilpotent
  exact Group.IsPerfect.not_isSolvable (K.subgroupOf H) inferInstance

omit [Finite G] in
/-- Ordinary components satisfy the source definition of C-component. -/
theorem component_isCComponent {K : Subgroup G} (hK : IsComponent G K) :
    K.IsCComponent := by
  let := hK.2
  let := component_nontrivial hK
  refine ⟨(nontrivial_iff_ne_bot K).mp inferInstance, inferInstance, hK.1, ?_⟩
  intro J hJK hJne hJperfect hJsub
  let := hJperfect
  let e := subgroupOfEquivOfLe hJK
  let : Group.IsPerfect (J.subgroupOf K) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  rcases IsQuasisimple.subnormal_le_center_or_eq_top (J.subgroupOf K) hJsub.subgroupOf with hc | ht
  · have hb : ⁅J.subgroupOf K, J.subgroupOf K⁆ = ⊥ :=
      le_bot_iff.mp ((commutator_mono hc le_top).trans
        (commutator_center_left (⊤ : Subgroup K)).le)
    rw [commutator_eq_self] at hb
    have : J = ⊥ := by
      simpa [map_subgroupOf_eq_of_le hJK] using congrArg (Subgroup.map K.subtype) hb
    exact (hJne this).elim
  · exact subgroupOf_eq_top.mp ht

/-- The generalized-Fitting inequality produces an actual ordinary component. -/
theorem exists_ordinary_component_of_fstar_ne_twoCore
    (hodd : pPrimeCore 2 G = ⊥)
    (hF : generalizedFitting G ≠ pCore 2 G) :
    ∃ K : Subgroup G, IsComponent G K := by
  by_contra! hn
  apply hF
  have he : componentLayer G = ⊥ := by
    apply sSup_eq_bot.mpr
    intro K hK
    exact (hn K hK).elim
  rw [generalizedFitting, he, sup_bot_eq, Fitting_eq_pcore G 2 hodd]

/-- The odd-core conclusion of 15.3.33(3) holds for all C-components,
without treating them as ordinary components. -/
theorem cComponent_oddCore_eq_bot {K : Subgroup G}
    (hK : K.IsCComponent) (hodd : pPrimeCore 2 G = ⊥) :
    pPrimeCore 2 K = ⊥ := by
  apply ((pPrimeCore 2 K).map_eq_bot_iff_of_injective K.subtype_injective).mp
  exact le_bot_iff.mp ((oddCore_map_le_of_subnormal hK.subnormal).trans hodd.le)

/-- The component chosen immediately before 15.3.33, with its relative
subnormality, source C-component status, and noncontainment in `M`.
The intrinsic subgroup `M.subgroupOf I` is exactly `M ∩ I` viewed inside `I`. -/
theorem exists_component_for_outside
    {Yplus S M I : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M,
      generalizedFitting J ≠ pCore 2 J)
    (hodd : pPrimeCore 2 I = ⊥)
    (hMI : generalizedFitting (M.subgroupOf I) = pCore 2 (M.subgroupOf I)) :
    ∃ L : Subgroup I, IsComponent I L ∧ L.IsCComponent ∧
      center L = pCore 2 L ∧ pPrimeCore 2 L = ⊥ ∧
      ¬ L.map I.subtype ≤ M := by
  obtain ⟨L, hL⟩ := exists_ordinary_component_of_fstar_ne_twoCore hodd (h25 I hI)
  refine ⟨L, hL, component_isCComponent hL,
    component_center_eq_twoCore hL hodd, component_oddCore_eq_bot hL hodd, ?_⟩
  intro hLM
  exact component_not_le_characteristicTwo hL hMI (map_le_iff_le_comap.mp hLM)

end CFSG.Quasithin.Chapter15.Section03
