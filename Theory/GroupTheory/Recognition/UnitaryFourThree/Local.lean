module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.Core
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# Intrinsic local structure from the U₄(3) centralizer hypothesis

The original residual and core have orders 288 and 32. The core center is
 the specified involution line; its normalizer is the original involution
 centralizer, and its whole ambient centralizer is just that line. The latter
 uses self-centralization of the actual generalized Fitting subgroup.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 45.2, printed p.242.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace CentralizerHypothesis
variable (h : CentralizerHypothesis z)

noncomputable def coreData : QuaternionCentralProductData (core z) :=
  h.factorData.coreData h.involution

include h in
theorem core_card : Nat.card (core z) = 32 := h.factorData.core_card h.involution
include h in
theorem residual_card : Nat.card (residual z) = 288 := h.factorData.residual_card h.involution
include h in
theorem core_center : (center (core z)).map (core z).subtype = zpowers z :=
  h.factorData.core_center h.involution
include h in
theorem core_extraspecial : IsExtraspecial 2 (core z) := h.coreData.extraspecial
include h in
theorem line_le_core : zpowers z ≤ core z := by
  rw [← h.core_center]
  exact map_subtype_le _

omit [Finite G] in
theorem centralizer_normalizes_residual : centralizer z ≤ normalizer (residual z : Set G) :=
  (centralizer z).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (centralizer z) (pResidual 2 (centralizer z)))

omit [Finite G] in
theorem centralizer_normalizes_core : centralizer z ≤ normalizer (core z : Set G) :=
  centralizer_normalizes_residual.trans
    (normalizer_le_normalizer_characteristic_image (residual z) (pCore 2 (residual z)))

include h in
theorem normalizer_core : normalizer (core z : Set G) = centralizer z := by
  apply le_antisymm ?_ centralizer_normalizes_core
  exact normalizer_le_centralizer_of_characteristic_involution (core z) (center (core z))
    z h.involution h.core_center

include h in
theorem centralizer_core : Subgroup.centralizer (core z : Set G) = zpowers z := by
  have hQH : core z ≤ centralizer z := (pCoreIn_le 2 (residual z)).trans (map_subtype_le _)
  apply le_antisymm
  · intro x hx
    have hxH : x ∈ centralizer z := mem_centralizer_singleton_iff.mpr
      (hx z (h.line_le_core (mem_zpowers z))).symm
    have hxF : (⟨x,hxH⟩ : centralizer z) ∈ generalizedFitting (centralizer z) := by
      apply Theory.GroupTheory.centralizer_generalizedFitting_le (centralizer z)
      intro y hy
      apply Subtype.ext
      exact hx y (h.generalizedFitting_eq ▸ mem_map_of_mem (centralizer z).subtype hy)
    have hxQ : x ∈ core z := h.generalizedFitting_eq ▸
      mem_map_of_mem (centralizer z).subtype hxF
    rw [← h.core_center]
    exact ⟨⟨x,hxQ⟩,mem_center_iff.mpr (fun y => Subtype.ext (hx y y.property)),rfl⟩
  · intro x hx y hy
    have hxZ : x ∈ (center (core z)).map (core z).subtype := h.core_center ▸ hx
    obtain ⟨xc,hxc,rfl⟩ := hxZ
    exact congrArg Subtype.val (mem_center_iff.mp hxc ⟨y,hy⟩)

end CentralizerHypothesis
end Theory.GroupTheory.Recognition.UnitaryFourThree
