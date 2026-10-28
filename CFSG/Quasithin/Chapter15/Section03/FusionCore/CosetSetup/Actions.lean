module

public import CFSG.Quasithin.Chapter15.Section03.Constructions
public import Theory.GroupTheory.CentralizerModulo
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Relative quotients in the coset setup of Section 15.3

All quotients are formed inside the indicated overgroup. The centralizer of
`A/Z` means the inverse image of the centralizer of its actual image in `H/Z`.
In particular its normal core is taken in `H`, before taking the two-residual.
The spans `U_H = ⟨Z_S^H⟩` and `V_H = ⟨V^H⟩` use the common `localSpan`
construction with different first arguments.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.1141–1143.
These definitions do not assert F.9.1 or its normal-core bound.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- `C_H(A/Z)`, in the actual quotient `H/(Z ∩ H)`. Applications supply
`Z ≤ A ≤ H`; ambient normality of `Z` is not needed. -/
def quotientCentralizer (H A Z : Subgroup G) [(Z.subgroupOf H).Normal] : Subgroup H :=
  centralizerModulo ⊤ (A.subgroupOf H) (Z.subgroupOf H)

/-- Membership is exactly the commutator condition on elements of `A`. -/
theorem mem_quotientCentralizer_iff (H A Z : Subgroup G)
    [(Z.subgroupOf H).Normal] (hAH : A ≤ H) (x : H) :
    x ∈ quotientCentralizer H A Z ↔ ∀ a ∈ A, ⁅a, (x : G)⁆ ∈ Z := by
  simp only [quotientCentralizer, mem_centralizerModulo_iff, mem_top, true_and]
  constructor
  · intro h a ha
    exact h ⟨a, hAH ha⟩ ha
  · intro h a ha
    exact h a ha

/-- Normality of the acted-on subgroup makes its quotient centralizer normal
in the actor. This is used for `U_H`, but is not assumed for `Z_S`. -/
instance quotientCentralizer_normal (H A Z : Subgroup G)
    [(Z.subgroupOf H).Normal] [(A.subgroupOf H).Normal] :
    (quotientCentralizer H A Z).Normal := by
  unfold quotientCentralizer centralizerModulo
  infer_instance

/-- The normal core in clause (a) of F.9.1, before taking `O²`. -/
def centralizerCore (H ZS Z : Subgroup G) [(Z.subgroupOf H).Normal] : Subgroup H :=
  (quotientCentralizer H ZS Z).normalCore

instance centralizerCore_normal (H ZS Z : Subgroup G) [(Z.subgroupOf H).Normal] :
    (centralizerCore H ZS Z).Normal := inferInstanceAs
      ((quotientCentralizer H ZS Z).normalCore.Normal)

/-- The source `X = O²(core_H(C_H(Z_S/Z)))`, embedded back into `G`. -/
noncomputable def centralizerCoreResidual (H ZS Z : Subgroup G)
    [(Z.subgroupOf H).Normal] : Subgroup G :=
  (Stellmacher.twoResidualAmbient (centralizerCore H ZS Z)).map H.subtype

/-- The source `L₁` uses the centralizer of `Z`, not the centralizer of `V`. -/
noncomputable def localL1 (Y Z : Subgroup G) : Subgroup G :=
  Stellmacher.twoResidualAmbient (Y ⊓ centralizer (Z : Set G))

/-- Normality of the layer is relative to the centralizing overgroup. -/
theorem layer_normal (H Z : Subgroup G) (hHZ : H ≤ centralizer (Z : Set G)) :
    (Z.subgroupOf H).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  exact hHZ.trans (Subgroup.centralizer_le_normalizer _)

/-- Every local span is normalized by its actor, including when restricted
to that actor. -/
instance localSpan_subgroupOf_normal (A H : Subgroup G) :
    ((localSpan A H).subgroupOf H).Normal :=
  normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy A H)

instance localSpan_top_normal (A : Subgroup G) : (localSpan A ⊤).Normal :=
  normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_conjugateSpanBy A ⊤))

/-- A homomorphism transports the generators and their actor together. -/
theorem map_localSpan {K : Type*} [Group K] (f : G →* K) (A H : Subgroup G) :
    (localSpan A H).map f = localSpan (A.map f) (H.map f) := by
  unfold localSpan conjugateSpanBy
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨h, hh, a, ha, rfl⟩, rfl⟩
    exact ⟨f h, mem_map_of_mem f hh, f a, mem_map_of_mem f ha, by simp⟩
  · rintro ⟨_, ⟨h, hh, rfl⟩, _, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨h * a * h⁻¹, ⟨h, hh, a, ha, rfl⟩, by simp⟩

/-- Computing a span inside `H` and embedding it gives the original ambient
span. In particular this applies separately to `Z_S` and to `V`. -/
theorem map_localSpan_subgroupOf (A H : Subgroup G) (hAH : A ≤ H) :
    (localSpan (A.subgroupOf H) ⊤).map H.subtype = localSpan A H := by
  rw [map_localSpan, map_subgroupOf_eq_of_le hAH, ← MonoidHom.range_eq_map, range_subtype]

/-- The source `U_C = C_{U_H}(Q_H)`, as a subgroup of `G`. -/
def fixedCore (ZS H : Subgroup G) : Subgroup G :=
  localSpan ZS H ⊓ centralizer (H.pCoreIn 2 : Set G)

instance fixedCore_subgroupOf_normal (ZS H : Subgroup G) :
    ((fixedCore ZS H).subgroupOf H).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  apply le_trans _ inf_normalizer_le_normalizer_inf
  refine le_inf (le_normalizer_conjugateSpanBy ZS H) ?_
  exact (H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))).trans
      (normalizer_le_normalizer_centralizer _)

/-- `H*` in 15.3.48–49 is the actual two-core quotient. -/
abbrev CoreQuotient (H : Subgroup G) := H ⧸ pCore 2 H

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup

end
