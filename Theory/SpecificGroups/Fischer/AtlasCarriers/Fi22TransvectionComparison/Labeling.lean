module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.RootWords
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.Coordinates
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable

/-!
# Explicit labeling for the Fi22 transvection comparison

`Labeling.labelingEquiv` is an unconditional, checked bijection from the fixed
points of the actual ATLAS involution to the identity-form isotropic projective
points plus a singleton. The distinguished label 1982 maps to the singleton,
and its root acts as the identity.

`Labeling.coordinate_actions` certifies the complete coordinate action table
for the shared conjugate words. `toPoint_transvection` turns those scalar
identities into the specified matrix action, giving `labelingEquiv_action` and
`exists_labeling`. Only the centralizing witness remains explicit; the separate
centralizer-generation branch supplies it to the image-comparison assembly.

Source: ATLAS F22G1-p3510B0 and GLS3 Table 5.3t,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi22.TransvectionComparison
open Theory.SpecificGroups

/-- The actual distinguished fixed point of the shared conjugate table. -/
def labelingBase : FixedPointsA := ⟨rootBase, by
  change generatorA rootBase = rootBase
  rw [KernelCertificate.generatorA_apply_eq_fastA]
  decide +kernel⟩

theorem labelingEquiv_base : Labeling.labelingEquiv labelingBase = none := by
  change Labeling.toPoint (Labeling.toNormal labelingBase) = none
  apply Labeling.toPoint_zero
  change Labeling.representative rootBase = 0
  decide +kernel

/-- The distinguished ambient label is exactly the additional singleton. -/
theorem labelingEquiv_eq_none_iff (i : FixedPointsA) :
    Labeling.labelingEquiv i = none ↔ i = labelingBase := by
  rw [← labelingEquiv_base]
  exact Labeling.labelingEquiv.injective.eq_iff

theorem fixedPointRoot_labelingBase
    (hc : ∀ i : FixedPointsA, conjugateAt i.val ∈ centralizerA) :
    fixedPointRoot hc labelingBase = centralAtlasA :=
  Subtype.ext conjugateAt_base

/-- The entire distinguished root row has the required identity action. -/
theorem labelingEquiv_base_action
    (hc : ∀ i : FixedPointsA, conjugateAt i.val ∈ centralizerA) (j : FixedPointsA) :
    Labeling.labelingEquiv (fixedPointAction (fixedPointRoot hc labelingBase) j) =
      pointTransvection (Labeling.labelingEquiv labelingBase) (Labeling.labelingEquiv j) := by
  rw [fixedPointRoot_labelingBase, labelingEquiv_base, pointTransvection_none]
  have h : fixedPointAction centralAtlasA = 1 := centralAtlasA_mem_ker
  rw [h]
  rfl

/-- Assembly of the literal root action from its computable quadratic-field table.
The coordinate premise is supplied by `Labeling.coordinate_actions` below. -/
theorem labelingEquiv_action_of_coordinate_actions
    (ha : ∀ x y : Fin 3510, KernelCertificate.fastA x = x → KernelCertificate.fastA y = y →
      ∃ c : Labeling.Four, c ≠ 0 ∧
        c • Labeling.representative (Generation.rootAction x y) =
          Labeling.transvection (Labeling.representative x) (Labeling.representative y))
    (hc : ∀ i : FixedPointsA, conjugateAt i.val ∈ centralizerA) (i j : FixedPointsA) :
    Labeling.labelingEquiv (fixedPointAction (fixedPointRoot hc i) j) =
      pointTransvection (Labeling.labelingEquiv i) (Labeling.labelingEquiv j) := by
  have hi : KernelCertificate.fastA i.val = i.val := by
    rw [← KernelCertificate.generatorA_apply_eq_fastA]
    exact i.property
  have hj : KernelCertificate.fastA j.val = j.val := by
    rw [← KernelCertificate.generatorA_apply_eq_fastA]
    exact j.property
  obtain ⟨c, hcz, h⟩ := ha i.val j.val hi hj
  apply Labeling.toPoint_transvection (Labeling.toNormal i) (Labeling.toNormal j)
    (Labeling.toNormal (fixedPointAction (fixedPointRoot hc i) j)) c hcz
  change c • Labeling.representative (fixedPointAction (fixedPointRoot hc i) j).val = _
  rw [fixedPointAction_apply]
  change c • Labeling.representative (inclusion (conjugateAt i.val) j.val) = _
  rw [← Generation.rootAction_eq]
  exact h

/-- The existence statement from raw coordinate identities; the centralizing
witness remains explicit. -/
theorem exists_labeling_of_coordinate_actions
    (ha : ∀ x y : Fin 3510, KernelCertificate.fastA x = x → KernelCertificate.fastA y = y →
      ∃ c : Labeling.Four, c ≠ 0 ∧
        c • Labeling.representative (Generation.rootAction x y) =
          Labeling.transvection (Labeling.representative x) (Labeling.representative y)) :
    ∀ hc : ∀ i : FixedPointsA, conjugateAt i.val ∈ centralizerA,
      ∃ e : FixedPointsA ≃ U6Two.PointWithSingleton,
        ∀ i j, e (fixedPointAction (fixedPointRoot hc i) j) =
          pointTransvection (e i) (e j) := by
  intro hc
  exact ⟨Labeling.labelingEquiv, labelingEquiv_action_of_coordinate_actions ha hc⟩

/-- The explicit bijection intertwines every shared Fi22 root with its literal
unitary transvection, including the distinguished singleton in either argument. -/
theorem labelingEquiv_action
    (hc : ∀ i : FixedPointsA, conjugateAt i.val ∈ centralizerA) (i j : FixedPointsA) :
    Labeling.labelingEquiv (fixedPointAction (fixedPointRoot hc i) j) =
      pointTransvection (Labeling.labelingEquiv i) (Labeling.labelingEquiv j) :=
  labelingEquiv_action_of_coordinate_actions Labeling.coordinate_actions hc i j

/-- The complete labeling contract for the fixed ATLAS conjugate words. The
centralizing premise is supplied separately by the centralizer-generation branch. -/
theorem exists_labeling :
    ∀ hc : ∀ i : FixedPointsA, conjugateAt i.val ∈ centralizerA,
      ∃ e : FixedPointsA ≃ U6Two.PointWithSingleton,
        ∀ i j, e (fixedPointAction (fixedPointRoot hc i) j) =
          pointTransvection (e i) (e j) :=
  exists_labeling_of_coordinate_actions Labeling.coordinate_actions

end Sporadic.Fischer.Fi22.TransvectionComparison
