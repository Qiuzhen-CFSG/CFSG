module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.ResidualNormalizers.KernelReduction
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.Coordinates

/-!
# The complementary actions of the endpoint single-node parabolics

The first node acts on the quotient by the two-space, and the last node
acts on the three-space. The kernels of these actions in the corresponding
maximal parabolics lie in the original single-node groups. If the action
images are two-groups, the intermediate-kernel lemma shows that the maximal
parabolics normalize the respective O² residuals.

The two-group image hypotheses remain explicit here. They are the remaining
coordinate calculations, rather than normalizer conclusions assumed as data.
Source: Aschbacher–Smith, 13.8.25, combined manuscript of 1 March 2004,
printed p.960 (PDF p.977). Nodes and cuts are indexed from zero.
-/

@[expose] public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.SylowOvergroups
namespace BinaryLinear.SmallParabolicLevi.ResidualNormalizers

private theorem flagSpace_mono (b : FiveBasis) {i j : Fin 4} (h : i ≤ j) :
    flagSpace b i ≤ flagSpace b j := by
  apply Submodule.span_mono
  exact Set.image_mono (fun _ hi => Nat.le_trans hi (show i.val ≤ j.val from h))

/-- The first single-node parabolic preserves the two-space. -/
theorem firstNode_le_cut (b : FiveBasis) :
    flagStabilizer b ({0} : Set (Fin 4))ᶜ ≤ parabolic (flagSpace b 1) := by
  rw [← flagStabilizer_singleton]
  exact flagStabilizer_antitone b (by simp)

/-- The last single-node parabolic preserves the three-space. -/
theorem lastNode_le_cut (b : FiveBasis) :
    flagStabilizer b ({3} : Set (Fin 4))ᶜ ≤ parabolic (flagSpace b 2) := by
  rw [← flagStabilizer_singleton]
  exact flagStabilizer_antitone b (by simp)

/-- The actual first-node action on the three-dimensional quotient. -/
noncomputable def firstTailAction (b : FiveBasis) :
    flagStabilizer b ({0} : Set (Fin 4))ᶜ →*
      BinaryLinear.GL (Space 5 ⧸ flagSpace b 1) :=
  (quotientAction (flagSpace b 1)).comp (inclusion (firstNode_le_cut b))

/-- The actual last-node action on the three-dimensional subspace. -/
noncomputable def lastHeadAction (b : FiveBasis) :
    flagStabilizer b ({3} : Set (Fin 4))ᶜ →* BinaryLinear.GL (flagSpace b 2) :=
  (subspaceAction (flagSpace b 2)).comp (inclusion (lastNode_le_cut b))

/-- Fixing the quotient preserves every cut above the two-space. -/
theorem quotientKernel_le_firstNode (b : FiveBasis) :
    (quotientAction (flagSpace b 1)).ker.map (parabolic (flagSpace b 1)).subtype ≤
      flagStabilizer b ({0} : Set (Fin 4))ᶜ := by
  rintro _ ⟨g, hg, rfl⟩
  have hq : quotientAction (flagSpace b 1) g = 1 := hg
  apply (mem_flagStabilizer_iff_maps b _ _).mpr
  intro i hi v hv
  have hi0 : i ≠ 0 := hi
  have hle : (1 : Fin 4) ≤ i := by
    have : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    change 1 ≤ i.val
    omega
  have hd : g.val v - v ∈ flagSpace b 1 := by
    exact (Submodule.Quotient.eq _).mp (LinearEquiv.congr_fun hq ((flagSpace b 1).mkQ v))
  have hm := (flagSpace b i).add_mem (flagSpace_mono b hle hd) hv
  simpa only [subtype_apply, sub_add_cancel] using hm

/-- Fixing the three-space preserves every cut below it. -/
theorem subspaceKernel_le_lastNode (b : FiveBasis) :
    (subspaceAction (flagSpace b 2)).ker.map (parabolic (flagSpace b 2)).subtype ≤
      flagStabilizer b ({3} : Set (Fin 4))ᶜ := by
  rintro _ ⟨g, hg, rfl⟩
  have hs : subspaceAction (flagSpace b 2) g = 1 := hg
  apply (mem_flagStabilizer_iff_maps b _ _).mpr
  intro i hi v hv
  have hi3 : i ≠ 3 := hi
  have hle : i ≤ (2 : Fin 4) := by
    have : i.val ≠ 3 := fun h => hi3 (Fin.ext h)
    change i.val ≤ 2
    have := i.isLt
    omega
  have he := congrArg Subtype.val
    (LinearEquiv.congr_fun hs ⟨v, flagSpace_mono b hle hv⟩)
  change g.val v = v at he
  simpa only [subtype_apply, he] using hv

/-- The first endpoint normalizer bound, conditional on its quotient image. -/
theorem first_normalizer_of_tail_range_isPGroup (b : FiveBasis)
    (h : IsPGroup 2 (firstTailAction b).range) :
    flagStabilizer b {1} ≤
      normalizer ((pResidual 2 (flagStabilizer b ({0} : Set (Fin 4))ᶜ)).map
        (flagStabilizer b ({0} : Set (Fin 4))ᶜ).subtype) := by
  let : Finite (LinearGroup 5) := Finite.of_injective
    (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective
  rw [flagStabilizer_singleton]
  exact le_normalizer_embedded_pResidual_of_kernel 2 _ _ (firstNode_le_cut b) _
    (quotientKernel_le_firstNode b) h

/-- The last endpoint normalizer bound, conditional on its subspace image. -/
theorem last_normalizer_of_head_range_isPGroup (b : FiveBasis)
    (h : IsPGroup 2 (lastHeadAction b).range) :
    flagStabilizer b {2} ≤
      normalizer ((pResidual 2 (flagStabilizer b ({3} : Set (Fin 4))ᶜ)).map
        (flagStabilizer b ({3} : Set (Fin 4))ᶜ).subtype) := by
  let : Finite (LinearGroup 5) := Finite.of_injective
    (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective
  rw [flagStabilizer_singleton]
  exact le_normalizer_embedded_pResidual_of_kernel 2 _ _ (lastNode_le_cut b) _
    (subspaceKernel_le_lastNode b) h
end BinaryLinear.SmallParabolicLevi.ResidualNormalizers

end
