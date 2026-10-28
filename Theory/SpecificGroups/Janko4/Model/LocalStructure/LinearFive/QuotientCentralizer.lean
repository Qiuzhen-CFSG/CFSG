module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.AmbientBound
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Projection

/-!
# Localization of the full native centralizer in the octad pullback

The pointwise octad kernel is self-centralizing in M24: a nonidentity element
forces its centralizer into the octad stabilizer, whose two-core is already
self-centralizing. Since the image of the native F is the whole kernel, its
ambient centralizer lies in Q. All quotient maps are the literal max1 marking.
-/

public noncomputable section
namespace Janko4.LocalStructure.LinearFive
open Subgroup Cardinality
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

private theorem centralizer_A_le : centralizer (A : Set M24) ≤ A := by
  have hnot : A ≠ ⊥ := by
    intro h
    have hc := A_card
    rw [h, card_bot] at hc
    contradiction
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hnot
  have ha' : (a : M24) ≠ 1 := fun h => ha (Subtype.ext h)
  intro g hg
  have hgs : g ∈ octadStabilizer O :=
    octad_kernel_centralizer_le_stabilizer O a a.property ha'
      (mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hg) a a.property).symm)
  have hcore : (⟨g, hgs⟩ : octadStabilizer O) ∈ pCore 2 (octadStabilizer O) := by
    apply LinearFourCore.octad_core_selfCentralizing O
    intro u hu
    apply Subtype.ext
    have hua : (u : M24) ∈ A := by
      rw [A, ← octad_core_map_eq_pointwise]
      exact Subgroup.mem_map_of_mem _ hu
    exact (mem_centralizer_iff.mp hg) u hua
  rw [A, ← octad_core_map_eq_pointwise]
  exact Subgroup.mem_map_of_mem _ hcore

/-- Whole ambient centralizers, not only max1 centralizers, lie in the literal Q. -/
theorem centralizer_F_le_Q : centralizer (F : Set Model) ≤ Q := by
  intro z hz
  let x : M := ⟨z, centralizer_F_le_M hz⟩
  have hx : projection x ∈ centralizer (A : Set M24) := by
    intro a ha
    rw [← localF_image] at ha
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp ha
    have hfF : (f : Model) ∈ F := Subgroup.mem_map.mpr ⟨f, hf, rfl⟩
    have hc : f * x = x * f := Subtype.ext ((mem_centralizer_iff.mp hz) f hfF)
    exact (map_mul projection f x).symm.trans
      ((congrArg projection hc).trans (map_mul projection x f))
  exact Subgroup.mem_map.mpr ⟨x, centralizer_A_le hx, rfl⟩

end Janko4.LocalStructure.LinearFive
