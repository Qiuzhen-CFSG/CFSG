module
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MiddleRecognition

/-!
# Automorphisms preserving a binary five-space parabolic

An automorphism preserving a specified maximal flag stabilizer is inner.
Inverse transpose would exchange its invariant subspace dimension with
its complement, impossible in odd dimension five. The proof reconstructs
the subspace from its stabilizer, so it retains the actual embedding.

Source application: Aschbacher--Smith, 12.5.3 and 12.5.11(2), printed
pp.818 and 821. The original point-parabolic supplies this invariant
subgroup in the strict linear enlargement branch.
-/

public section
open Subgroup Module
namespace BinaryLinear.FiveFlagGeometry
open OuterCyclic InvariantNodeActions

/-- Every automorphism preserving a specified maximal parabolic in GL₅(2) is inner. -/
theorem singleton_flag_preserving_is_inner (b : FiveBasis) (i : Fin 4)
    (a : MulAut (LinearGroup 5))
    (ha : (flagStabilizer b {i}).map a.toMonoidHom = flagStabilizer b {i}) :
    a ∈ MulAut.innerSubgroup (LinearGroup 5) := by
  obtain ⟨g,rfl | rfl⟩ := inner_graph (Or.inr rfl) a
  · exact ⟨g,rfl⟩
  · rw [flagStabilizer_singleton,graph_inner_map_parabolic] at ha
    let W := flagOrthogonal ((cutSpace b i).map g.toLinearMap)
    have hd : Module.finrank (ZMod 2) W = 4 - i.val := graph_inner_cut_finrank b g i
    have h0 : W ≠ ⊥ := by
      intro he
      rw [he,finrank_bot] at hd
      have := i.isLt
      omega
    have h1 : W ≠ ⊤ := by
      intro he
      rw [he,finrank_top,Module.finrank_fin_fun] at hd
      omega
    have hle : cutStabilizer b {i} ≤ parabolic W := by
      change flagStabilizer b {i} ≤ parabolic W
      rw [flagStabilizer_singleton]
      exact ha.symm.le
    obtain ⟨j,hj,he⟩ := (cutStabilizer_le_parabolic_iff b {i} W h0 h1).mp hle
    have hji : j = i := hj
    rw [hji] at he
    have hh := congrArg (fun U : Submodule (ZMod 2) (Space 5) => Module.finrank (ZMod 2) U) he
    rw [hd,cutSpace_finrank] at hh
    have := i.isLt
    omega
end BinaryLinear.FiveFlagGeometry
