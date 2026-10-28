module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Inner
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.Coordinate
public import Mathlib.GroupTheory.Index

/-!
# Outer involutions fixing nonsingular pairs

Inverse transpose fixes the pair consisting of a coordinate vector and its
coordinate covector. Inner transitivity on pairing-one pairs transports this
involution to every nonsingular pair. Its swapping action proves that it is
outside the actual inner subgroup. The inner/graph coverage then gives index
two for the inner subgroup of each full stabilizer.

Source: Aschbacher–Smith, H.9.1(4), printed pp.389–390, with the corrected
independent choice of the stabilizer Sylow described in the H.9 source audit.
-/

@[expose] public section

namespace BinaryNaturalDual.VectorStabilizers
open BinaryLinear.OuterCyclic

/-- The specified graph operator is genuinely outer. -/
theorem graphLinear_not_inner {n : ℕ} (hn : 0 < n) (d : CoordinateAction n) :
    graphLinear n ∉ MulAut.innerSubgroup (LinearGroup n) := by
  rintro ⟨g, hg⟩
  let x : BinaryLinear.OuterCyclic.Space n := fun _ => 1
  have he := congrArg (fun a : MulAut (LinearGroup n) =>
    (d.representation a (x, 0)).1) hg
  rw [d.on_inner, d.on_graph, naturalDualRepresentation_apply,
    coordinateSwap_apply, map_zero] at he
  have hx : x = 0 := g.injective (he.trans (map_zero g).symm)
  exact one_ne_zero (congrFun hx ⟨0, hn⟩)

/-- The inner subgroup of the actual automorphism group has index two. -/
theorem innerSubgroup_index {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n) :
    (MulAut.innerSubgroup (LinearGroup n)).index = 2 := by
  apply Subgroup.index_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨graphLinear n, graphLinear_not_inner (by omega) d, ?_⟩
  intro a
  obtain ⟨g, rfl | rfl⟩ := inner_graph hn a
  · exact Or.inr ⟨g, rfl⟩
  · left
    rw [← mul_assoc, ← pow_two, graphLinear_sq, one_mul]
    exact ⟨g, rfl⟩

/-- Every pairing-one vector has an outer involution in its actual full stabilizer.
No preassigned Sylow subgroup is involved. -/
theorem exists_outer_involution {n : ℕ} (hn : 0 < n) (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    ∃ s : MulAut (LinearGroup n), s ∈ fullStabilizer d (x,f) ∧
      s ∉ MulAut.innerSubgroup (LinearGroup n) ∧ s ^ 2 = 1 := by
  let e : BinaryLinear.OuterCyclic.Space n := Pi.single ⟨0, hn⟩ 1
  let q := dotProductEquiv (ZMod 2) (Fin n) e
  have he : q e = 1 := by
    change dotProduct e (Pi.single ⟨0, hn⟩ 1) = 1
    simp [dotProduct_single, e]
  obtain ⟨g, hg⟩ := ModelOrbits.exists_inner_eq_of_pairing_one d
    (show quadratic (x,f) = 1 from h) (show quadratic (e,q) = 1 from he)
  let c := MulAut.conj g
  let s := (MulAut.conj c⁻¹) (graphLinear n)
  have hs : s ∈ fullStabilizer d (x,f) := by
    change d.representation (c⁻¹ * graphLinear n * c) (x,f) = (x,f)
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg, d.on_graph]
    have hswap : coordinateSwap n (e,q) = (e,q) := by
      simp [coordinateSwap_apply, q]
    rw [hswap, ← hg]
    change (d.representation c⁻¹ * d.representation c) (x,f) = (x,f)
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  refine ⟨s, hs, ?_, ?_⟩
  · intro hsL
    have hc : c * s * c⁻¹ ∈ MulAut.innerSubgroup (LinearGroup n) :=
      Subgroup.Normal.conj_mem inferInstance s hsL c
    have heq : c * s * c⁻¹ = graphLinear n := by
      dsimp [s]
      group
    rw [heq] at hc
    exact graphLinear_not_inner hn d hc
  · change ((MulAut.conj c⁻¹) (graphLinear n)) ^ 2 = 1
    rw [← map_pow, graphLinear_sq, map_one]

/-- The inner stabilizer, as a subgroup of the full stabilizer. -/
def innerInFull {n : ℕ} (d : CoordinateAction n) (v : CoordinateSpace n) :
    Subgroup (fullStabilizer d v) := (innerStabilizer d v).subgroupOf (fullStabilizer d v)

@[simp] theorem mem_innerInFull {n : ℕ} (d : CoordinateAction n) (v : CoordinateSpace n)
    (a : fullStabilizer d v) :
    a ∈ innerInFull d v ↔ a.val ∈ MulAut.innerSubgroup (LinearGroup n) := by
  change (a.val ∈ MulAut.innerSubgroup _ ∧ a.val ∈ fullStabilizer d v) ↔ _
  exact and_iff_left a.property

/-- Restricting the inner subgroup does not change its carrier or embedding. -/
def innerInFullEquiv {n : ℕ} (d : CoordinateAction n) (v : CoordinateSpace n) :
    innerInFull d v ≃* innerStabilizer d v := Subgroup.subgroupOfEquivOfLe inf_le_right

instance innerInFull_normal {n : ℕ} (d : CoordinateAction n) (v : CoordinateSpace n) :
    (innerInFull d v).Normal where
  conj_mem a ha b := (mem_innerInFull d v _).mpr
    (Subgroup.Normal.conj_mem inferInstance a.val ((mem_innerInFull d v a).mp ha) b.val)

/-- Every nonsingular full stabilizer has precisely two inner cosets. -/
theorem innerInFull_index {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    (innerInFull d (x,f)).index = 2 := by
  obtain ⟨s, hs, hout, hsq⟩ := exists_outer_involution (by omega) d h
  apply Subgroup.index_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨⟨s, hs⟩, by simpa using hout, ?_⟩
  intro a
  by_cases ha : a.val ∈ MulAut.innerSubgroup (LinearGroup n)
  · exact Or.inr ((mem_innerInFull d (x,f) a).mpr ha)
  · left
    apply (mem_innerInFull d (x,f) _).mpr
    exact (Subgroup.mul_mem_iff_of_index_two (innerSubgroup_index hn d)).mpr
      (iff_of_false hout ha)

end BinaryNaturalDual.VectorStabilizers
