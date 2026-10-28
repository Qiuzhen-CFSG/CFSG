module
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3.Geometry
public import Theory.SpecificGroups.Held.Model.FourPointBase

public import Mathlib.Algebra.Pointwise.Stabilizer

/-!
# Restriction and finite adjacency counts for the Held sextet

Restrict the actual graph-and-sextet stabilizer to its six vertices. Its kernel
fixes those vertices pointwise. A graph permutation fixing a list preserves each
adjacency-signature class and all neighbor counts into that class. Small explicit
classes will bound this kernel without recognizing the full graph group.

Source: the unchanged ATLAS HeG1-p2058B0 relation; GLS3 Table 5.3p.
-/

public section
open scoped Pointwise
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
open Held.NormalizerGraph Held.NormalizerGraph.CardBound

@[expose] def graphSextetGroup : Subgroup (Equiv.Perm (Fin 2058)) :=
  preservingGroup ⊓ sextetPermutationStabilizer

@[expose] def sextetRestriction : graphSextetGroup →* Equiv.Perm ↥sextet where
  toFun g := g.val.subtypePerm (MulAction.mem_stabilizer_set.mp g.property.2)
  map_one' := by ext x; rfl
  map_mul' g h := by ext x; rfl

theorem fixes_sextet (g : sextetRestriction.ker) (x : Fin 2058) (hx : x ∈ sextet) :
    g.val.val x = x := by
  have he := congrArg (fun p : Equiv.Perm ↥sextet => (p ⟨x, hx⟩).val) g.property
  exact he

@[expose] def neighborCount (s : Finset (Fin 2058)) (x : Fin 2058) : ℕ :=
  (s.filter (Adj x)).card

theorem sample_invariant (bs : List (Fin 2058)) (s : Finset (Fin 2058)) (v : ℕ)
    (hc : ∀ x, x ∈ s ↔ baseSignature bs x = v)
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ preservingGroup)
    (hf : ∀ b ∈ bs, σ b = b) : s.image σ = s := by
  ext x
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (hc _).mpr ((baseSignature_invariant bs σ hσ hf y).trans ((hc y).mp hy))
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨σ.symm x, ?_, σ.apply_symm_apply x⟩
    apply (hc _).mpr
    have he := baseSignature_invariant bs σ hσ hf (σ.symm x)
    rw [σ.apply_symm_apply] at he
    exact he.symm.trans ((hc x).mp hx)

theorem neighborCount_invariant (s : Finset (Fin 2058))
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ preservingGroup)
    (hs : s.image σ = s) (x : Fin 2058) :
    neighborCount s (σ x) = neighborCount s x := by
  unfold neighborCount
  calc
    (s.filter (Adj (σ x))).card = ((s.image σ).filter (Adj (σ x))).card := by rw [hs]
    _ = ((s.filter (Adj x)).image σ).card := by
      rw [Finset.filter_image]
      congr 2
      exact Finset.filter_congr (fun y _ => hσ x y)
    _ = (s.filter (Adj x)).card := Finset.card_image_of_injective _ σ.injective

namespace SextetGraphBound

/-- The ordered list used for adjacency signatures of the fixed sextet. -/
@[expose] def sextetBase : List (Fin 2058) := [480, 557, 719, 892, 1016, 1444]

theorem mem_sextetBase (x : Fin 2058) : x ∈ sextetBase ↔ x ∈ sextet := by
  simp [sextetBase, sextet]

end SextetGraphBound
end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max3
