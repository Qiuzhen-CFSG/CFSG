module
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.Contracts
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.FixedGeometry.Gram
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.FixedGeometry.Standard
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Compatible fixed-group models for binary degree-five outer involutions

The inner/graph automorphism theorem and the trivial binary scalar center
force the twisting matrix of an outer involution to be symmetric. A Gram
factorization `g = hᵀ h` then gives an explicit conjugation intertwining that
involution with ordinary inverse transpose. Restriction of this conjugation
identifies the actual fixed subgroups. Automorphisms preserve the intrinsic
set of binary transvections, so this restriction transports every clause of
`FixedModel`, including its natural-action requirement.

The imported `symmetric_gram` normalizes every invertible symmetric binary
five-matrix. `Standard` constructs the compatible
fixed model for ordinary inverse transpose by splitting its canonical line
from the alternating four-space and extending the designated polar S₆ action.
`exists_fixedModel` combines these geometric results with the reduction,
including the actual transvection clause on the original five-space.

This is the outer-involution reduction in the degree-five calculation of
Aschbacher–Smith, E.6.23, printed p.254 (PDF p.265) of
`refs/quasithin.pdf`. The inverse-transpose convention and automorphism
coverage come from `BinaryLinear.OuterCyclic`. The symmetry argument follows
the analogous degree-three reduction in `PSL3Two.OuterInvolutionSinger`.
-/

public section

open scoped MatrixGroups
open BinaryLinear.OuterCyclic

namespace BinaryLinear.SixSylowActors.Five

private theorem graph_twist_square {G : Type*} [Group G]
    (γ : MulAut G) (hγ : ∀ x, γ (γ x) = x) (g : G) :
    MulAut.conj (γ g * g) = (γ * MulAut.conj g) ^ 2 := by
  ext x : 1
  simp only [pow_two, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hγ]

private theorem apply_apply_of_sq {G : Type*} [Group G]
    (γ : MulAut G) (hγ : γ ^ 2 = 1) (x : G) : γ (γ x) = x := by
  simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using
    congrArg (fun a : MulAut G => a x) hγ

private theorem cocycle_of_twist_sq {G : Type*} [Group G]
    (hc : Subgroup.center G = ⊥) (γ : MulAut G) (hγ : γ ^ 2 = 1)
    (g : G) (h : (γ * MulAut.conj g) ^ 2 = 1) : γ g = g⁻¹ := by
  have he := graph_twist_square γ (apply_apply_of_sq γ hγ) g
  apply mul_eq_one_iff_eq_inv.mp
  apply MulAut.conj_injective_of_center_eq_bot hc
  rw [he, h, map_one]

private theorem symmetric_of_graph_twist_sq_aux {n : ℕ} (hn : 0 < n)
    (g : SL(n, ZMod 2)) (h : (graphSL n * MulAut.conj g) ^ 2 = 1) :
    g.transpose = g := by
  have hi := cocycle_of_twist_sq (binary_center_eq_bot hn)
    (graphSL n) (graphSL_sq n) g h
  dsimp only [graphSL] at hi
  exact inv_injective hi

/-- An involutory inner twist of inverse transpose has a symmetric matrix. -/
theorem symmetric_of_graph_twist_sq (g : SL(5, ZMod 2))
    (h : (graphSL 5 * MulAut.conj g) ^ 2 = 1) : g.transpose = g :=
  symmetric_of_graph_twist_sq_aux (by decide) g h

/-- Every outer involution is a graph twist by an actual symmetric matrix. -/
theorem exists_symmetric_twist (τ : MulAut (LinearGroup 5)) (hτ : τ ^ 2 = 1)
    (hout : τ ∉ MulAut.innerSubgroup (LinearGroup 5)) :
    ∃ g : SL(5, ZMod 2), g.transpose = g ∧
      τ = graphLinear 5 * MulAut.conj (slEquivLinear 5 g) := by
  obtain ⟨g, hi | hg⟩ := inner_graph (Or.inr rfl) τ
  · exact (hout (hi ▸ ⟨g, rfl⟩)).elim
  obtain ⟨k, rfl⟩ := (slEquivLinear 5).surjective g
  refine ⟨k, symmetric_of_graph_twist_sq k ?_, hg⟩
  apply (MulAut.congr (slEquivLinear 5)).injective
  have he : MulAut.congr (slEquivLinear 5) (graphSL 5 * MulAut.conj k) = τ := by
    rw [hg]
    ext x : 1
    simp [graphLinear, MulAut.congr_apply]
  rw [map_pow, he, hτ, map_one]

private def fixedEquivOfIntertwines {G : Type*} [Group G]
    (α β a : MulAut G) (h : ∀ x, a (α x) = β (a x)) :
    α.fixedSubgroup ≃* β.fixedSubgroup where
  toFun x := ⟨a x, by
    rw [MulAut.mem_fixedSubgroup, ← h]
    exact congrArg a ((MulAut.mem_fixedSubgroup α x).mp x.property)⟩
  invFun y := ⟨a.symm y, by
    rw [MulAut.mem_fixedSubgroup]
    apply a.injective
    rw [h, a.apply_symm_apply, (MulAut.mem_fixedSubgroup β y).mp y.property]⟩
  left_inv x := Subtype.ext (a.symm_apply_apply x)
  right_inv x := Subtype.ext (a.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul a (x : G) (y : G))

/-- Transport preserves both the fixed subgroup and the transvection clause. -/
def FixedModel.ofIntertwines {α β : MulAut (LinearGroup 5)}
    (m : FixedModel β) (a : MulAut (LinearGroup 5))
    (h : ∀ x, a (α x) = β (a x)) : FixedModel α where
  equiv := (fixedEquivOfIntertwines α β a h).trans m.equiv
  swap_isTransvection σ hσ := by
    change IsTransvection (a.symm ((m.equiv.symm σ : β.fixedSubgroup) : LinearGroup 5))
    exact (isTransvection_map_linear (by decide : 2 ≤ 5) a.symm _).mpr
      (m.swap_isTransvection σ hσ)

/-- Gram factorization makes the inner twist conjugate to inverse transpose. -/
theorem gram_intertwines (g h : SL(5, ZMod 2)) (hg : g = h.transpose * h)
    (x : LinearGroup 5) :
    MulAut.conj (slEquivLinear 5 h)
        ((graphLinear 5 * MulAut.conj (slEquivLinear 5 g)) x) =
      graphLinear 5 (MulAut.conj (slEquivLinear 5 h) x) := by
  obtain ⟨y, rfl⟩ := (slEquivLinear 5).surjective x
  have ht : graphSL 5 h.transpose = h⁻¹ := by
    change (h.transpose.transpose)⁻¹ = h⁻¹
    congr 1
  have he : MulAut.conj h ((graphSL 5 * MulAut.conj g) y) =
      graphSL 5 (MulAut.conj h y) := by
    rw [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, hg]
    simp only [MulAut.conj_apply, map_mul, map_inv, ht]
    group
  have hm := congrArg (slEquivLinear 5) he
  simpa [MulAut.mul_apply, MulAut.conj_apply, graphLinear,
    MulAut.congr_apply, map_mul, map_inv] using hm

/-- This reduction retains two explicit geometric obligations: symmetric Gram
factorization and the compatible fixed model for ordinary inverse transpose. -/
theorem exists_fixedModel_of_gram
    (hgram : ∀ g : SL(5, ZMod 2), g.transpose = g →
      ∃ h : SL(5, ZMod 2), g = h.transpose * h)
    (hstandard : Nonempty (FixedModel (graphLinear 5)))
    (τ : MulAut (LinearGroup 5)) (hτ : τ ^ 2 = 1)
    (hout : τ ∉ MulAut.innerSubgroup (LinearGroup 5)) : Nonempty (FixedModel τ) := by
  obtain ⟨g, hs, rfl⟩ := exists_symmetric_twist τ hτ hout
  obtain ⟨h, hh⟩ := hgram g hs
  obtain ⟨m⟩ := hstandard
  exact ⟨m.ofIntertwines (MulAut.conj (slEquivLinear 5 h)) (gram_intertwines g h hh)⟩

/-- Every outer involution of the binary linear group in degree five has an
actual S₆ fixed-group model whose transpositions are natural transvections. -/
theorem exists_fixedModel (τ : MulAut (LinearGroup 5)) (hτ : τ ^ 2 = 1)
    (hout : τ ∉ MulAut.innerSubgroup (LinearGroup 5)) : Nonempty (FixedModel τ) :=
  exists_fixedModel_of_gram symmetric_gram graph_fixedModel τ hτ hout

end BinaryLinear.SixSylowActors.Five
