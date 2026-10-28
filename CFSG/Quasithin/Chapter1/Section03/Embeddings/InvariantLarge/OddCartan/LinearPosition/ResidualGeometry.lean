module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.InvolutionModel
public import Theory.GroupTheory.SylowNormalCenterIntersection

/-!+# Comparing the whole-center and involution residuals

A normal subgroup of even order meets the ambient Sylow center in an
involution. The residual of C_D(Z(S)) lies in the residual of C_D(z) for
each such involution z. Conversely, the latter residual is perfect, so it
lies in the former as soon as the whole Sylow center centralizes it.

This isolates the actual remaining geometric assertion as a centralization
statement. Neither a cyclic Sylow center nor an involution-centralizer
isomorphism alone proves that assertion.

The normal-intersection and perfectness arguments also occur in the
parallel `OddCartan.UnitaryPosition.Residual` development. Here the relative
centralizer is expressed directly as a subgroup of the ambient group.

Source: Aschbacher–Smith, proof of 1.3.4, printed pp.510–511.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
variable {J : Type*} [Group J]

/-- The ambient image of the involution residual lies in D. -/
theorem involutionResidual_le (D : Subgroup J) (z : J) : involutionResidual D z ≤ D :=
  (map_subtype_le _).trans inf_le_left

/-- Including a finite solvable residual in the ambient group preserves perfectness. -/
instance involutionResidual_isPerfect [Finite J] (D : Subgroup J) (z : J) :
    Group.IsPerfect (involutionResidual D z) :=
  Group.IsPerfect.ofSurjective
    (f := (D ⊓ centralizer ({z} : Set J)).subtype.subgroupMap (solvableResidual _))
    ((D ⊓ centralizer ({z} : Set J)).subtype.subgroupMap_surjective _)

/-- Centralizing the whole Sylow center implies centralizing each of its elements. -/
theorem canonicalResidual_le_involutionResidual (D S : Subgroup J) {z : J}
    (hz : z ∈ centerImage S) : canonicalResidual D S ≤ involutionResidual D z := by
  apply map_solvableResidual_mono
  exact inf_le_inf_left D (centralizer_le (Set.singleton_subset_iff.mpr hz))

/-- Perfectness gives equality once the residual centralizes the entire Sylow center. -/
theorem canonicalResidual_eq_involutionResidual [Finite J] (D S : Subgroup J) {z : J}
    (hz : z ∈ centerImage S)
    (hc : involutionResidual D z ≤ centralizer (centerImage S : Set J)) :
    canonicalResidual D S = involutionResidual D z := by
  apply le_antisymm (canonicalResidual_le_involutionResidual D S hz)
  exact le_map_solvableResidual_of_isPerfect _ _ (le_inf (involutionResidual_le D z) hc)

/-- A normal subgroup of even order meets the ambient Sylow center in an involution. -/
theorem exists_involution_mem_centerImage [Finite J]
    (D : Subgroup J) [D.Normal] (S : Sylow 2 J) (hD : 2 ∣ Nat.card D) :
    ∃ z ∈ D ⊓ centerImage (S : Subgroup J), orderOf z = 2 := by
  obtain ⟨x, hx, hx1, hxD⟩ := S.exists_ne_one_mem_center_of_normal D hD
  let n := orderOf x / 2
  have hxn : orderOf (x ^ n) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne' (S.isPGroup'.dvd_orderOf hx1)
  refine ⟨((x ^ n : S) : J),
    ⟨D.pow_mem hxD n, ⟨x ^ n, (center S).pow_mem hx n, rfl⟩⟩, ?_⟩
  simpa only [Subgroup.orderOf_coe] using hxn

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
