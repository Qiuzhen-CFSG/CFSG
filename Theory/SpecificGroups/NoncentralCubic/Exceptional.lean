module

public import Theory.SpecificGroups.NoncentralCubic.Linear
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Theory.AtlasPort.LinearGroups.G2.BinaryThreeRank.CubicWitness
public import Theory.AtlasPort.LinearGroups.G2.PairStabilizer
public import Theory.Representation.HexacodeAction.ThreeRank

/-!
# Noncentral cubics in the exceptional perfect FF actors

Explicit permutations handle A₆ and A₇. The opposite-vector stabilizer in the
split-octonion model embeds SL₂, whose cubic witness was constructed in
`Linear`. For G₂(2)′ we retain the existing noncommuting pair in its actual
order-27 subgroup. The hexacode case retains the actual monomial triple cover
and its checked coordinate map, without replacing that cover by A₆.

The imported octonion and hexacode constructions preserve their ATLAS source
attribution and license; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source application: Aschbacher–Smith, B.5.6, printed p.105, and the
perfect-component argument in 15.3.49(i), printed pp.1143–1144.
-/

public section
open Subgroup Equiv
namespace Theory.SpecificGroups.NoncentralCubic

/-- Explicit three-cycles in the two alternating actors fail to commute with
an even product of two transpositions. -/
theorem exists_noncentral_cubic_alternating (n : ℕ) (hn : n = 6 ∨ n = 7) :
    ∃ x : alternatingGroup (Fin n), orderOf x = 3 ∧ x ∉ center (alternatingGroup (Fin n)) := by
  let x : alternatingGroup (Fin n) :=
    ⟨swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ * swap (⟨1, by omega⟩ : Fin n) ⟨2, by omega⟩, by
      rw [Equiv.Perm.mem_alternatingGroup]
      rcases hn with rfl | rfl <;> decide⟩
  let y : alternatingGroup (Fin n) :=
    ⟨swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ * swap (⟨2, by omega⟩ : Fin n) ⟨3, by omega⟩, by
      rw [Equiv.Perm.mem_alternatingGroup]
      rcases hn with rfl | rfl <;> decide⟩
  have hp : x ^ 3 = 1 := by rcases hn with rfl | rfl <;> decide
  have hne : x ≠ 1 := by rcases hn with rfl | rfl <;> decide
  have hnc : y * x ≠ x * y := by rcases hn with rfl | rfl <;> decide
  exact ⟨x, orderOf_eq_prime hp hne, fun hc => hnc (mem_center_iff.mp hc y)⟩

/-- The cubic in the nonabelian order-27 subgroup of the actual G₂(2)′ is
noncentral already inside that derived group. -/
theorem exists_noncentral_cubic_g2Derived : ∃ x : commutator (Atlas.G2.Model (ZMod 2)),
    orderOf x = 3 ∧ x ∉ center (commutator (Atlas.G2.Model (ZMod 2))) := by
  obtain ⟨P, _, x, y, hx, hxy⟩ := Atlas.G2.BinaryThreeRank.exists_noncentral_cubic_three_subgroup
  have hn : (x : commutator (Atlas.G2.Model (ZMod 2))) ∉
      center (commutator (Atlas.G2.Model (ZMod 2))) := by
    intro hc
    apply hxy
    apply Subtype.ext
    exact (mem_center_iff.mp hc y.val).symm
  refine ⟨x.val, orderOf_eq_prime ?_ (fun h => hn (h ▸ (center _).one_mem)), hn⟩
  exact congrArg Subtype.val hx

/-- The opposite-vector stabilizer embeds SL₂ in the split-octonion model. -/
theorem exists_noncentral_cubic_g2 (F : Type*) [Field F] [CharP F 2] :
    ∃ x : Atlas.G2.Model F, orderOf x = 3 ∧ x ∉ center (Atlas.G2.Model F) := by
  let e := Atlas.G2.PairStabilizer.fixingPairEquivSL2 (F := F)
  exact Theory.GroupTheory.exists_noncentral_orderOf_of_injective
    ((Atlas.G2.PairStabilizer.fixingPair (F := F)).subtype.comp e.symm.toMonoidHom)
    (Subtype.val_injective.comp e.symm.injective)
    (exists_noncentral_cubic_specialLinear F (by decide : 2 ≤ 2))

/-- The checked monomial lift has order three and nontrivial coordinate image
in A₆, whereas the center of the actual triple cover is the coordinate kernel. -/
theorem exists_noncentral_cubic_hexacode :
    ∃ x : Atlas.Codes.HexEvenAutomorphisms,
      orderOf x = 3 ∧ x ∉ center Atlas.Codes.HexEvenAutomorphisms :=
  ⟨Representation.Hexacode.evenX, Representation.Hexacode.evenX_order,
    Representation.Hexacode.evenX_not_mem_center⟩

end Theory.SpecificGroups.NoncentralCubic
