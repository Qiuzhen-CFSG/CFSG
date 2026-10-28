module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.BorelCertification.SolvableFlags.Geometry
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.BorelCertification.SolvableFlags.Combinatorics

/-!
# Simple-root constraints on the coordinates of an invariant subspace

The four prescribed simple roots, and their actual negatives for the opposite
sign, give eight implications between coordinate-line memberships. These
are exactly the edges of the diamond-shaped order on the eight natural
weights. The matrix identities from `Triangular` determine each action
without expanding the Spin construction.

Source: GLS3, 1.11.2 (`refs/KGroup/GLS3/Chapter1.tex`), specialized to D4.
-/

@[expose] public section
open Theory Theory.AlgebraicGroup
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.NaturalCoefficients
open Triality.Standard.PositiveCoordinates
noncomputable section
namespace Triality.SimplyConnected.OppositeBorels.BorelCertification.SolvableFlags
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

lemma signedRootPoint_mem_candidate (negative : Bool) (r : Fin 12) (a : k) :
    rootPoint k (signedRoot negative (rootIndex r)) a ∈ candidate k negative := by
  apply rootGenerated_le_torusRootGenerated k (signedRoots k negative)
  apply rootPoint_mem_rootGenerated
  have hp : pinnedRootIndex k (rootIndex r) ∈ positiveRoots k := by
    rw [← range_positiveRoot]
    exact ⟨r, rfl⟩
  cases negative
  · exact hp
  · change (pinnedRootData k).neg (pinnedRootIndex k (negativeRoot (rootIndex r))) ∈ positiveRoots k
    rwa [pinnedRootData_neg, negativeRoot_negativeRoot]

private def edgeRoot (i j : Fin 8) : Fin 12 :=
  if i = 0 ∨ j = 7 then 0 else
  if i = 1 ∨ j = 6 then 3 else
  if (i = 2 ∧ j = 3) ∨ (i = 4 ∧ j = 5) then 1 else 2

omit [CharP k 2] in
private lemma basis_displacement {g : Points k} {p q r s : Index}
    (hM : pointMatrix k g = 1 + Matrix.single p q 1 + Matrix.single r s 1)
    (hqs : q ≠ s) :
    (naturalAction k g).1 (basis k q) - basis k q = basis k p := by
  classical
  apply (basis k).ext_elem
  intro l
  change (basis k).coord l _ = (basis k).coord l _
  rw [map_sub, ← pointMatrix_apply, hM]
  simp [Matrix.single_apply, Matrix.one_apply, hqs.symm, Finsupp.single_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self, eq_comm]

omit [CharP k 2] in
private lemma basis_displacement_second {g : Points k} {p q r s : Index}
    (hM : pointMatrix k g = 1 + Matrix.single p q 1 + Matrix.single r s 1)
    (hqs : s ≠ q) :
    (naturalAction k g).1 (basis k s) - basis k s = basis k r :=
  basis_displacement k (hM.trans (add_right_comm _ _ _)) hqs

private lemma edge_root_action (negative : Bool) (i j : Fin 8) (hij : Combinatorics.Edge i j) :
    (naturalAction k (rootPoint k (signedRoot negative (rootIndex (edgeRoot i j))) 1)).1
        (orderedBasis k (signedOrder negative) j) - orderedBasis k (signedOrder negative) j =
      orderedBasis k (signedOrder negative) i := by
  simp only [orderedBasis_apply]
  rw [Combinatorics.Edge] at hij
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases negative
    · exact basis_displacement k (root_difference_matrix k 0 1 (by decide) 1) (by decide)
    · exact basis_displacement_second k (root_negative_difference_matrix k 0 1 (by decide) 1) (by decide)
  · cases negative
    · exact basis_displacement k (root_difference_matrix k 1 2 (by decide) 1) (by decide)
    · exact basis_displacement_second k (root_negative_difference_matrix k 1 2 (by decide) 1) (by decide)
  · cases negative
    · exact basis_displacement k (root_difference_matrix k 2 3 (by decide) 1) (by decide)
    · exact basis_displacement_second k (root_negative_difference_matrix k 2 3 (by decide) 1) (by decide)
  · cases negative
    · exact basis_displacement k (root_sum_matrix k 2 3 (by decide) 1) (by decide)
    · exact basis_displacement k (root_negative_sum_matrix k 2 3 (by decide) 1) (by decide)
  · cases negative
    · exact basis_displacement_second k (root_sum_matrix k 2 3 (by decide) 1) (by decide)
    · exact basis_displacement_second k (root_negative_sum_matrix k 2 3 (by decide) 1) (by decide)
  · cases negative
    · exact basis_displacement_second k (root_difference_matrix k 2 3 (by decide) 1) (by decide)
    · exact basis_displacement k (root_negative_difference_matrix k 2 3 (by decide) 1) (by decide)
  · cases negative
    · exact basis_displacement_second k (root_difference_matrix k 1 2 (by decide) 1) (by decide)
    · exact basis_displacement k (root_negative_difference_matrix k 1 2 (by decide) 1) (by decide)
  · cases negative
    · exact basis_displacement_second k (root_difference_matrix k 0 1 (by decide) 1) (by decide)
    · exact basis_displacement k (root_negative_difference_matrix k 0 1 (by decide) 1) (by decide)

lemma basis_mem_of_edge (negative : Bool) (W : Submodule k (QuadraticSpace k))
    (hW : ∀ g ∈ candidate k negative, ∀ v ∈ W, (naturalAction k g).1 v ∈ W)
    (i j : Fin 8) (hij : Combinatorics.Edge i j)
    (hj : orderedBasis k (signedOrder negative) j ∈ W) :
    orderedBasis k (signedOrder negative) i ∈ W := by
  have hh := W.sub_mem
    (hW _ (signedRootPoint_mem_candidate k negative (edgeRoot i j) 1) _ hj) hj
  rwa [edge_root_action k negative i j hij] at hh

end Triality.SimplyConnected.OppositeBorels.BorelCertification.SolvableFlags
