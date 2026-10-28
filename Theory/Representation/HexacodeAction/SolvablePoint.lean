module
public import Theory.Representation.HexacodeAction.PairGeometry
public import Theory.Representation.HexacodeAction.PlaneStabilizer

/-!
# Solvable hexacode point stabilizers select coordinate pairs

The even stabilizer of a full-weight field point maps onto A₅. A solvable
stabilizer in any actor containing the even hexacode cover therefore cannot
fix such a point. The actual field-point dichotomy leaves a double-zero
coordinate pair, with the original binary subspace retained.

This uses the existing attributed ATLAS hexacode action and its proved
six-plane quotient. Source: Aschbacher–Smith, 13.8.21(2), printed p.956;
this supplies the pair geometry for the literal V_H/U_H permutation section.
-/

public section
open Atlas.Codes Subgroup
namespace Representation.Hexacode
variable {A : Type*} [Group A]

theorem fieldPoint_pair_of_solvable_stabilizer
    (e : A →* HexAutomorphisms) (heven : hexSign.ker ≤ e.range)
    (D : Submodule F hexacode) (hd : Module.finrank F D = 1)
    (hsolv : Group.IsSolvable
      ((BinaryOffender.subspaceStabilizer action (D.restrictScalars (ZMod 2))).comap e)) :
    ∃ s : BinaryPermutation.SixPairsQuadratic.Pair,
      D.restrictScalars (ZMod 2) = zeroPairPlane s := by
  apply (fieldPoint_full_or_pair D hd).resolve_left
  intro hfull
  let S := BinaryOffender.subspaceStabilizer action (D.restrictScalars (ZMod 2))
  let P := S.comap e
  let := hsolv
  let : Group.IsSolvable (P.map e) :=
    Group.isSolvable_of_surjective (e.subgroupMap_surjective P)
  have hEP : hexSign.ker ⊓ S ≤ P.map e := by
    rw [Subgroup.map_comap_eq]
    exact le_inf (inf_le_left.trans heven) inf_le_right
  let : Group.IsSolvable (hexSign.ker ⊓ S : Subgroup HexAutomorphisms) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hEP)
  obtain ⟨f,hf⟩ := exists_surjective_planeStabilizer_A5 (D.restrictScalars (ZMod 2)) hfull
  let : Group.IsSolvable (alternatingGroup (Fin 5)) := Group.isSolvable_of_surjective hf
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance
end Representation.Hexacode
