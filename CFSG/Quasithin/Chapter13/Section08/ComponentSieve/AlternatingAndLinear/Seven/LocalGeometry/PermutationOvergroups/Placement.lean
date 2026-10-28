module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.PermutationOvergroups.Sylow
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.PermutationOvergroups.Placement.Coverage

/-!
# Placement of normalized solvable seven-point Sylow overgroups

A solvable subgroup containing the standard even Sylow subgroup has every
element in one of the two actual source partition stabilizers. The exhaustive
word certificates exclude all other elements by the derived series. A subgroup
contained in a union of two subgroups is contained in one of them. Applying this
to the image in S₇ proves the fixed-coordinate statement for both A₇ and S₇.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, printed pp.958–959 (1 March 2004 manuscript).
-/

public section
open Equiv Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.PermutationOvergroups

private theorem le_one_of_mem_union {G : Type*} [Group G] (H K L : Subgroup G)
    (h : ∀ g ∈ H, g ∈ K ∨ g ∈ L) : H ≤ K ∨ H ≤ L := by
  classical
  by_cases hK : H ≤ K
  · exact Or.inl hK
  right
  obtain ⟨x, hxH, hxK⟩ := Set.not_subset.mp hK
  have hxL := (h x hxH).resolve_left hxK
  intro y hyH
  by_contra hyL
  have hyK := (h y hyH).resolve_right hyL
  rcases h (x * y) (H.mul_mem hxH hyH) with hxyK | hxyL
  · exact hxK ((K.mul_mem_cancel_right hyK).mp hxyK)
  · exact hyL ((L.mul_mem_cancel_left hxL).mp hxyL)

/-- Already the standard even Sylow subgroup forces the two source alternatives
for a solvable subgroup of the full symmetric group. -/
theorem solvable_overgroup_standardEvenTwo_placement (H : Subgroup S7)
    [Group.IsSolvable H]
    (hT : ∀ g ∈ standardTwo, g ∈ alternatingGroup (Fin 7) → g ∈ H) :
    H ≤ fourThreeStabilizer ∨ H ≤ pairStabilizer := by
  have hu (i : Fin 8) : PlacementCertificate.upper i ∈ H :=
    hT _ (PlacementCertificate.upper_mem i).1 (PlacementCertificate.upper_mem i).2
  apply le_one_of_mem_union
  intro g hg
  obtain ⟨i, j, k, rfl⟩ := PlacementCertificate.decomposition g
  have hj : PlacementCertificate.rep j ∈ H := by
    have h := H.mul_mem (H.mul_mem (H.inv_mem (hu i)) hg) (H.inv_mem (hu k))
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using h
  rcases PlacementCertificate.rep_alternative H hu j hj with h | h | h
  · exact Or.inl (fourThreeStabilizer.mul_mem
      (fourThreeStabilizer.mul_mem (PlacementCertificate.upper_mem i).1.1 h)
      (PlacementCertificate.upper_mem k).1.1)
  · exact Or.inr (pairStabilizer.mul_mem
      (pairStabilizer.mul_mem (PlacementCertificate.upper_mem i).1.2 h)
      (PlacementCertificate.upper_mem k).1.2)
  · exact (h inferInstance).elim

/-- A solvable overgroup of the fixed standard Sylow subgroup lies in the
four-plus-three stabilizer or in the three-pair-and-singleton stabilizer,
with the same coordinates in the supplied ambient group. -/
theorem solvable_overgroup_placement (B : Subgroup S7)
    (hB : alternatingGroup (Fin 7) ≤ B) (P : Subgroup B)
    [Group.IsSolvable P] (hP : standardTwoIn B ≤ P) :
    P ≤ fourThreeStabilizer.comap B.subtype ∨ P ≤ pairStabilizer.comap B.subtype := by
  let H : Subgroup S7 := P.map B.subtype
  let e : P ≃* H := P.equivMapOfInjective B.subtype B.subtype_injective
  have : Group.IsSolvable H :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hT : ∀ g ∈ standardTwo, g ∈ alternatingGroup (Fin 7) → g ∈ H := by
    intro g hg hga
    exact ⟨⟨g, hB hga⟩, hP hg, rfl⟩
  rcases solvable_overgroup_standardEvenTwo_placement H hT with h | h
  · exact Or.inl (Subgroup.map_le_iff_le_comap.mp h)
  · exact Or.inr (Subgroup.map_le_iff_le_comap.mp h)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.PermutationOvergroups
