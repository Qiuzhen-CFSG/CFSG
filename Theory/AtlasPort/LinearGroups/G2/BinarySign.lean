module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/BinarySign.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.G2.BinaryHexagon
public import Theory.AtlasPort.LinearGroups.G2.BinaryExceptionFromCharacter
public import Theory.AtlasPort.GroupTheory.G2ActionInvolutionSign

/-!
The signs of the actual binary hexagon line permutations distinguish long
and short roots: their fixed-line counts are seven and nine out of 63.
This character proves the binary exception and computes its normal subgroup.
-/

@[expose] public section

namespace Atlas.G2.Binary
open Atlas.G2.Explicit

 theorem lineSign_rootA_one : lineSign (rootA (1:K))=1 := by
  classical
  let := Fintype.ofFinite Line
  have hp : (rootA (1:K))^2=1 := by
    rw [pow_two,rootA_add,show (1:K)+1=0 by decide,rootA_zero]
  change Equiv.Perm.sign (MulAction.toPermHom (Model K) Line (rootA 1))=1
  rw [Atlas.GroupTheory.action_sign_involution _ hp,card_Line,card_fixed_rootA]
  norm_num

 theorem lineSign_rootA (a:K) : lineSign (rootA a)=1 := by
  have h : ∀a:ZMod 2,a=0∨a=1 := by decide
  rcases h a with rfl|rfl
  · rw [rootA_zero,map_one]
  · exact lineSign_rootA_one

 theorem lineSign_rootF_one : lineSign (rootF (1:K))= -1 := by
  classical
  let := Fintype.ofFinite Line
  have hp : (rootF (1:K))^2=1 := BinaryException.F_sq
  change Equiv.Perm.sign (MulAction.toPermHom (Model K) Line (rootF 1))= -1
  rw [Atlas.GroupTheory.action_sign_involution _ hp,card_Line,card_fixed_rootF]
  norm_num

 theorem lineSign_surjective : Function.Surjective lineSign := by
  intro u
  rcases Int.units_eq_one_or u with rfl|rfl
  · exact ⟨1,map_one _⟩
  · exact ⟨rootF 1,lineSign_rootF_one⟩

end Atlas.G2.Binary

namespace Atlas.G2.BinaryException

 theorem H_proper : H ≠ ⊤ :=
  H_proper_of_character Binary.lineSign Binary.lineSign_rootA Binary.lineSign_rootF_one
 theorem index_H : H.index=2 :=
  index_two_of_character Binary.lineSign Binary.lineSign_rootA Binary.lineSign_rootF_one
 theorem card_H : Nat.card H=6048 :=
  order_of_character Binary.lineSign Binary.lineSign_rootA Binary.lineSign_rootF_one
 theorem lineSign_kernel : Binary.lineSign.ker=H :=
  ker_eq_H_of_character Binary.lineSign Binary.lineSign_rootA Binary.lineSign_rootF_one
 theorem not_simple : ¬ IsSimpleGroup (Model K) :=
  not_simple_of_character Binary.lineSign Binary.lineSign_rootA Binary.lineSign_rootF_one

theorem H_singularPoints_pretransitive :
    MulAction.IsPretransitive H (SingularPoints K) := by
  let := singularPoints_primitive (K := K)
  exact Atlas.GroupTheory.normal_pretransitive (X := SingularPoints K) H H_ne_bot

theorem card_H_pointStabilizer :
    Nat.card (MulAction.stabilizer H (firstPoint (K := K)))=96 := by
  let := H_singularPoints_pretransitive
  have hc : Nat.card H = Nat.card (SingularPoints K) *
      Nat.card (MulAction.stabilizer H (firstPoint (K := K))) := by
    rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H
      (firstPoint (K := K))),Nat.card_prod]
    congr 1
    rw [MulAction.orbit_eq_univ]
    exact Nat.card_congr (Equiv.Set.univ (SingularPoints K))
  rw [card_H,OrderChecks.binary_points] at hc
  omega

end Atlas.G2.BinaryException

