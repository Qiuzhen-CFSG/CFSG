module
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Natural
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Words
import Mathlib.Tactic.FinCases

/-!
# The two max4 generators in the marked natural actor

The published conjugation identities on the three marked involutions determine
both natural matrices. These equations identify the actor exactly, without
choosing an unrelated isomorphism with SL3(2). The two lifted generators generate
the actual max4 subtype, for extension of subsequent intertwining equations.

Source: Aschbacher--Smith I.2.2(7), printed pp.412--413, and GLS3 Table 5.3r.
Original ATLAS words and their attribution are inherited from SylowOvergroups.
-/

open Subgroup
open Rudvalis Rudvalis.SylowOvergroups Rudvalis.CoreQuotients
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
open scoped IsMulCommutative
namespace Rudvalis.CoveringIncidence.Max4Steinberg

local instance : IsElementaryAbelian 2 (elementary 2) :=
  RankOneEightCharacteristic.elementary_two_elementary

@[expose] public def actorGenerator (i : Fin 2) : max4 :=
  ![⟨max4Generators.1, subset_closure (by simp)⟩,
    ⟨max4Generators.2, subset_closure (by simp)⟩] i

@[expose] public def naturalGenerator (i : Fin 2) : BinaryLinearThree.Group :=
  ![⟨!![1,1,0;0,1,0;0,1,1], by decide⟩,
    ⟨!![1,0,0;1,1,1;0,1,0], by decide⟩] i

public theorem actorGenerator_closure : closure (Set.range actorGenerator) = ⊤ := by
  apply map_injective max4.subtype_injective
  rw [MonoidHom.map_closure, ← Set.range_comp]
  rw [← MonoidHom.range_eq_map, range_subtype]
  congr 1
  ext x
  simp only [Set.mem_range, Function.comp_apply, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [actorGenerator]
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

private theorem action_basis (i : Fin 2) (j : Fin 3) :
    max4EightAction (actorGenerator i) (markedBasis j) =
      (![![markedBasis 0, markedBasis 0 * markedBasis 1 * markedBasis 2, markedBasis 2],
          ![markedBasis 0 * markedBasis 1, markedBasis 1 * markedBasis 2, markedBasis 1]] i j) := by
  apply Subtype.ext
  fin_cases i <;> fin_cases j
  · exact RankOneEightAction.first_conj_zero
  · exact RankOneEightAction.first_conj_one
  · exact RankOneEightAction.first_conj_two
  · exact RankOneEightAction.second_conj_zero
  · exact RankOneEightAction.second_conj_one
  · exact RankOneEightAction.second_conj_two

/-- The matrices use the published marking, with no choice of a new PSL actor. -/
public theorem naturalActor_generator (i : Fin 2) :
    max4NaturalActor (QuotientGroup.mk' (pCore 2 max4) (actorGenerator i)) =
      naturalGenerator i := by
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply (Pi.basisFun (ZMod 2) (Fin 3)).ext
  intro j
  simp only [Pi.basisFun_apply]
  change BinaryLinearThree.W
    (max4NaturalActor (QuotientGroup.mk' (pCore 2 max4) (actorGenerator i)))
    (Pi.single j 1) = (naturalGenerator i).val.mulVec (Pi.single j 1)
  rw [← markedCoordinates_basis j, max4_marked_natural, action_basis]
  fin_cases i <;> fin_cases j <;>
    simp [naturalGenerator, map_add, markedCoordinates_basis] <;> decide

end Rudvalis.CoveringIncidence.Max4Steinberg
