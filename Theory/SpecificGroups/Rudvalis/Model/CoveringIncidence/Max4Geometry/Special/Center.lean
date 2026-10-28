module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special.Structure
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Natural
public import Theory.GroupTheory.ClassTwoCommutator

/-!
# The center of the literal Rudvalis max4 core

Assuming that the eleven fixed words generate the core P, its center is the
original marked eight-group E. The first marked coordinate of [g_i, x], for
0 ≤ i < 8, defines eight homomorphisms on P, since the derived subgroup is E
and E is central. Their values on the first eight generators form an invertible
binary matrix. A small inverse certificate reconstructs the actual map P → P/E
from those eight homomorphisms: the reconstruction agrees on all eleven
generators, with the last three lying in E. Every central element has zero
commutator coordinates and hence lies in E.

Generation is the only additional premise. In particular, the proof does not
use the order of P/Z(P), a basis for that quotient, or a radical assumption.
Source: Aschbacher--Smith I.2.2(7), printed pp.412--413; GLS3 Table 5.3r and
its justification, printed pp.291--292. All words and marked coordinates are
taken in the original ambient Rudvalis model.
-/

namespace Rudvalis.CoveringIncidence.Max4Special
open Subgroup SylowOvergroups.RadicalCoverage.LocalCover
open scoped commutatorElement IsMulCommutative

local instance : IsElementaryAbelian 2 (elementary 2) :=
  RankOneEightCharacteristic.elementary_two_elementary

private noncomputable def firstCoordinate : elementary 2 →* Multiplicative (ZMod 2) :=
  ((LinearMap.proj 0).comp markedCoordinates.toLinearMap).toAddMonoidHom.toMultiplicativeRight

private theorem firstCoordinate_basis (i : Fin 3) :
    firstCoordinate (markedBasis i) = Multiplicative.ofAdd ((Pi.single i 1 : Fin 3 → ZMod 2) 0) := by
  change markedCoordinates (Additive.ofMul (markedBasis i)) 0 = _
  rw [markedCoordinates_basis]
  rfl

private theorem firstCoordinate_centralValue (n : Fin 8) :
    firstCoordinate ⟨centralValue n, centralValue_mem n⟩ =
      Multiplicative.ofAdd (n.val : ZMod 2) := by
  have he : (⟨centralValue n, centralValue_mem n⟩ : elementary 2) =
      (if n.val % 2 = 1 then markedBasis 0 else 1) *
      (if n.val / 2 % 2 = 1 then markedBasis 1 else 1) *
      (if n.val / 4 % 2 = 1 then markedBasis 2 else 1) := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_one, markedBasis, apply_ite] using centralValue_eq n
  rw [he]
  fin_cases n <;> simp [map_mul, firstCoordinate_basis] <;> decide +kernel

private noncomputable def commutatorRow
    (hgen : closure (Set.range Max4Words.generator) = max4Core) (i : Fin 8) :
    max4Core →* Multiplicative (ZMod 2) := by
  let hc : _root_.commutator max4Core ≤ center max4Core := by
    rw [derived_eq_marked_of_generation hgen]
    exact markedCore_le_center
  let c := ClassTwo.commutatorHom hc (intrinsicGenerator (i.castAdd 3))
  let f : max4Core →* elementary 2 := (max4Core.subtype.comp c).codRestrict
    (elementary 2) (by
      intro x
      change ⁅intrinsicGenerator (i.castAdd 3), x⁆ ∈ markedCore
      rw [← derived_eq_marked_of_generation hgen]
      exact commutator_mem_commutator (mem_top _) (mem_top _))
  exact firstCoordinate.comp f

private theorem commutatorRow_generator
    (hgen : closure (Set.range Max4Words.generator) = max4Core) (i : Fin 8) (j : Fin 11) :
    commutatorRow hgen i (intrinsicGenerator j) =
      Multiplicative.ofAdd ((commutatorCode (i.castAdd 3) j).val : ZMod 2) := by
  change firstCoordinate ⟨⁅Max4Words.generator (i.castAdd 3), Max4Words.generator j⁆, _⟩ = _
  simpa only [generator_commutator] using
    firstCoordinate_centralValue (commutatorCode (i.castAdd 3) j)

/-- Candidate inverse of the first-coordinate commutator matrix, encoded by
row masks. The next lemma checks it directly against the literal relation codes. -/
private def inversePairing : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  fun i j => ((![208, 88, 232, 102, 35, 92, 47, 5] i : ℕ) / 2 ^ j.val % 2 : ℕ)

private theorem inversePairing_column (j : Fin 8) :
    inversePairing.mulVec (fun i : Fin 8 =>
      ((commutatorCode (i.castAdd 3) (j.castAdd 3)).val : ZMod 2)) = Pi.single j 1 := by
  revert j
  decide +kernel

private theorem commutator_column_center (j : Fin 3) :
    (fun i : Fin 8 => ((commutatorCode (i.castAdd 3) (centerIndex j)).val : ZMod 2)) = 0 := by
  revert j
  decide +kernel

private noncomputable def commutatorCoordinates
    (hgen : closure (Set.range Max4Words.generator) = max4Core) :
    max4Core →* Multiplicative (Fin 8 → ZMod 2) :=
  (AddMonoidHom.pi (fun i => (commutatorRow hgen i).toAdditiveLeft)).toMultiplicativeRight

private theorem commutatorCoordinates_generator
    (hgen : closure (Set.range Max4Words.generator) = max4Core) (j : Fin 11) :
    commutatorCoordinates hgen (intrinsicGenerator j) = Multiplicative.ofAdd
      (fun i : Fin 8 => ((commutatorCode (i.castAdd 3) j).val : ZMod 2)) := by
  apply Multiplicative.toAdd.injective
  funext i
  exact congrArg Multiplicative.toAdd (commutatorRow_generator hgen i j)

private theorem commutatorCoordinates_center
    (hgen : closure (Set.range Max4Words.generator) = max4Core)
    (x : max4Core) (hx : x ∈ center max4Core) : commutatorCoordinates hgen x = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  change (firstCoordinate ⟨(⁅intrinsicGenerator (i.castAdd 3), x⁆ : max4Core).val, _⟩).toAdd = 0
  have he : ⁅intrinsicGenerator (i.castAdd 3), x⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hx _)
  simp only [he, Subgroup.coe_one]
  exact congrArg Multiplicative.toAdd firstCoordinate.map_one

private theorem quotient_generator_center (j : Fin 3) :
    QuotientGroup.mk' markedCore (intrinsicGenerator (centerIndex j)) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  change Max4Words.generator (centerIndex j) ∈ elementary 2
  rw [← basis_eq_generator]
  exact RankOneEightCharacteristic.basis_mem j

/-- Reconstruct the literal quotient map from the commutator coordinates. -/
private theorem center_le_marked_of_generation
    (hgen : closure (Set.range Max4Words.generator) = max4Core) :
    center max4Core ≤ markedCore := by
  let : IsElementaryAbelian 2 (max4Core ⧸ markedCore) :=
    markedQuotient_elementary_of_generation hgen
  let q := QuotientGroup.mk' markedCore
  let l : (Fin 8 → ZMod 2) →ₗ[ZMod 2] Additive (max4Core ⧸ markedCore) :=
    Fintype.linearCombination (ZMod 2) (fun i : Fin 8 =>
      Additive.ofMul (q (intrinsicGenerator (i.castAdd 3))))
  let r : Multiplicative (Fin 8 → ZMod 2) →* max4Core ⧸ markedCore :=
    (l.comp inversePairing.mulVecLin).toAddMonoidHom.toMultiplicativeLeft
  have hsmall (j : Fin 8) :
      r (commutatorCoordinates hgen (intrinsicGenerator (j.castAdd 3))) =
        q (intrinsicGenerator (j.castAdd 3)) := by
    rw [commutatorCoordinates_generator]
    change Additive.toMul (l (inversePairing.mulVec (fun i : Fin 8 =>
      ((commutatorCode (i.castAdd 3) (j.castAdd 3)).val : ZMod 2)))) = _
    rw [inversePairing_column]
    simp [l]
  have hcentral (j : Fin 3) :
      r (commutatorCoordinates hgen (intrinsicGenerator (centerIndex j))) =
        q (intrinsicGenerator (centerIndex j)) := by
    rw [commutatorCoordinates_generator, commutator_column_center]
    change r 1 = _
    rw [map_one, quotient_generator_center]
  have he : r.comp (commutatorCoordinates hgen) = q := by
    apply MonoidHom.eq_of_eqOn_dense (intrinsic_generation_of_generation hgen)
    rintro _ ⟨j, rfl⟩
    change r (commutatorCoordinates hgen (intrinsicGenerator j)) = q (intrinsicGenerator j)
    fin_cases j
    · exact hsmall 0
    · exact hsmall 1
    · exact hsmall 2
    · exact hsmall 3
    · exact hsmall 4
    · exact hsmall 5
    · exact hsmall 6
    · exact hsmall 7
    · exact hcentral 2
    · exact hcentral 1
    · exact hcentral 0
  intro x hx
  apply (QuotientGroup.eq_one_iff _).mp
  change q x = 1
  rw [← he, MonoidHom.comp_apply, commutatorCoordinates_center hgen x hx, map_one]

/-- Intrinsic center equality under the fixed word-generation premise. -/
public theorem center_eq_marked_of_generation
    (hgen : closure (Set.range Max4Words.generator) = max4Core) :
    center max4Core = markedCore :=
  le_antisymm (center_le_marked_of_generation hgen) markedCore_le_center

/-- Every element of the actual core center belongs to the marked eight-group. -/
public theorem max4CoreCenter_le_marked_of_generation
    (hgen : closure (Set.range Max4Words.generator) = max4Core) :
    max4CoreCenter ≤ elementary 2 := by
  rintro x ⟨y, hy, rfl⟩
  exact center_le_marked_of_generation hgen hy

/-- The actual core center, embedded in Ru, is the original marked eight-group. -/
public theorem max4CoreCenter_eq_marked_of_generation
    (hgen : closure (Set.range Max4Words.generator) = max4Core) :
    max4CoreCenter = elementary 2 :=
  le_antisymm (max4CoreCenter_le_marked_of_generation hgen) marked_eight_le_core_center

end Rudvalis.CoveringIncidence.Max4Special
