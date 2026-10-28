module
public import Theory.GroupTheory.QuaternionCentralProductQuotient

/-!
# A hyperbolic frame in the quaternion central product

A checked 64-word certificate supplies two involutions in the centralizer
of the standard noncentral involution of Q₈ * Q₈. Together with the marked
central four they generate its full centralizer. All quotient statements
are proved through the literal diagonal-center quotient map.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 45.3, p.243.
-/

open Subgroup
open scoped commutatorElement
namespace QuaternionCentralProduct
private instance : DecidablePred (fun x : Pair => x ∈ diagonalCenter) :=
  fun x => inferInstanceAs (Decidable (x = 1 ∨ x = diagonalInvolution))

private abbrev i : QuaternionGroup 2 := QuaternionGroup.a 1
private abbrev j : QuaternionGroup 2 := QuaternionGroup.xa 0
private def Z : Pair := (QuaternionGroup.a 2,1)
private def U : Pair := (i,i)
private def A : Pair := (j,j)
private def B : Pair := (i*j,j)

private theorem frame_relations :
    Z^2 ∈ diagonalCenter ∧ Z ∉ diagonalCenter ∧
    U^2 ∈ diagonalCenter ∧ U ∉ diagonalCenter ∧
    A^2 ∈ diagonalCenter ∧ B^2 ∈ diagonalCenter ∧
    ⁅A,U⁆ ∈ diagonalCenter ∧ ⁅B,U⁆ ∈ diagonalCenter ∧
    (A*B)*(B*A*Z)⁻¹ ∈ diagonalCenter ∧
    (∀ x : Pair, ⁅x,Z⁆ ∈ diagonalCenter) ∧
    (∃ x : Pair, ⁅x,U⁆ ∉ diagonalCenter) := by decide +kernel

private theorem frame_coverage : ∀ x : Pair, ⁅x,U⁆ ∈ diagonalCenter →
    ∃ a b c d : Fin 2,
      x*(Z^a.val*U^b.val*A^c.val*B^d.val)⁻¹ ∈ diagonalCenter := by decide +kernel


public def frameZ : Model := QuotientGroup.mk' diagonalCenter Z
public def frameU : Model := QuotientGroup.mk' diagonalCenter U
public def frameA : Model := QuotientGroup.mk' diagonalCenter A
public def frameB : Model := QuotientGroup.mk' diagonalCenter B

private theorem quotient_commutes_iff (x y : Pair) :
    Commute (QuotientGroup.mk' diagonalCenter x) (QuotientGroup.mk' diagonalCenter y) ↔
      ⁅x,y⁆ ∈ diagonalCenter := by
  change (_ * _ = _ * _) ↔ _
  rw [← commutatorElement_eq_one_iff_mul_comm,← map_commutatorElement]
  exact QuotientGroup.eq_one_iff _

public theorem frameZ_square : frameZ^2=1 := by
  rw [frameZ,← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr frame_relations.1
public theorem frameZ_ne_one : frameZ ≠ 1 := by
  intro he
  exact frame_relations.2.1 ((QuotientGroup.eq_one_iff _).mp he)
public theorem frameZ_central : frameZ ∈ center Model := by
  apply mem_center_iff.mpr
  intro x
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
  exact (quotient_commutes_iff x Z).mpr (frame_relations.2.2.2.2.2.2.2.2.2.1 x)
public theorem frameU_square : frameU^2=1 := by
  rw [frameU,← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr frame_relations.2.2.1
public theorem frameU_ne_one : frameU ≠ 1 := by
  intro he
  exact frame_relations.2.2.2.1 ((QuotientGroup.eq_one_iff _).mp he)
public theorem frameU_not_central : frameU ∉ center Model := by
  intro hu
  obtain ⟨x,hx⟩ := frame_relations.2.2.2.2.2.2.2.2.2.2
  exact hx ((quotient_commutes_iff x U).mp (mem_center_iff.mp hu _))
public theorem frameA_square : frameA^2=1 := by
  rw [frameA,← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr frame_relations.2.2.2.2.1
public theorem frameB_square : frameB^2=1 := by
  rw [frameB,← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr frame_relations.2.2.2.2.2.1
public theorem frameA_commute : Commute frameA frameU :=
  (quotient_commutes_iff A U).mpr frame_relations.2.2.2.2.2.2.1
public theorem frameB_commute : Commute frameB frameU :=
  (quotient_commutes_iff B U).mpr frame_relations.2.2.2.2.2.2.2.1
public theorem frame_swap : frameA*frameB=frameB*frameA*frameZ := by
  change QuotientGroup.mk' diagonalCenter A * QuotientGroup.mk' diagonalCenter B = _
  simp only [frameA,frameB,frameZ,← map_mul]
  exact QuotientGroup.eq_iff_div_mem.mpr frame_relations.2.2.2.2.2.2.2.2.1

public theorem frame_centralizer_words (x : Model) (hx : Commute x frameU) :
    ∃ a b c d : Fin 2,
      x=frameZ^a.val*frameU^b.val*frameA^c.val*frameB^d.val := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
  obtain ⟨a,b,c,d,he⟩ := frame_coverage x ((quotient_commutes_iff x U).mp hx)
  refine ⟨a,b,c,d,?_⟩
  simp only [frameZ,frameU,frameA,frameB,← map_pow,← map_mul]
  exact QuotientGroup.eq_iff_div_mem.mpr he

end QuaternionCentralProduct
