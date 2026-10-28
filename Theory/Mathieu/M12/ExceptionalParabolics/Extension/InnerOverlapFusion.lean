module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.CentralExtensions.Coordinates

/-!
# Inner-involution fusion through the actual outer Mathieu parabolics

The existing 128-element overlap coordinates have 28 inner square-one
elements, including the identity. Each reaches the eight inner elements
of the elementary Thompson sixteen by at most two local conjugations:
first in the second parabolic, then in the first. A 28-row certificate
checks the literal degree-24 permutation equations in the kernel. Both
intermediate and final elements remain in the actual overlap, so the two
commuting squares of a marked amalgam transport the entire fusion path.

Source: Aschbacher–Smith 14.2.22(1), printed p.989. The coordinates and
ATLAS attribution are inherited from Extension.Seeds. No ambient fusion
or amalgam recognition hypothesis enters this model calculation.
-/

public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.InnerOverlapFusion
open Subgroup OverlapExtensions SecondCoordinates
set_option maxRecDepth 100000

@[expose] def J : Subgroup Carrier := QuaternionSwapModel.A.map movement

def target (i : Fin 8) : Carrier :=
  movement (QuaternionSwapModel.MarkedCubic.bit 0) ^ (i.val % 2) *
  movement (QuaternionSwapModel.MarkedCubic.bit 1) ^ ((i.val / 2) % 2) *
  movement (QuaternionSwapModel.MarkedCubic.bit 2) ^ (i.val / 4)

theorem target_mem (i : Fin 8) : target i ∈ J := by
  apply J.mul_mem (J.mul_mem (J.pow_mem _ _) (J.pow_mem _ _)) (J.pow_mem _ _)
  all_goals exact mem_map_of_mem movement (QuaternionSwapModel.MarkedCubic.bit_mem_A _)

def targetPerm (i : Fin 8) : Equiv.Perm (Fin 24) :=
  (leftIPerm * rightIPerm) ^ (i.val % 2) *
  (leftJPerm * rightJPerm) ^ ((i.val / 2) % 2) * FirstParabolic.zPerm ^ (i.val / 4)

theorem target_val (i : Fin 8) : (target i).val = targetPerm i := by
  have hv : v.val = leftJPerm * rightJPerm := by decide +kernel
  simp only [target, Subgroup.coe_mul, Subgroup.coe_pow, movement_bit_zero,
    movement_bit_one,movement_bit_two,markedLeftI,markedRightI,hv,FirstParabolic.z_val]
  rfl

def leftActor (i : Fin 3) : firstParabolic :=
  ![1,Endpoint.generator 3,Endpoint.generator 3 * Endpoint.generator 1] i

def rightActor (i : Fin 3) : secondParabolic :=
  ![1,⟨secondActor,secondActor_mem_secondParabolic⟩,
    ⟨secondActor,secondActor_mem_secondParabolic⟩ *
      ⟨(Overlap.generator 0).val,(Overlap.generator 0).property.2⟩] i

def leftPerm (i : Fin 3) : Equiv.Perm (Fin 24) :=
  ![1,Endpoint.cubicPerm,Endpoint.cubicPerm * swapPerm] i

def rightPerm (i : Fin 3) : Equiv.Perm (Fin 24) :=
  ![1,actorPerm⁻¹,actorPerm⁻¹ * FirstParabolic.leftIPerm] i

theorem leftActor_val (i : Fin 3) : (leftActor i).val.val = leftPerm i := by
  fin_cases i
  · rfl
  · exact Endpoint.cubic_val
  · change cubicActor.val * swap.val = Endpoint.cubicPerm * swapPerm
    rw [Endpoint.cubic_val]
    rfl

theorem rightActor_val (i : Fin 3) : (rightActor i).val.val = rightPerm i := by
  fin_cases i
  · rfl
  · rfl
  · change actor.val⁻¹ * leftI.val = actorPerm⁻¹ * FirstParabolic.leftIPerm
    rw [FirstParabolic.leftI_val]
    rfl

private def perm (i : Fin 128) : Equiv.Perm (Fin 24) :=
  FiniteWords.evaluate Overlap.generatorPerm (Data.overlapWords i)

private def sourceIndex : Fin 28 → Fin 128 := ![0,3,4,13,16,28,46,62,73,83,85,91,96,97,98,102,105,106,107,108,110,111,112,116,117,124,125,126]

private def middleIndex : Fin 28 → Fin 128 := ![0,85,4,96,96,28,85,83,73,83,85,91,96,97,98,91,105,91,107,108,110,111,112,116,117,124,125,83]

private def rightIndex : Fin 28 → Fin 3 := ![0,2,0,2,1,0,1,1,0,0,0,0,0,0,0,1,0,2,0,0,0,0,0,0,0,0,0,2]

private def leftIndex : Fin 28 → Fin 3 := ![0,1,0,2,2,0,1,1,0,1,1,2,2,0,0,2,1,2,2,2,1,2,2,1,1,0,0,1]

private def endIndex : Fin 28 → Fin 8 := ![0,6,4,2,2,1,6,2,5,2,6,6,2,7,3,6,3,6,7,3,7,1,5,1,5,6,2,2]

private theorem coverage : ∀ i : Fin 128,
    perm i ^ 2 = 1 →
    (∃ j : Fin 12, perm i (blockLabel 0) = blockLabel j) →
    ∃ k : Fin 28, i = sourceIndex k := by
  decide +kernel

private theorem right_identity : ∀ k : Fin 28,
    rightPerm (rightIndex k) * perm (sourceIndex k) * (rightPerm (rightIndex k))⁻¹ =
      perm (middleIndex k) := by
  decide +kernel

private theorem left_identity : ∀ k : Fin 28,
    leftPerm (leftIndex k) * perm (middleIndex k) * (leftPerm (leftIndex k))⁻¹ =
      targetPerm (endIndex k) := by
  decide +kernel

/-- Two local conjugations carry each inner square-one element of the whole
Sylow overlap into its actual elementary Thompson sixteen. -/
theorem inner_fusion (x : overlap) (hs : (x : Carrier)^2 = 1) (hx : (x : Carrier) ∈ inner) :
    ∃ y z : overlap, ∃ a : secondParabolic, ∃ b : firstParabolic,
      (y : Carrier) ∈ J ∧ (y : Carrier) ∈ inner ∧
      (a : Carrier) * x * (a : Carrier)⁻¹ = z ∧
      (b : Carrier) * z * (b : Carrier)⁻¹ = y := by
  obtain ⟨i,rfl⟩ := Overlap.element_surjective x
  have hp : perm i ^ 2 = 1 := by
    have h := congrArg Subtype.val hs
    simpa only [Subgroup.coe_pow,Subgroup.coe_one,Overlap.element_val,perm] using h
  have hb : ∃ j : Fin 12, perm i (blockLabel 0) = blockLabel j := by
    refine ⟨(blockRestriction ⟨(Overlap.element i : Carrier),hx⟩).val 0,?_⟩
    simpa only [Overlap.element_val,perm] using blockRestriction_spec
      ⟨(Overlap.element i : Carrier),hx⟩ 0
  obtain ⟨k,rfl⟩ := coverage i hp hb
  have h1 : (rightActor (rightIndex k) : Carrier) * (Overlap.element (sourceIndex k) : Carrier) *
      (rightActor (rightIndex k) : Carrier)⁻¹ = (Overlap.element (middleIndex k) : Carrier) := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,rightActor_val,Overlap.element_val,perm]
      using right_identity k
  have h2 : (leftActor (leftIndex k) : Carrier) * (Overlap.element (middleIndex k) : Carrier) *
      (leftActor (leftIndex k) : Carrier)⁻¹ = target (endIndex k) := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,leftActor_val,Overlap.element_val,perm,target_val]
      using left_identity k
  have hJle : J ≤ overlap := VerifiedPair.secondGeometry.toGeometry.A_le
  have hn : inner.Normal := normal_of_index_eq_two inner_index
  refine ⟨⟨target (endIndex k),hJle (target_mem _)⟩,Overlap.element (middleIndex k),
    rightActor (rightIndex k),leftActor (leftIndex k),target_mem _,?_,h1,h2⟩
  change target (endIndex k) ∈ inner
  rw [←h2,←h1]
  exact hn.conj_mem _ (hn.conj_mem _ hx _) _
end Sporadic.Mathieu.M12ExceptionalExtension.InnerOverlapFusion
