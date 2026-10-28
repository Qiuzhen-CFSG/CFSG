module

public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.PairAction
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms.Compatibility

/-!
# The actual star-pair stabilizer is Aut(M22)

The certified Mathieu relabelling sends star 0 to 1 and star 1 to 14.
An explicit word in the native Mathieu generators sends (1,14) to (0,9).
Conjugation by this word identifies the literal seed pair stabilizer with
the standard native pair stabilizer, whose action on native M22 is already
proved to give the full automorphism group.

Source: Aschbacher--Smith 16.1.5(9), printed p.1172, and H.13.1, p.395.
The transport word is found by breadth-first search on ordered pairs and
its two images are checked in Lean.
-/

@[expose] public section
noncomputable section
namespace Janko4.InvolutionCentralizers.Second
open Cardinality.QuotientCount.Image Sporadic.Mathieu
open scoped Pointwise

/-- A native Mathieu word carrying the actual pair (1,14) to (0,9). -/
def pairMover : M24 :=
  let genA : M24 := ⟨m24GeneratorA, m24GeneratorA_mem⟩
  let genB : M24 := ⟨m24GeneratorB, m24GeneratorB_mem⟩
  genB * genA * genB * genB * genA * genB * genB * genA * genB *
    genA * genB * genB * genA * genB * genA * genB * genB

private theorem pairMover_one : (pairMover : Equiv.Perm (Fin 24)) 1 = 0 := by
  decide +kernel
private theorem pairMover_fourteen : (pairMover : Equiv.Perm (Fin 24)) 14 = 9 := by
  decide +kernel

attribute [local irreducible] pairMover

/-- The marking from the certified star coordinates to the native M22 pair. -/
def pairMarking : Equiv.Perm (Fin 24) :=
  (pairMover : Equiv.Perm (Fin 24)) * StarOrderCertificate.relabel

private theorem mark_zero (p : Equiv.Perm (Fin 24)) :
    (p * StarOrderCertificate.relabel) 0 = p 1 := rfl
private theorem mark_one (p : Equiv.Perm (Fin 24)) :
    (p * StarOrderCertificate.relabel) 1 = p 14 := rfl

theorem pairMarking_zero : pairMarking 0 = 0 :=
  (mark_zero (pairMover : Equiv.Perm (Fin 24))).trans pairMover_one

theorem pairMarking_one : pairMarking 1 = 9 :=
  (mark_one (pairMover : Equiv.Perm (Fin 24))).trans pairMover_fourteen

/-- The certified M24 comparison followed by an actual inner conjugation. -/
def markedStarEquiv : StarGroup ≃* M24 :=
  starGroupEquivM24.trans (MulAut.conj pairMover)

private theorem conjugation_apply (u r p : Equiv.Perm (Fin 24)) (i : Fin 24) :
    (u * (r * p * r⁻¹) * u⁻¹) ((u * r) i) = (u * r) (p i) := by
  change u (r (p (r.symm (u.symm (u (r i)))))) = u (r (p i))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem markedStarEquiv_apply (p : StarGroup) (i : Fin 24) :
    (markedStarEquiv p : Equiv.Perm (Fin 24)) (pairMarking i) =
      pairMarking (p.val i) := by
  change ((pairMover : Equiv.Perm (Fin 24)) *
      (starGroupEquivM24 p : Equiv.Perm (Fin 24)) *
      (pairMover : Equiv.Perm (Fin 24))⁻¹) (pairMarking i) = _
  rw [starGroupEquivM24_apply]
  exact conjugation_apply (pairMover : Equiv.Perm (Fin 24))
    StarOrderCertificate.relabel p.val i

private theorem marking_mem_pair (i : Fin 24) :
    pairMarking i ∈ MathieuCode.m22Pair ↔ i ∈ starPair := by
  simp only [MathieuCode.m22Pair, starPair, Finset.mem_insert, Finset.mem_singleton]
  have h0 : pairMarking i = 0 ↔ i = 0 := by
    simpa only [pairMarking_zero] using (pairMarking.injective.eq_iff (a := i) (b := 0))
  have h1 : pairMarking i = 9 ↔ i = 1 := by
    simpa only [pairMarking_one] using (pairMarking.injective.eq_iff (a := i) (b := 1))
  rw [h0, h1]

/-- The marked comparison preserves precisely setwise pair stabilization. -/
theorem markedStarEquiv_mem_pair (p : StarGroup) :
    markedStarEquiv p ∈ MathieuCode.m22PairStabilizer ↔ p ∈ starPairStabilizer := by
  constructor
  · intro hp
    apply MulAction.mem_stabilizer_finset'.mpr
    intro i hi
    apply (marking_mem_pair _).mp
    change pairMarking (p.val i) ∈ _
    rw [← markedStarEquiv_apply]
    exact MulAction.mem_stabilizer_finset'.mp hp ((marking_mem_pair _).mpr hi)
  · intro hp
    apply MulAction.mem_stabilizer_finset'.mpr
    intro i hi
    obtain ⟨j, rfl⟩ := pairMarking.surjective i
    change (markedStarEquiv p : Equiv.Perm (Fin 24)) (pairMarking j) ∈ _
    rw [markedStarEquiv_apply]
    exact (marking_mem_pair _).mpr
      (MulAction.mem_stabilizer_finset'.mp hp ((marking_mem_pair _).mp hi))

/-- A genuine multiplicative equivalence between the two marked stabilizers. -/
def starPairEquivNative : starPairStabilizer ≃* MathieuCode.m22PairStabilizer where
  toFun p := ⟨markedStarEquiv p.val, (markedStarEquiv_mem_pair _).mpr p.property⟩
  invFun p := ⟨markedStarEquiv.symm p.val, (markedStarEquiv_mem_pair _).mp
    (by simpa only [markedStarEquiv.apply_symm_apply] using p.property)⟩
  left_inv p := Subtype.ext (markedStarEquiv.symm_apply_apply p.val)
  right_inv p := Subtype.ext (markedStarEquiv.apply_symm_apply p.val)
  map_mul' p q := Subtype.ext (map_mul markedStarEquiv p.val q.val)

/-- The actual pair action, followed by conjugation on the native M22 carrier. -/
def starPairEquivAutM22 : starPairStabilizer ≃* MulAut M22 :=
  starPairEquivNative.trans MathieuCode.m22PairStabilizerEquivAut

end Janko4.InvolutionCentralizers.Second
