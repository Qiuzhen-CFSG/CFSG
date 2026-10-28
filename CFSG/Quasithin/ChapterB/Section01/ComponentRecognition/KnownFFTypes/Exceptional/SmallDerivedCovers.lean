module

public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.SpecificGroups.PSL2.EightCentralCovers

/-!
# Covering reductions for the three small derived catalogue rows

All maps start with the literal projection L → L/Z(L), followed by the
specified catalogue isomorphism. The PSL₂(8) covering calculation is fully
discharged by the scalar-root and cyclic-Sylow transfer proofs. Its small
Ree application retains the genuine matrix-commutator isomorphism as an
explicit input. The G₂(2)′ and Tits applications retain the kernels of their
actual universal projections as explicit inputs.

These are conditional assembly results, not completed identifications of
all three catalogue rows. The G₂ and Tits multiplier calculations and the
exceptional Ree isomorphism must be proved separately. None of these
covering arguments uses an FF hypothesis.

Source: Aschbacher–Smith B.1.13, printed pp.73–74, with the small derived
conventions in GLS III §2.2 and §2.5, Theorem 2.5.15, and the multiplier
calculations in §6.1. The symplectic row is handled separately by
`Exceptional.symplectic_derived_recognition` and is not altered here.
-/

public section

open Subgroup PerfectCentralCovering
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional

variable {L : Type*} [Group L] [Group.IsPerfect L]

/-- The original group is PSL₂(8) whenever its central quotient is PSL₂(8).
The whole multiplier computation is discharged; no core hypothesis is needed. -/
noncomputable def psl28Equiv (e : L ⧸ center L ≃* PSL(2, GaloisField 2 3)) :
    L ≃* PSL(2, GaloisField 2 3) :=
  Theory.SpecificGroups.PSL2Eight.coverEquiv (centralQuotientCover e)

@[simp] theorem psl28Equiv_apply
    (e : L ⧸ center L ≃* PSL(2, GaloisField 2 3)) (x : L) :
    psl28Equiv e x = e (QuotientGroup.mk x) := by
  simp only [psl28Equiv, Theory.SpecificGroups.PSL2Eight.coverEquiv_apply,
    centralQuotientCover_apply]

/-- Small Ree covering reduction along an actual exceptional isomorphism.
Equality of the two model orders is not a sufficient input. -/
noncomputable def reeDerivedEquivOfModelEquiv
    (r : commutator (Atlas.ReeG2.Model (ZMod 3) 0) ≃* PSL(2, GaloisField 2 3))
    (e : L ⧸ center L ≃* commutator (Atlas.ReeG2.Model (ZMod 3) 0)) :
    L ≃* PSL(2, GaloisField 2 3) := psl28Equiv (e.trans r)

@[simp] theorem reeDerivedEquivOfModelEquiv_apply
    (r : commutator (Atlas.ReeG2.Model (ZMod 3) 0) ≃* PSL(2, GaloisField 2 3))
    (e : L ⧸ center L ≃* commutator (Atlas.ReeG2.Model (ZMod 3) 0)) (x : L) :
    reeDerivedEquivOfModelEquiv r e x = r (e (QuotientGroup.mk x)) := by
  simp only [reeDerivedEquivOfModelEquiv, psl28Equiv_apply, MulEquiv.trans_apply]

/-- Consumer of the exact ternary commutator catalogue input. Only the
exceptional model isomorphism remains; the covering kernel is discharged. -/
theorem reeDerived_recognition_of_modelEquiv
    (r : commutator (Atlas.ReeG2.Model (ZMod 3) 0) ≃* PSL(2, GaloisField 2 3))
    (h : Nonempty (L ⧸ center L ≃* commutator (Atlas.ReeG2.Model (ZMod 3) 0))) :
    Nonempty (L ≃* PSL(2, GaloisField 2 3)) := by
  obtain ⟨e⟩ := h
  exact ⟨reeDerivedEquivOfModelEquiv r e⟩

/-- Consumer of the exact binary octonion commutator row, conditional on
its pending universal-kernel calculation. -/
theorem g2Derived_recognition_of_universalKernel
    (hm : (universalProjection (commutator (Atlas.G2.Model (ZMod 2)))).ker = ⊥)
    (h : Nonempty (L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  obtain ⟨e⟩ := h
  exact ⟨centralQuotientEquivOfUniversalKernelEqBot hm e⟩

/-- Consumer of the literal Parrott presentation row, conditional on
its pending universal-kernel calculation. -/
theorem tits_recognition_of_universalKernel
    (hm : (universalProjection Tits.ParrottGroup).ker = ⊥)
    (h : Nonempty (L ⧸ center L ≃* Tits.ParrottGroup)) :
    Nonempty (L ≃* Tits.ParrottGroup) := by
  obtain ⟨e⟩ := h
  exact ⟨centralQuotientEquivOfUniversalKernelEqBot hm e⟩

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional
