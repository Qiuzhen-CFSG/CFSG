module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.Models
public import Theory.AlgebraicGroup.Representations.Coinduction.RightQuotient
public import Mathlib.RepresentationTheory.FiniteIndex

/-!
# The induced binary adjoint module on the native 22 cosets

Central matrices act trivially on trace-zero endomorphisms by conjugation.
Thus the binary adjoint descends to the actual M22 point stabilizer. The
surjective central quotient gives equality of the two coinvariant relation
spaces, identifying induction along `pointSLMap` with subgroup induction.
Finite-index induction/coinduction and right-coset evaluation then give an
actual representation equivalence with 22 copies of the binary adjoint.
Consequently the original induction has dimension 352.

The coset marking sends the right coset of g to g⁻¹(0); the coordinate action
retains the stabilizer correction, rather than forgetting the local action.
No composition-factor degrees or simplicity assertions are proved here.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16, and
Aschbacher--Smith, Chapter K, printed pp.451--452 and 457. This supplies the
concrete induction model for the remaining filtration calculation.
-/

@[expose] public noncomputable section

open Representation Sporadic.Mathieu
open scoped MatrixGroups
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule

/-- Every element of the actual central kernel acts trivially on the adjoint. -/
theorem adjointBinary_center (g : Matrix.PSL3Four.SL) (hg : g ∈ Subgroup.center Matrix.PSL3Four.SL) :
    adjointBinary g = 1 := by
  have hscalar := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hg (0 : Fin 3)
  have hn (v : Fin 3 → Matrix.PSL3Four.F) :
      SL3.BinaryDefiningFactors.natural (RingHom.id Matrix.PSL3Four.F) g v =
        g.val 0 0 • v := by
    change Matrix.mulVec g.val v = _
    rw [← hscalar]
    simp
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  change SL3.BinaryDefiningFactors.natural (RingHom.id Matrix.PSL3Four.F) g
    (a.val (SL3.BinaryDefiningFactors.natural (RingHom.id Matrix.PSL3Four.F) g⁻¹ v)) = a.val v
  rw [hn, ← map_smul, ← hn]
  rw [Representation.self_inv_apply]

/-- Descent of the binary adjoint to the native zero stabilizer. -/
def pointAdjoint : Representation (ZMod 2)
    (MulAction.stabilizer M22 (0 : Fin 22)) Adjoint :=
  (QuotientGroup.lift (Subgroup.center Matrix.PSL3Four.SL) adjointBinary
    (fun g hg => adjointBinary_center g hg)).comp
    (MathieuCode.m22PointStabilizerEquiv 0).toMonoidHom

/-- Inflating the descended action recovers the original action exactly. -/
@[simp] theorem pointAdjoint_pointSL (g : Matrix.PSL3Four.SL) :
    pointAdjoint (pointSL g) = adjointBinary g := by
  simp [pointAdjoint, pointSL]
  rfl

/-- Surjectivity of the central quotient identifies the induction relations. -/
theorem inducedKernel_eq :
    Coinvariants.ker (Representation.tprod ((leftRegular (ZMod 2) M22).comp pointSLMap) adjointBinary) =
      Coinvariants.ker (Representation.tprod ((leftRegular (ZMod 2) M22).comp
        (MulAction.stabilizer M22 (0 : Fin 22)).subtype) pointAdjoint) := by
  unfold Coinvariants.ker
  congr 1
  ext x
  constructor
  · rintro ⟨⟨g, v⟩, rfl⟩
    refine ⟨(pointSL g, v), ?_⟩
    simp only [Representation.tprod_apply, MonoidHom.comp_apply, pointAdjoint_pointSL]
    rfl
  · rintro ⟨⟨g, v⟩, rfl⟩
    obtain ⟨s, rfl⟩ := pointSL_surjective g
    refine ⟨(s, v), ?_⟩
    simp only [Representation.tprod_apply, MonoidHom.comp_apply, pointAdjoint_pointSL]
    rfl

/-- The noninjective central-cover induction is subgroup induction. -/
def inducedPointEquiv : Representation.Equiv inducedAdjoint
    (Representation.ind (MulAction.stabilizer M22 (0 : Fin 22)).subtype pointAdjoint) where
  toLinearEquiv := Submodule.quotEquivOfEq _ _ inducedKernel_eq
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

/-- Right cosets of the native point stabilizer. -/
abbrev PointCosets := Quotient (QuotientGroup.rightRel
  (MulAction.stabilizer M22 (0 : Fin 22)))
/-- One binary adjoint fiber at each of the 22 right cosets. -/
abbrev CosetAdjoint := PointCosets → Adjoint

/-- The native M22 action, including its point-stabilizer correction. -/
def cosetAdjoint : Representation (ZMod 2) M22 CosetAdjoint :=
  Theory.AlgebraicGroup.Representation.coindRightQuotient
    (MulAction.stabilizer M22 (0 : Fin 22)) (Rep.of pointAdjoint)

/-- The exact action formula on right-coset coordinates. -/
theorem cosetAdjoint_apply (g : M22) (q : PointCosets) (v : CosetAdjoint) :
    cosetAdjoint g v q = pointAdjoint
      (Theory.AlgebraicGroup.Subgroup.rightCosetCorrection
        (MulAction.stabilizer M22 (0 : Fin 22)) (q.out * g))
      (v (Quotient.mk (QuotientGroup.rightRel
        (MulAction.stabilizer M22 (0 : Fin 22))) (q.out * g))) := rfl

/-- Evaluation on right-coset representatives is equivariant. -/
def coindCosetEquiv : Representation.Equiv
    (coind (MulAction.stabilizer M22 (0 : Fin 22)).subtype pointAdjoint) cosetAdjoint where
  toLinearEquiv := Theory.AlgebraicGroup.Representation.coindVEquivRightQuotientPi
    (MulAction.stabilizer M22 (0 : Fin 22)) (Rep.of pointAdjoint)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    let e := Theory.AlgebraicGroup.Representation.coindVEquivRightQuotientPi
      (MulAction.stabilizer M22 (0 : Fin 22)) (Rep.of pointAdjoint)
    change e ((coind _ _ g) v) = e ((coind _ _ g) (e.symm (e v)))
    exact congrArg (fun w : coindV (MulAction.stabilizer M22 (0 : Fin 22)).subtype
      pointAdjoint => e ((coind _ _ g) w)) (e.symm_apply_apply v).symm

/-- The actual induced representation equals the 22-coset representation. -/
def inducedCosetEquiv : Representation.Equiv inducedAdjoint cosetAdjoint := by
  classical
  exact inducedPointEquiv.trans
    ((Representation.equivOfIso (Rep.indCoindIso (Rep.of pointAdjoint))).trans coindCosetEquiv)

/-- Identify right cosets with the native point moved by the inverse. -/
def pointCosetsEquiv : PointCosets ≃ Fin 22 := by
  let : MulAction.IsPretransitive M22 (Fin 22) := m22_isPretransitive
  refine (QuotientGroup.quotientRightRelEquivQuotientLeftRel
    (MulAction.stabilizer M22 (0 : Fin 22))).trans
      (_root_.Equiv.ofBijective (MulAction.ofQuotientStabilizer M22 (0 : Fin 22))
        ⟨MulAction.injective_ofQuotientStabilizer _ _, ?_⟩)
  intro x
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M22 (0 : Fin 22) x
  exact ⟨QuotientGroup.mk g, hg⟩

/-- The right-coset convention corresponds to inverse action on points. -/
theorem pointCosetsEquiv_mk (g : M22) :
    pointCosetsEquiv (Quotient.mk (QuotientGroup.rightRel
      (MulAction.stabilizer M22 (0 : Fin 22))) g) = g⁻¹ • (0 : Fin 22) := rfl

/-- There are exactly 22 native right cosets. -/
theorem card_pointCosets : Nat.card PointCosets = 22 := by
  let : MulAction.IsPretransitive M22 (Fin 22) := m22_isPretransitive
  rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel
    (MulAction.stabilizer M22 (0 : Fin 22))), ← Subgroup.index_eq_card,
    MulAction.index_stabilizer_of_transitive]
  simp

/-- The coset model has binary dimension 22 times 16. -/
theorem finrank_cosetAdjoint : Module.finrank (ZMod 2) CosetAdjoint = 352 := by
  let : Fintype PointCosets := Fintype.ofFinite _
  let : FiniteDimensional (ZMod 2) Adjoint := FiniteDimensional.of_finrank_pos
    (by rw [finrank_adjoint]; decide)
  let : Module.Free (ZMod 2) Adjoint := Module.Free.of_divisionRing _ _
  rw [Module.finrank_pi_fintype]
  simp only [finrank_adjoint, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, card_pointCosets]

/-- Dimension of the original induction along the noninjective point map. -/
theorem finrank_inducedAdjoint : Module.finrank (ZMod 2) InducedAdjoint = 352 :=
  inducedCosetEquiv.toLinearEquiv.finrank_eq.trans finrank_cosetAdjoint

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule
