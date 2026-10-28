module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.NativeSource
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Linear

/-!
# Transport of native incident dual vectors

Conjugate both the actual neighboring radius group and its displacement.
The graph action uses the inverse of the conjugating element. The natural
and inverse-transpose actions preserve evaluation, so native incidence is
preserved. Surjectivity of the marked quotient and transitivity of the
literal binary dual action then reduce uniform realization to one nonzero
native lift. The imported DistanceFour result is only the matrix orbit
calculation; no distance-four or later source hypothesis is used.

Source: Meierfrankenfeld--Stellmacher (1993), the generation display before
(4.3.2)(4), printed p.884.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
variable {M : Type*} [Group M] {R : Subgroup M}

private theorem evaluation_invariant (g : SL) (v u : Fin 3 → ZMod 2) :
    dotProduct ((g⁻¹).val.transpose.mulVec v) (g.val.mulVec u) = dotProduct v u := by
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
  simp

/-- Transport retains the literal neighboring group, marking and annihilator. -/
noncomputable def NativeNeighborLift.conjugate {c : Vertex R}
    {o : OppositeSectionAt c} {hC : Vcirc R c ≤ stabilizer R c} {v : Space}
    (lift : NativeNeighborLift o hC v) (g : stabilizer R c) :
    NativeNeighborLift o hC
      (Multiplicative.ofAdd (((markedProjection o g)⁻¹).val.transpose.mulVec v.toAdd)) := by
  let y : Vcirc R c := ⟨g * (lift.vector : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
    le_normalizer_iff.mp (Vcirc_normalized c) g g.property _ lift.vector.property⟩
  have hg : act R (g : FreeAmalgam R)⁻¹ c = c := (stabilizer R c).inv_mem g.property
  refine {
    neighbor := act R (g : FreeAmalgam R)⁻¹ lift.neighbor
    adjacent := ?_
    vector := y
    in_neighbor := ?_
    coordinates := ?_
    annihilates := ?_ }
  · simpa only [hg] using
      (adjacent_act_iff R (g : FreeAmalgam R)⁻¹ c lift.neighbor).mpr lift.adjacent
  · rw [V_act]
    exact ⟨lift.vector, lift.in_neighbor, by simp only [inv_inv]; rfl⟩
  · apply Multiplicative.toAdd.injective
    rw [movingCoordinates_conjugation o hC g lift.vector y rfl, lift.coordinates]
    rfl
  · intro d hd
    have he := FirstPairing.edgeDisplacement_act (g : FreeAmalgam R)⁻¹ c lift.neighbor
    rw [hg, inv_inv] at he
    rw [he] at hd
    obtain ⟨e, heD, he⟩ := hd
    have heU : e ∈ U R c := by
      have hh := le_normalizer_iff.mp (U_normalized c) (g : FreeAmalgam R)⁻¹
        ((stabilizer R c).inv_mem g.property) d d.property
      rw [← he] at hh
      simpa [MulAut.conj_apply, mul_assoc] using hh
    let eU : U R c := ⟨e, heU⟩
    have hdcoord := naturalEquiv_conjugation o g eU d he.symm
    change dotProduct (((markedProjection o g)⁻¹).val.transpose.mulVec v.toAdd)
      (naturalEquiv o d).toAdd = 0
    rw [hdcoord, evaluation_invariant]
    exact lift.annihilates eU heD

/-- One nonzero native lift supplies every nonzero dual coordinate by the
actual surjective marked action. The seed remains a geometric obligation. -/
theorem nativeNeighborLifts_of_one {c : Vertex R} (o : OppositeSectionAt c)
    (hC : Vcirc R c ≤ stabilizer R c) {v : Space} (hv : v ≠ 1)
    (lift : NativeNeighborLift o hC v) : NativeNeighborLifts o hC := by
  intro w hw
  obtain ⟨a, ha⟩ := DistanceFour.Linear.dual_orbit
    (show v.toAdd ≠ 0 from hv) (show w.toAdd ≠ 0 from hw)
  obtain ⟨g, hg⟩ := o.surjective (o.naturalU.marking.symm a)
  have hmark : markedProjection o g = a := by
    change o.naturalU.marking (o.projection g) = a
    rw [hg, o.naturalU.marking.apply_symm_apply]
  have he : Multiplicative.ofAdd
      (((markedProjection o g)⁻¹).val.transpose.mulVec v.toAdd) = w := by
    rw [hmark]
    exact congrArg Multiplicative.ofAdd ha
  exact he ▸ Nonempty.intro (lift.conjugate g)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
