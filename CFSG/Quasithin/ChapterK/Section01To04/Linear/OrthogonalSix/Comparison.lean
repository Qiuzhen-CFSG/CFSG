module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.Representation.BinaryPermutationAlternatingActions

/-!
# The exterior-square and deleted-permutation comparison in K.3.2.2

The quotient of the even code by its constant line is identified with the
image of the even code in the deleted full module. This intertwines coordinate
permutations. Composing with the checked split-form comparison identifies the
actual six-coordinate exterior square of SL₄(2) with the natural A₈ action.

The quadratic comparison is from Gerald Höhn and ATLAS contributors, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917, ported in
`Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8`; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff for attribution and license.
Source: Aschbacher–Smith, K.3.2.2, printed p.455/PDF p.466.
-/

public noncomputable section
open BinaryPermutation
open Atlas.Order20160A8
namespace CFSG.Quasithin.ChapterK.Linear.OrthogonalSix

private def evenToNatural : DeletedEight.evenCode →ₗ[ZMod 2] natural (Fin 8) :=
  coreToNatural (Fin 8)

private theorem evenToNatural_surjective : Function.Surjective evenToNatural := by
  rintro ⟨_, v, hv, rfl⟩
  exact ⟨⟨v, hv⟩, rfl⟩

private theorem evenToNatural_ker : evenToNatural.ker = DeletedEight.constants := by
  ext v
  change coreToNatural (Fin 8) v = 0 ↔ v ∈ Submodule.span (ZMod 2) {DeletedEight.oneWord}
  rw [Subtype.ext_iff]
  change (Submodule.Quotient.mk v.val : Deleted (Fin 8)) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  simp only [constants, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, congrArg Subtype.val ha⟩

/-- Identifies the quotient of the even code with the image of the even code
in the quotient of the full permutation module. -/
def deletedEightEquivNatural : DeletedEight.W ≃ₗ[ZMod 2] natural (Fin 8) :=
  (Submodule.quotEquivOfEq _ _ evenToNatural_ker.symm).trans
    (evenToNatural.quotKerEquivOfSurjective evenToNatural_surjective)

@[simp] theorem deletedEightEquivNatural_mk (v : DeletedEight.evenCode) :
    deletedEightEquivNatural (Submodule.Quotient.mk v) = coreToNatural (Fin 8) v := by
  simp only [deletedEightEquivNatural, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

/-- The quotient comparison uses the same inverse-coordinate left action. -/
theorem deletedEightEquivNatural_intertwines (p : Equiv.Perm (Fin 8)) (w : DeletedEight.W) :
    deletedEightEquivNatural (DeletedEight.quotientPerm p w) =
      naturalRepresentation (Fin 8) p (deletedEightEquivNatural w) := by
  induction w using Submodule.Quotient.induction_on with
  | H v =>
    change deletedEightEquivNatural (Submodule.Quotient.mk (DeletedEight.evenPerm p v)) = _
    rw [deletedEightEquivNatural_mk, deletedEightEquivNatural_mk]
    rfl

/-- The marked SL₄(2) ≃ A₈ equivalence supplied by the actual quadratic actions. -/
def sl4EquivAlternating : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) ≃*
    alternatingGroup (Fin 8) :=
  sl4TwoEquivPSL.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8

/-- Actual six-dimensional exterior-square coordinates on the natural A₈ module. -/
def exteriorEquivNatural : Bivectors.Six (ZMod 2) ≃ₗ[ZMod 2] natural (Fin 8) :=
  Exterior.coordinates.trans (DeletedEight.splitEquiv.trans deletedEightEquivNatural)

/-- K.3.2.2's module comparison, beyond the abstract exceptional isomorphism. -/
theorem exteriorEquivNatural_intertwines
    (g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) (w : Bivectors.Six (ZMod 2)) :
    exteriorEquivNatural (Bivectors.exteriorMap g.val w) =
      alternatingNaturalRepresentation (Fin 8) (sl4EquivAlternating g) (exteriorEquivNatural w) := by
  have h := congrArg (fun k : O_DPlus 3 (ZMod 2) => k.val (Exterior.coordinates w))
    (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8_orthogonal g)
  change DeletedEight.splitEquiv.symm
    (DeletedEight.quotientPerm (sl4EquivAlternating g).val
      (DeletedEight.splitEquiv (Exterior.coordinates w))) =
    Exterior.coordinates (Bivectors.exteriorMap g.val (Exterior.coordinates.symm (Exterior.coordinates w))) at h
  rw [LinearEquiv.symm_apply_apply] at h
  have h' := congrArg DeletedEight.splitEquiv h
  simp only [LinearEquiv.apply_symm_apply] at h'
  change deletedEightEquivNatural (DeletedEight.splitEquiv
    (Exterior.coordinates (Bivectors.exteriorMap g.val w))) = _
  rw [← h', deletedEightEquivNatural_intertwines]
  rfl

end CFSG.Quasithin.ChapterK.Linear.OrthogonalSix
