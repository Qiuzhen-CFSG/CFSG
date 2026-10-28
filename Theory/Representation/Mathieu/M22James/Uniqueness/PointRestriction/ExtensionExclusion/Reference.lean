module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ClassicalExtension.Multiplication
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue

/-!
# The diagonal nonzero catalogue parameters give the reference module

In the natural-by-dual catalogue coordinates the off-diagonal block acts
after Frobenius on the second summand. Squaring that summand converts the
parameter (1,1) to the reference field-linear action. Scaling the first
summand identifies every (p,p), p nonzero, with the same reference action.
These are actual whole-module equivalences, retaining every extension block.

Source context: James (1973), Lemma 8.3, and Aschbacher–Smith H.12.1(1),
printed pp.393–394. Exclusion of the other catalogue parameters belongs to
the full-group extension argument.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.ExtensionExclusion

open Matrix PointModel
open Representation.SL3FourLocalCatalogue
open Representation.SL3FourLocalCatalogue.ExtensionCoordinates

/-- The catalogue entry with the two equal, specified mixed parameters. -/
def referenceEntry (p : Reference.F) : CatalogueEntry := ⟨.natural, .dual, (p, p)⟩

private lemma coupling_eq (g : Reference.SL) :
    Reference.coupling g = symmetricMatrix g + dualSymmetricMatrix g := by
  have hp (a : Matrix (Fin 3) (Fin 3) Reference.F) (i j : Fin 3) :
      Reference.crossProducts a i j = a j (i+1) * a j (i+2) := by
    fin_cases i
    · rfl
    · exact mul_comm _ _
    · rfl
  have hs : symmetricMatrix g = (Reference.crossProducts g.val).transpose.map
      (fun x => x^2) := by
    funext i j
    exact congrArg (fun x : Reference.F => x^2) (hp g.val j i).symm
  have hd : dualSymmetricMatrix g = Reference.crossProducts (g⁻¹).val := by
    funext i j
    change (((g⁻¹).val j (i+1) * (g⁻¹).val j (i+2)) ^ 2) ^ 2 = _
    rw [← pow_mul, show 2 * 2 = 4 by rfl, Representation.SL2FourNatural.pow_four]
    exact (hp (g⁻¹).val i j).symm
  rw [hs, hd]
  exact add_comm _ _

private lemma squareVector_matrix (m : Matrix (Fin 3) (Fin 3) Reference.F) (v : W) :
    squareVector ((m.map (fun x => x^2)) *ᵥ v) = m *ᵥ squareVector v := by
  have hm : (m.map (fun x => x^2)).map
      Representation.SL2FourNatural.fieldFrobenius = m := by
    funext i j
    exact Representation.SL2FourNatural.fieldFrobenius_involutive _
  funext j
  change Representation.SL2FourNatural.fieldFrobenius
    (((m.map (fun x => x^2)) *ᵥ v) j) = _
  have h := Representation.SL2FourNatural.fieldFrobenius.toRingHom.map_mulVec
    (m.map (fun x => x^2)) v j
  change _ = (((m.map (fun x => x^2)).map
    Representation.SL2FourNatural.fieldFrobenius) *ᵥ squareVector v) j at h
  rw [hm] at h
  exact h

private lemma mixedValue_diagonal (p : Reference.F) (g : Reference.SL) (v : W) :
    mixedValue p p g v = p • (Reference.coupling g *ᵥ squareVector v) := by
  change (p • symmetricMatrix g + p • dualSymmetricMatrix g) *ᵥ squareVector v = _
  rw [← smul_add, ← coupling_eq, Matrix.smul_mulVec]

/-- The reference whole-module action is equivalent to every nonzero diagonal
mixed parameter. The second block is changed by binary-linear Frobenius. -/
def referenceEquivEntry (p : Reference.F) (hp : p ≠ 0) :
    Reference.binaryRepresentation.Equiv (catalogueRepresentation (referenceEntry p)) := by
  let e : Reference.V ≃ₗ[ZMod 2] (W × W) :=
    ((LinearEquiv.smulOfNeZero Reference.F W p hp).restrictScalars (ZMod 2)).prodCongr
      squareVector
  exact Representation.Equiv.mk e (by
    intro g
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · change p • (g.val *ᵥ v.1 + Reference.coupling g *ᵥ v.2) =
      g.val *ᵥ (p • v.1) + mixedValue p p g (squareVector v.2)
      rw [mixedValue_diagonal]
      have hs : squareVector (squareVector v.2) = v.2 := squareVector.symm_apply_apply _
      rw [hs, smul_add, Matrix.mulVec_smul]
    · exact squareVector_matrix (g⁻¹).val.transpose v.2)

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.ExtensionExclusion
