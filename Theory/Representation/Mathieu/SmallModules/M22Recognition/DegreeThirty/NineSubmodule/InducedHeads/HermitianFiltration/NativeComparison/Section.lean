module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.Coordinates
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.Transversal

/-!
# Explicit section coordinates for the Hermitian induction

Evaluate the coinduced functions on the certified native transversal. The
inverse uses the stabilizer correction, proving an equivariant change from
`Quotient.out` to that transversal. Right multiplication by `g` reads the block
at `g⁻¹ • i`, with correction `t i * g * (t (g⁻¹ • i))⁻¹`.

The same section is used by the binary adjoint calculation; only its proved
group identities are reused here. No numerical fiber matrices are assumed in
this coordinate change.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16, and
Aschbacher--Smith, Chapter K, printed pp.451--452,457.
-/

@[expose] public noncomputable section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison

open SixteenSubmodule.GeneratorMatrices

abbrev PointSpace := Fin 22 → Models.HermitianSpace

/-- The left stabilizer factor of a native element in the explicit section. -/
def sectionCorrection (g : M22) : Models.pointGroup :=
  ⟨g * (transversal (g⁻¹ • (0 : Fin 22)))⁻¹, by
    change (g * (transversal (g⁻¹ • (0 : Fin 22)))⁻¹) • (0 : Fin 22) = 0
    rw [mul_smul, transversal_inv_zero, smul_inv_smul]⟩

theorem sectionCorrection_mul_transversal (g : M22) :
    (sectionCorrection g).val * transversal (g⁻¹ • (0 : Fin 22)) = g := by
  simp [sectionCorrection, mul_assoc]

theorem sectionCorrection_transversal (i : Fin 22) :
    sectionCorrection (transversal i) = 1 := by
  apply Subtype.ext
  simp [sectionCorrection, transversal_inv_zero]

private theorem stabilizer_inverse_zero (s : Models.pointGroup) :
    (s.val)⁻¹ • (0 : Fin 22) = 0 := s⁻¹.property

private theorem sectionCorrection_left (s : Models.pointGroup) (g : M22) :
    sectionCorrection (s.val * g) = s * sectionCorrection g := by
  apply Subtype.ext
  simp [sectionCorrection, mul_inv_rev, mul_smul, stabilizer_inverse_zero, mul_assoc]

/-- Evaluation at the finite section is a genuine linear equivalence. -/
def coindSectionEquiv :
    coindV Models.pointGroup.subtype (Models.pointAction false) ≃ₗ[ZMod 2] PointSpace where
  toFun f i := f.val (transversal i)
  invFun v := ⟨fun g => Models.pointAction false (sectionCorrection g)
    (v (g⁻¹ • (0 : Fin 22))), by
    intro s g
    change Models.pointAction false (sectionCorrection (s.val * g))
      (v ((s.val * g)⁻¹ • (0 : Fin 22))) = _
    rw [sectionCorrection_left, mul_inv_rev, mul_smul, stabilizer_inverse_zero,
      map_mul, Module.End.mul_apply]⟩
  left_inv f := by
    apply Subtype.ext
    funext g
    change Models.pointAction false (sectionCorrection g)
      (f.val (transversal (g⁻¹ • (0 : Fin 22)))) = f.val g
    rw [← f.property]
    change f.val ((sectionCorrection g).val * transversal (g⁻¹ • (0 : Fin 22))) = _
    rw [sectionCorrection_mul_transversal]
  right_inv v := by
    funext i
    change Models.pointAction false (sectionCorrection (transversal i))
      (v ((transversal i)⁻¹ • (0 : Fin 22))) = v i
    rw [sectionCorrection_transversal, transversal_inv_zero, map_one]
    rfl
  map_add' f h := rfl
  map_smul' c f := rfl

theorem coindSectionEquiv_action (g : M22)
    (f : coindV Models.pointGroup.subtype (Models.pointAction false)) (i : Fin 22) :
    coindSectionEquiv (coind _ (Models.pointAction false) g f) i =
      Models.pointAction false (correction g i) (coindSectionEquiv f (g⁻¹ • i)) := by
  change f.val (transversal i * g) =
    Models.pointAction false (correction g i) (f.val (transversal (g⁻¹ • i)))
  rw [← f.property]
  change f.val (transversal i * g) = f.val ((correction g i).val * transversal (g⁻¹ • i))
  rw [correction_mul_transversal]

/-- The actual Hermitian induction in native point-indexed coordinates. -/
def sectionAction : Representation (ZMod 2) M22 PointSpace :=
  coindSectionEquiv.conjRingEquiv.toMonoidHom.comp (coind _ (Models.pointAction false))

def coindSectionRepEquiv :
    (coind Models.pointGroup.subtype (Models.pointAction false)).Equiv sectionAction where
  toLinearEquiv := coindSectionEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change coindSectionEquiv (coind _ (Models.pointAction false) g v) =
      coindSectionEquiv (coind _ (Models.pointAction false) g
        (coindSectionEquiv.symm (coindSectionEquiv v)))
    rw [coindSectionEquiv.symm_apply_apply]

theorem sectionAction_apply (g : M22) (v : PointSpace) (i : Fin 22) :
    sectionAction g v i = Models.pointAction false (correction g i) (v (g⁻¹ • i)) := by
  change coindSectionEquiv
    (coind _ (Models.pointAction false) g (coindSectionEquiv.symm v)) i = _
  rw [coindSectionEquiv_action, coindSectionEquiv.apply_symm_apply]

/-- Replace the noncomputably chosen quotient representatives equivariantly. -/
def coordinateSectionEquiv : (coordinateAction false).Equiv sectionAction :=
  (coindCoordinateEquiv false).symm.trans coindSectionRepEquiv

/-- The source block uses the inverse native generator, not its forward action. -/
theorem sectionAction_generator (j : Fin 2) (v : PointSpace) (i : Fin 22) :
    sectionAction (generator j) v i =
      Models.pointAction false (generatorCorrection j i) (v (generatorPoint j i)) := by
  rw [sectionAction_apply, generatorPoint_eq]
  rfl

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison
