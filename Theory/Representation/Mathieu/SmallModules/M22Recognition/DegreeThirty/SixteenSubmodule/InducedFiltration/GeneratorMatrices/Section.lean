module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.Transversal

/-!
# Replacing the chosen coset representatives by a finite explicit section

Evaluation of a coinduced function at the certified representatives is a linear
isomorphism. Its inverse uses the actual point-stabilizer representation and the
unique stabilizer correction. This proves the sparse block action with the exact
right-coset convention, and gives representation equivalences from both the
published coset model and the literal induced binary adjoint.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16. This is the
coordinate change needed before computing the local adjoint matrices; it does
not supply those matrices or a factor filtration.
-/

@[expose] public section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.GeneratorMatrices

/-- Decompose an arbitrary element using the explicit right-coset section. -/
noncomputable def sectionCorrection (g : M22) :
    MulAction.stabilizer M22 (0 : Fin 22) :=
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

private theorem stabilizer_inverse_zero (s : MulAction.stabilizer M22 (0 : Fin 22)) :
    (s.val)⁻¹ • (0 : Fin 22) = 0 := by
  exact s⁻¹.property

private theorem sectionCorrection_left (s : MulAction.stabilizer M22 (0 : Fin 22))
    (g : M22) : sectionCorrection (s.val * g) = s * sectionCorrection g := by
  apply Subtype.ext
  simp [sectionCorrection, mul_inv_rev, mul_smul, stabilizer_inverse_zero, mul_assoc]

/-- An adjoint fiber at each native point. -/
abbrev PointAdjoint := Fin 22 → Adjoint

/-- Evaluate coinduced functions at the explicit representatives. -/
noncomputable def coindSectionEquiv :
    coindV (MulAction.stabilizer M22 (0 : Fin 22)).subtype pointAdjoint ≃ₗ[ZMod 2]
      PointAdjoint where
  toFun f i := f.val (transversal i)
  invFun v := ⟨fun g => pointAdjoint (sectionCorrection g) (v (g⁻¹ • (0 : Fin 22))), by
    intro s g
    change pointAdjoint (sectionCorrection (s.val * g))
      (v ((s.val * g)⁻¹ • (0 : Fin 22))) = _
    rw [sectionCorrection_left, mul_inv_rev, mul_smul, stabilizer_inverse_zero,
      map_mul, Module.End.mul_apply]⟩
  left_inv f := by
    apply Subtype.ext
    funext g
    change pointAdjoint (sectionCorrection g)
      (f.val (transversal (g⁻¹ • (0 : Fin 22)))) = f.val g
    rw [← f.property]
    change f.val ((sectionCorrection g).val * transversal (g⁻¹ • (0 : Fin 22))) = _
    rw [sectionCorrection_mul_transversal]
  right_inv v := by
    funext i
    change pointAdjoint (sectionCorrection (transversal i))
      (v ((transversal i)⁻¹ • (0 : Fin 22))) = v i
    rw [sectionCorrection_transversal, transversal_inv_zero, map_one]
    rfl
  map_add' f h := rfl
  map_smul' c f := rfl

theorem coindSectionEquiv_action (g : M22)
    (f : coindV (MulAction.stabilizer M22 (0 : Fin 22)).subtype pointAdjoint)
    (i : Fin 22) :
    coindSectionEquiv (coind _ pointAdjoint g f) i =
      pointAdjoint (correction g i) (coindSectionEquiv f (g⁻¹ • i)) := by
  change f.val (transversal i * g) =
    pointAdjoint (correction g i) (f.val (transversal (g⁻¹ • i)))
  rw [← f.property]
  change f.val (transversal i * g) = f.val ((correction g i).val * transversal (g⁻¹ • i))
  rw [correction_mul_transversal]

/-- The literal coinduced action transported to the explicit section. -/
noncomputable def sectionAdjoint : Representation (ZMod 2) M22 PointAdjoint :=
  coindSectionEquiv.conjRingEquiv.toMonoidHom.comp (coind _ pointAdjoint)

/-- Section evaluation intertwines the full native M22 action. -/
noncomputable def coindSectionRepEquiv : Representation.Equiv
    (coind (MulAction.stabilizer M22 (0 : Fin 22)).subtype pointAdjoint) sectionAdjoint where
  toLinearEquiv := coindSectionEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change coindSectionEquiv (coind _ pointAdjoint g v) =
      coindSectionEquiv (coind _ pointAdjoint g (coindSectionEquiv.symm (coindSectionEquiv v)))
    rw [coindSectionEquiv.symm_apply_apply]

theorem sectionAdjoint_apply (g : M22) (v : PointAdjoint) (i : Fin 22) :
    sectionAdjoint g v i = pointAdjoint (correction g i) (v (g⁻¹ • i)) := by
  change coindSectionEquiv (coind _ pointAdjoint g (coindSectionEquiv.symm v)) i = _
  rw [coindSectionEquiv_action, coindSectionEquiv.apply_symm_apply]

/-- Change from the published chosen representatives to the explicit section. -/
noncomputable def cosetSectionEquiv : Representation.Equiv cosetAdjoint sectionAdjoint :=
  coindCosetEquiv.symm.trans coindSectionRepEquiv

/-- Coordinates for the literal induction along the central-cover point map. -/
noncomputable def inducedSectionEquiv : Representation.Equiv inducedAdjoint sectionAdjoint :=
  inducedCosetEquiv.trans cosetSectionEquiv

theorem sectionAdjoint_generator (k : Fin 2) (v : PointAdjoint) (i : Fin 22) :
    sectionAdjoint (generator k) v i =
      pointAdjoint (generatorCorrection k i) (v (generatorPoint k i)) := by
  rw [sectionAdjoint_apply, generatorPoint_eq]
  rfl


end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.GeneratorMatrices
