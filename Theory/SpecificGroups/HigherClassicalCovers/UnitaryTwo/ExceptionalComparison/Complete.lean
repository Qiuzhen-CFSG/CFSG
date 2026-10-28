module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.PresentationBound
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.UnitaryOrder
import all Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison

/-!
# The completed unitary–symplectic comparison with its generators

The proved presentation and unitary bounds discharge the two inputs of the
exceptional comparison. Its equations on the two prescribed generators retain
the marking needed to compare outer involutions in the six-dimensional
orthogonal model. The internal import accesses only the existing assembly's
construction to prove these public equations, without changing its boundary.

Source: GLS3 §2.2 and §2.7; Aschbacher–Smith F.5.1, printed p.300.
-/

public noncomputable section

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo

open Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime
open ExceptionalComparison

/-- The literal special unitary group is the ternary projective symplectic group. -/
def specialEquivPSp : StandardSU ≃* PSp (ZMod 3) := by
  let := presentation_finite_card_le.1
  exact specialEquivPSp_of_bounds presentation_finite_card_le.2 UnitaryOrder.card_standardSU_le

/-- The exceptional comparison agrees with the prescribed presentation maps. -/
theorem specialEquivPSp_toSpecial (a : Presentation) :
    specialEquivPSp (toSpecial a) = toProjectiveSymplectic a := by
  let := presentation_finite_card_le.1
  have hc : Nat.card Presentation = 25920 :=
    (Nat.card_congr (presentationEquivPSp presentation_finite_card_le.2).toEquiv).trans
      card_projective_symplectic
  have hf : Function.Bijective toSpecial :=
    (toSpecial_injective presentation_finite_card_le.2).bijective_of_nat_card_le
      (by simpa only [hc] using UnitaryOrder.card_standardSU_le)
  change presentationEquivPSp presentation_finite_card_le.2
    ((MulEquiv.ofBijective toSpecial hf).symm
      ((MulEquiv.ofBijective toSpecial hf) a)) = toProjectiveSymplectic a
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- Both literal matrix generators keep their prescribed images. -/
theorem specialEquivPSp_generator (i : Fin 2) :
    specialEquivPSp (unitaryGenerator i) = projectiveGenerator i := by
  rw [← toSpecial_generator, specialEquivPSp_toSpecial, toProjectiveSymplectic_generator]

/-- The specified unitary presentation map is onto the literal matrix group. -/
theorem toSpecial_surjective : Function.Surjective toSpecial := by
  intro g
  obtain ⟨p,hp⟩ := toProjectiveSymplectic_surjective (specialEquivPSp g)
  exact ⟨p,specialEquivPSp.injective ((specialEquivPSp_toSpecial p).trans hp)⟩

/-- Equality on the two matched matrices determines homomorphisms from SU₄(2). -/
theorem special_hom_ext {G : Type*} [Group G] {f g : StandardSU →* G}
    (h : ∀ i, f (unitaryGenerator i) = g (unitaryGenerator i)) : f = g := by
  have he : f.comp toSpecial = g.comp toSpecial := by
    apply PresentedGroup.ext
    intro i
    simpa only [MonoidHom.comp_apply, toSpecial_generator] using h i
  apply MonoidHom.ext
  intro a
  obtain ⟨p,rfl⟩ := toSpecial_surjective a
  exact congrArg (fun k : Presentation →* G => k p) he

/-- The literal projective unitary carrier, with no remaining order premise. -/
def standardEquivPSp : StandardPSU ≃* PSp (ZMod 3) :=
  (specialProjectiveEquiv standardForm standard_field_card standard_conj).symm.trans specialEquivPSp

/-- Projectivization commutes with the completed exceptional comparison. -/
theorem standardEquivPSp_project (a : StandardSU) :
    standardEquivPSp
      (specialProjectiveEquiv standardForm standard_field_card standard_conj a) =
      specialEquivPSp a := by
  exact congrArg specialEquivPSp
    ((specialProjectiveEquiv standardForm standard_field_card standard_conj).symm_apply_apply a)

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo
