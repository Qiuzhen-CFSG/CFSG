module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Actions
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Projective
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Natural and dual coordinates for the G.2.5 point maps

The actor is the literal starred image of L, identified with SL₃(F) by
the source hypothesis. Its natural and contragredient actions are genuine
representations. Right conjugation of the marked point uses the inverse
actor, matching `Setup.conjugate`. The proposed dual mark is exactly the
annihilator of the first two natural marked lines.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.5, printed pp.335–336.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
open Projective
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)

include d in
/-- Characteristic two follows from the source field cardinality. -/
theorem field_char_two : CharP F 2 := by
  let := Fintype.ofFinite F
  apply ringChar.of_eq
  apply FiniteField.even_card_iff_char_two.mpr
  rw [← Nat.card_eq_fintype_card, d.field_card]
  exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (Nat.ne_of_gt d.exponent_pos))

/-- The natural action of the exact starred subgroup. -/
def naturalAction : Representation F (D.star D.L) (Fin 3 → F) :=
  (Representation.specialLinearNatural 3).comp d.model.toMonoidHom

/-- The dual is taken over F, before forgetting to a binary module. -/
def dualAction : Representation F (D.star D.L) (Module.Dual F (Fin 3 → F)) :=
  (naturalAction d).dual

/-- The literal first point in natural coordinates. -/
def naturalPoint : Point F (Fin 3 → F) := ⟨d.point, d.point_dimension⟩

/-- The natural action is marked by the source's actual model, with no
additional representation-identification premise. -/
def naturalMarking : NaturalMarking (naturalAction d) where
  groupEquiv := d.model
  coordinates := LinearEquiv.refl F (Fin 3 → F)
  equivariant := fun _ _ => rfl

/-- The natural coordinates of the first conjugate point use g⁻¹. -/
def conjugatePoint (x : D.L) : Point F (Fin 3 → F) :=
  ⟨d.point.map (naturalAction d ((starProjection D x)⁻¹)), by
    let e := LinearEquiv.ofBijective (naturalAction d ((starProjection D x)⁻¹))
      ((naturalAction d).apply_bijective _)
    exact (e.finrank_map_eq d.point).trans d.point_dimension⟩

/-- The plane D=V₁+V₁ᵍ in the exact natural model. -/
def pairPlane : Submodule F (Fin 3 → F) :=
  d.point ⊔ (conjugatePoint d ⟨g, d.g_mem⟩).val

/-- The source dual mark is the annihilator of that plane. Proving its
dimension and plane-stabilizer invariance belongs to the dual geometry. -/
def pairAnnihilator : Submodule F (Module.Dual F (Fin 3 → F)) :=
  (pairPlane d).dualAnnihilator

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
