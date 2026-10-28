module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.CommonFacts

/-!
# The marked binary model used by the relative-normalizer choices

The space is the literal multiplicative additive group of F₂³, with
matrix action, pointwise plane fixers and setwise plane stabilizers.
`LocalModel` specifies a compatible quotient and natural-module marking
at an actual vertex. Constructing it, and identifying the actual edge
kernel with the inverse image of a pointwise plane fixer, are separate
proof obligations. No generating group or selected vertex is a field.

These shared definitions separate the finite matrix calculation from
transport in the amalgam. They do not assert the existence of choices.

Source: Meierfrankenfeld--Stellmacher (1993), notation on p.881 and
the choice of distinct intersection lines in (4.3.7)(i), p.887.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection.Choices

abbrev Space := Multiplicative (Fin 3 → ZMod 2)

/-- The literal natural action, written multiplicatively to match U_a. -/
def modelAction : SL →* MulAut Space where
  toFun g := (Matrix.SpecialLinearGroup.toLin' g).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (Matrix.SpecialLinearGroup.toLin' 1 v.toAdd) = v
    rw [map_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd ((Matrix.SpecialLinearGroup.toLin' (g * h)) v.toAdd) =
      Multiplicative.ofAdd ((Matrix.SpecialLinearGroup.toLin' g)
        ((Matrix.SpecialLinearGroup.toLin' h) v.toAdd))
    rw [map_mul]
    rfl

@[simp] theorem modelAction_apply (g : SL) (v : Space) :
    (modelAction g v).toAdd = g.val.mulVec v.toAdd := rfl

/-- Pointwise fixer of a subgroup of the natural three-space. -/
def planeFixer (A : Subgroup Space) : Subgroup SL where
  carrier := {g | ∀ v ∈ A, modelAction g v = v}
  one_mem' := by intro v hv; simp
  mul_mem' := by
    intro g h hg hh v hv
    simp only [map_mul, MulAut.mul_apply, hh v hv, hg v hv]
  inv_mem' := by
    intro g hg v hv
    apply (modelAction g).injective
    rw [map_inv, MulAut.apply_inv_self, hg v hv]

/-- Setwise stabilizer of a subgroup of the natural three-space. -/
def planeStabilizer (A : Subgroup Space) : Subgroup SL where
  carrier := {g | A.map (modelAction g).toMonoidHom = A}
  one_mem' := by
    change A.map (modelAction 1).toMonoidHom = A
    rw [map_one]
    exact Subgroup.map_id A
  mul_mem' := by
    intro g h hg hh
    change A.map (modelAction (g * h)).toMonoidHom = A
    rw [map_mul]
    change A.map ((modelAction g).toMonoidHom.comp (modelAction h).toMonoidHom) = A
    rw [← Subgroup.map_map, hh, hg]
  inv_mem' := by
    intro g hg
    have hh := congrArg (Subgroup.map (modelAction g⁻¹).toMonoidHom) hg
    rw [Subgroup.map_map] at hh
    have he : (modelAction g⁻¹).toMonoidHom.comp (modelAction g).toMonoidHom =
        MonoidHom.id Space := by
      apply MonoidHom.ext
      intro v
      change modelAction g⁻¹ (modelAction g v) = v
      rw [map_inv, MulAut.inv_apply_self]
    rw [he, Subgroup.map_id] at hh
    exact hh.symm

/-- Common fixed subgroup of a concrete matrix subgroup. -/
def fixedSpace (H : Subgroup SL) : Subgroup Space where
  carrier := {v | ∀ g ∈ H, modelAction g v = v}
  one_mem' := by intro g hg; exact map_one _
  mul_mem' := by
    intro u v hu hv g hg
    rw [map_mul, hu g hg, hv g hg]
  inv_mem' := by
    intro v hv g hg
    rw [map_inv, hv g hg]

variable {M : Type*} [Group M] {R : Subgroup M}

/-- Compatible markings of the actual local quotient and natural layer.
The producer must construct this from `LocalSource` and `NaturalU`. -/
structure LocalModel (a : Vertex R) where
  projection : stabilizer R a →* SL
  surjective : Function.Surjective projection
  kernel : projection.ker = (Q R a).subgroupOf (stabilizer R a)
  equiv : U R a ≃* Space
  action : ∀ (g : stabilizer R a) (u v : U R a),
    (v : FreeAmalgam R) = g * (u : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹ →
      equiv v = modelAction (projection g) (equiv u)

namespace LocalModel
variable {a : Vertex R} (model : LocalModel a)

/-- Image in the actual marked local quotient. -/
def actorImage (H : Subgroup (FreeAmalgam R)) : Subgroup SL :=
  (H.subgroupOf (stabilizer R a)).map model.projection

/-- Natural coordinates of an ambient subgroup, intersected with U_a. -/
noncomputable def coordinates (A : Subgroup (FreeAmalgam R)) : Subgroup Space :=
  (A.subgroupOf (U R a)).map model.equiv.toMonoidHom

end LocalModel
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection.Choices
