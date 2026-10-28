module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneGeometry
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Changing coordinates in the original b=1 action

Postcompose the literal actor quotient with a matrix automorphism and pull
back its representation by the inverse automorphism. The original actor,
core, center section and neighbor remain the same. Transport of the fixed
space and its generated module preserves every source clause, including
the sharp reciprocal index. BOneFullProfiles uses this to realize the
whole-Cartan diagonal marking without adding a coordinate assumption.

Source: DGS, Groups and Graphs (1985), (7.1) and (10.5), pp.126--127,156--157,
and the compatible Cartan choices in (14.2), pp.210--211.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
variable {G k W : Type*} [Group G] [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
  {F : Bool → Subgroup G} {v w : Vertex F}

/-- Change only the matrix coordinates of the source actor quotient, and
pull back the representation by the inverse marking. -/
def BOneActionData.marking (d : BOneActionData F v w k W) (e : SL(2,k) ≃* SL(2,k)) :
    BOneActionData F v w k W := by
  let σ := d.representation.comp e.symm.toMonoidHom
  let π := e.toMonoidHom.comp d.quotient
  let S := d.imageSylow.mapSurjective (f := e.toMonoidHom) e.surjective
  have hfix : fixedSpace σ (S : Subgroup SL(2,k)) = fixedSpace d.representation d.imageSylow := by
    change fixedSpace (d.representation.comp e.symm.toMonoidHom)
      ((d.imageSylow : Subgroup SL(2,k)).map e.toMonoidHom) = _
    rw [fixedSpace_comp_map, Subgroup.map_map]
    have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id SL(2,k) := by
      apply MonoidHom.ext
      intro a
      exact e.symm_apply_apply a
    rw [he, Subgroup.map_id]
  have hcomp : σ.comp π = d.representation.comp d.quotient := by
    ext x z
    change d.representation (e.symm (e (d.quotient x))) z = _
    rw [e.symm_apply_apply]
    rfl
  exact {
    d with
    quotient := π
    onto := e.surjective.comp d.onto
    kernel := (MonoidHom.ker_comp_of_injective _ _ e.injective).trans d.kernel
    representation := σ
    coordinates := hcomp.symm ▸ d.coordinates
    imageSylow := S
    neighbor_image := by
      change ((Z F w).subgroupOf d.actor).map (e.toMonoidHom.comp d.quotient) =
        (d.imageSylow : Subgroup SL(2,k)).map e.toMonoidHom
      rw [← Subgroup.map_map, d.neighbor_image]
    sharp_index := by rw [hfix]; exact d.sharp_index
    quadratic := by
      rintro a ⟨b,hb,rfl⟩ c ⟨z,hz,rfl⟩ u
      simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using
        d.quadratic b hb z hz u
    generated := by
      exact generatedByFixedSpace_of_equivariant_surjection d.representation σ
        e.toMonoidHom LinearMap.id Function.surjective_id
        (by intro g z; simp [σ]) d.imageSylow d.generated
    fixed_bot := by
      dsimp only [σ]
      rw [fixedSpace_comp_map, Subgroup.map_top_of_surjective _ e.symm.surjective, d.fixed_bot] }

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
