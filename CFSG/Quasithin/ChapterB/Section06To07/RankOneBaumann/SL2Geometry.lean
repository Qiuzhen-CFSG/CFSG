module
public import Theory.SpecificGroups.SL2.ResidualSylowGeneration
public import CFSG.Quasithin.ChapterB.Section02.Thompson
/-!
# The two generating conjugates in the rank-one Baumann argument

The original two-residual supplies two mapped Sylows generating the actual
SL2 quotient, including the field of two elements. Once the genuine natural
module calculation identifies the Thompson image with the Sylow image,
the same original residual element gives the two Thompson conjugates.

The Thompson-image premise is supplied by
`RankOneBaumann.thompson_baumann_images_of_natural_quotient` in `Offenders`.
The source assembly retains that discharge and the independent dimension
calculation for B.2.18(d); no generation premise is assumed here.
Source: Aschbacher--Smith B.6.10, printed p.117.
-/
public noncomputable section
open Subgroup Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]

/-- The original residual supplies the two generating mapped Sylows required by B.6.10. -/
theorem exists_residual_conjugate_sylow_image_sup_eq_top
    (T : Sylow 2 H) (q : H →* SL(2,F)) (hq : Function.Surjective q) :
    ∃ g : H, g ∈ pResidual 2 H ∧
      (T : Subgroup H).map q ⊔
        (((T : Subgroup H).map (MulAut.conj g).toMonoidHom).map q) = ⊤ :=
  Matrix.SpecialLinearGroup.exists_residual_conjugate_sylow_image_sup_eq_top T q hq

/-- Once B.2.20 identifies the Thompson image, the same original residual element gives its two generating conjugates. -/
theorem exists_residual_conjugate_thompson_images_sup_eq_top
    (T : Sylow 2 H) (q : H →* SL(2,F)) (hq : Function.Surjective q)
    (hJ : (elementaryAbelianMaxJ (T : Subgroup H)).map q = (T : Subgroup H).map q) :
    ∃ g : H, g ∈ pResidual 2 H ∧
      (elementaryAbelianMaxJ (T : Subgroup H)).map q ⊔
        (((elementaryAbelianMaxJ (T : Subgroup H)).map
          (MulAut.conj g).toMonoidHom).map q) = ⊤ := by
  obtain ⟨g,hg,hgen⟩ := exists_residual_conjugate_sylow_image_sup_eq_top T q hq
  have hmap (A : Subgroup H) : (A.map (MulAut.conj g).toMonoidHom).map q =
      (A.map q).map (MulAut.conj (q g)).toMonoidHom := by
    rw [Subgroup.map_map,Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change q (g * x * g⁻¹) = q g * q x * (q g)⁻¹
    simp only [map_mul,map_inv]
  refine ⟨g,hg,?_⟩
  rw [hmap,hJ]
  rwa [hmap] at hgen
end CFSG.Quasithin.ChapterB.RankOneBaumann
