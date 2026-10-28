module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.CentralKernel.RootLift.GeometryInterface
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.CentralKernel.RootLift.Geometry
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.CentralKernel.RootLift.Transport
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.CentralKernel.RootLift.MarkedAction

/-!
# The G.2.5 root lift from the independent SL₃ flag calculation

The actual quotient map followed by the supplied model transports the
marked radical and Sylow into SL₃(F). Their order, natural action and
normalization follow from the permitted source inputs. A matrix root
conjugator then lifts through the surjective star map; its intersection
with the original Sylow supplies the required faithful second factor.

The proved finite-matrix calculation discharges `ModelRootGeometry` over
every field of order 2ⁿ, including n = 1. Thus `hasRootLift` constructs the
root factor from the preceding source inputs, preserving the original g,h
and their denominator P. Kernel elimination remains with the independent
residual argument and the central-kernel assembly.
Source: Aschbacher–Smith G.2.5(3), printed pp.335–336.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel
open Setup
variable {G : Type*} [Group G] [Finite G]
  {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)

/-- The actual G.2.5 application of the independent matrix calculation.
All order and natural-action premises are discharged from the allowed inputs.
The displayed matrix premise remains a separate mathematical obligation. -/
theorem hasRootLift_of_model_geometry (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (eU : D.star D.U ≃* Multiplicative (Fin 2 → F))
    (hmove : ⁅D.V, D.U⁆ = D.V₁) (hgeometry : ModelRootGeometry F) :
    letI := d.WProduct_normal hUT hstar.ge
    HasRootLift d hUT hstar := by
  let := d.WProduct_normal hUT hstar.ge
  let m := rootModelMap d hUT hstar
  let A := rootModelRadical d hUT hstar
  obtain ⟨R, hR⟩ := exists_sylow_eq_image_T d hUT hstar
  let Q := R.mapSurjective (f := m) (rootModelMap_surjective d hUT hstar)
  have hAR : A ≤ Q := by
    change (image D g h D.U).map m ≤ (R : Subgroup (Quotient D g h)).map m
    rw [hR]
    exact map_mono (map_mono (comap_mono hUT))
  have hQA : (Q : Subgroup SL(3, F)) ≤ normalizer (A : Set SL(3, F)) := by
    change (R : Subgroup (Quotient D g h)).map m ≤ _
    rw [hR]
    exact (map_mono (image_T_normalizes_U d)).trans
      ((image D g h D.U).le_normalizer_map m)
  obtain ⟨x, hxdis, hxcover⟩ := hgeometry d.point A Q d.point_dimension
    (rootModelRadical_card d hUT hstar eU)
    (rootModelRadical_displacement d hUT hstar hmove)
    (rootModelRadical_fixes_point d hUT hstar) hAR hQA
  let f := starMap d hUT hstar
  let Astar := (image D g h D.U).map f
  let Tstar := (image D g h D.T).map f
  have hAmap : Astar.map d.model.toMonoidHom = A := by
    rw [Subgroup.map_map]
    rfl
  have hTmap : Tstar.map d.model.toMonoidHom = (Q : Subgroup SL(3, F)) := by
    change ((image D g h D.T).map f).map d.model.toMonoidHom =
      (R : Subgroup (Quotient D g h)).map m
    rw [hR, Subgroup.map_map]
    rfl
  have hconj : (conjugate Astar (d.model.symm x)).map d.model.toMonoidHom =
      A.map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [← hAmap]
    simp only [conjugate, Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro a
    change d.model ((d.model.symm x)⁻¹ * a * (d.model.symm x)⁻¹⁻¹) =
      x⁻¹ * d.model a * x⁻¹⁻¹
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hCmap : (Tstar ⊓ conjugate Astar (d.model.symm x)).map d.model.toMonoidHom =
      (Q : Subgroup SL(3, F)) ⊓ A.map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ d.model.injective, hTmap, hconj]
  apply hasRootLift_of_star_conjugate d hUT hstar
  refine ⟨d.model.symm x, ?_, ?_⟩
  · apply disjoint_def.mpr
    intro a ha hc
    apply d.model.injective
    rw [map_one]
    apply disjoint_def.mp hxdis
    · rw [← hAmap]
      exact mem_map_of_mem d.model.toMonoidHom ha
    · rw [← hCmap]
      exact mem_map_of_mem d.model.toMonoidHom hc
  · apply (map_le_map_iff_of_injective (f := d.model.toMonoidHom) d.model.injective).mp
    change Tstar.map d.model.toMonoidHom ≤
      (Astar ⊔ (Tstar ⊓ conjugate Astar (d.model.symm x))).map d.model.toMonoidHom
    rw [Subgroup.map_sup, hTmap, hAmap, hCmap]
    exact hxcover

/-- The root factor required by G.2.5(3), inside the genuine quotient I/P.
The field and natural-action hypotheses discharge the finite-matrix
calculation, without a residual or kernel-triviality premise. -/
theorem hasRootLift (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (eU : D.star D.U ≃* Multiplicative (Fin 2 → F))
    (hmove : ⁅D.V, D.U⁆ = D.V₁) :
    letI := d.WProduct_normal hUT hstar.ge
    HasRootLift d hUT hstar :=
  hasRootLift_of_model_geometry d hUT hstar eU hmove
    (modelRootGeometry F d.exponent_pos d.field_card)

end CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel
