module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Exterior.SourceFF.Offenders
public import Theory.Representation.SL5ExteriorSquare.MarkedRecognition
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.SectionOffender
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Incompatible offenders on the two ten-dimensional SL₅(2) modules

Complementary wedges identify the exterior cube with the actual dual of the
exterior square. A square best offender has rank four and cube fixed codimension
six, so the two irreducible modules have no common offender. Exhaustive
recognition therefore identifies any two ten-dimensional irreducibles sharing
an offender, while retaining the prescribed identification of the acting group.

This is the exterior-five exclusion in Aschbacher--Smith D.3.5(5), printed
p.196, using I.1.6(7). The literal chosen-seed application is in
`SeedAlternativesMovedSylowExterior`.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.SL5TenDimensional Representation.SL5ExteriorSquare
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325

private def squarePairing : ExteriorModule 2 ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (ExteriorModule 2) :=
  ((exteriorCoordinates 2).trans (dotProductEquiv (ZMod 2) (ExteriorIndex 2))).trans
    (exteriorCoordinates 2).dualMap

private theorem squarePairing_apply (v w : ExteriorModule 2) :
    squarePairing v w = dotProduct (exteriorCoordinates 2 v) (exteriorCoordinates 2 w) := rfl

private theorem exteriorMatrix_graph (g : SL5TenDimensional.Group) :
    exteriorMatrix 2 (Duality.graph g) = (exteriorMatrix 2 g⁻¹).transpose := by
  ext s t
  change (Matrix.of (fun i j : Fin 2 =>
    (Duality.graph g).val ((Set.powersetCard.ofFinEmbEquiv.symm s) j)
      ((Set.powersetCard.ofFinEmbEquiv.symm t) i))).det = _
  rw [Duality.graph_apply]
  exact Matrix.det_transpose _

private theorem squarePairing_action (g : SL5TenDimensional.Group) (v : ExteriorModule 2) :
    squarePairing (exteriorAction 2 (Duality.graph g) v) =
      (exteriorAction 2).dual g (squarePairing v) := by
  apply LinearMap.ext
  intro w
  change squarePairing (exteriorAction 2 (Duality.graph g) v) w =
    squarePairing v (exteriorAction 2 g⁻¹ w)
  rw [squarePairing_apply,squarePairing_apply,exteriorCoordinates_action,
    exteriorCoordinates_action,exteriorMatrix_graph]
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- Complementary wedges identify the exterior cube with the actual dual
of the exterior square, for the unchanged SL₅ actor. -/
def exteriorCubeDualEquiv : Representation.Equiv (exteriorAction 3) (exteriorAction 2).dual :=
  Representation.Equiv.mk (Duality.hodge.trans squarePairing) (by
    intro g
    apply LinearMap.ext
    intro v
    change squarePairing (Duality.hodge (exteriorAction 3 g v)) = _
    rw [Duality.hodge_action]
    exact squarePairing_action g (Duality.hodge v))

/-- A best offender on the exterior square has codimension six on the cube. -/
theorem exterior_cube_codim_of_square_best
    (A : Subgroup SL5TenDimensional.Group) (hA : IsBestOffender (exteriorAction 2) A) :
    fixedCodim (exteriorAction 3) A = 6 := by
  obtain ⟨g,hg⟩ := ChapterK.Linear.Exterior.SourceFF.best_conjugate_shear hA
  rw [←fixedCodim_map_conj (exteriorAction 3) A g,hg]
  have he := fixedCodim_map_equivariant (exteriorAction 3) (exteriorAction 2).dual
    (MonoidHom.id _) exteriorCubeDualEquiv.toLinearEquiv
    (fun g v => IntertwiningMap.isIntertwining _ _ exteriorCubeDualEquiv.toIntertwiningMap g v)
    shearSubgroup
  rw [Subgroup.map_id] at he
  rw [he,fixedCodim_dual_eq_moved_finrank,commutator_shearSubgroup]
  exact standard_dimensions.2.2.2.1

/-- The same subgroup cannot be an offender on both exterior modules. -/
theorem exterior_no_common_offender
    (A : Subgroup SL5TenDimensional.Group)
    (hA : IsOffender (exteriorAction 2) A)
    (hB : IsOffender (exteriorAction 3) A) : False := by
  have hbest := (hA.best_and_codim_eq_of_quadraticRatio_eq_one _
    ChapterK.Linear.Exterior.SourceFF.exterior_quadraticRatio).1
  have hr := (ChapterK.Linear.Exterior.SourceFF.best_rank_codim hbest).1
  have hc := exterior_cube_codim_of_square_best A hbest
  have hb := hB.2
  omega

private theorem offender_equiv {K U Z : Type*} [_root_.Group K]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup Z] [Module (ZMod 2) Z]
    {τ : Representation (ZMod 2) K U} {σ : Representation (ZMod 2) K Z}
    (e : Representation.Equiv τ σ) {A : Subgroup K} (hA : IsOffender τ A) :
    IsOffender σ A := by
  simpa only [Subgroup.map_id] using hA.map_equivariant τ σ (MonoidHom.id _)
    Function.injective_id e.toLinearEquiv
    (fun g v => IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v)

/-- A common offender determines the ten-dimensional irreducible SL₅(2)
constituent for the unchanged acting group. -/
theorem ten_dimensional_equiv_of_common_offender
    {U Z : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    (τ : Representation (ZMod 2) SL5TenDimensional.Group U)
    (σ : Representation (ZMod 2) SL5TenDimensional.Group Z)
    [IsIrreducible τ] [IsIrreducible σ]
    (hU : Module.finrank (ZMod 2) U = 10)
    (hZ : Module.finrank (ZMod 2) Z = 10)
    (A : Subgroup SL5TenDimensional.Group)
    (hA : IsOffender τ A) (hB : IsOffender σ A) :
    Nonempty (Representation.Equiv τ σ) := by
  rcases Classification.identification_of_finrank_ten τ hU with he | he <;>
    obtain ⟨e⟩ := he <;>
    rcases Classification.identification_of_finrank_ten σ hZ with hf | hf <;>
    obtain ⟨f⟩ := hf
  · exact ⟨e.trans f.symm⟩
  · exact (exterior_no_common_offender A (offender_equiv e hA) (offender_equiv f hB)).elim
  · exact (exterior_no_common_offender A (offender_equiv f hB) (offender_equiv e hA)).elim
  · exact ⟨e.trans f.symm⟩
/-- The common-offender test retains any prescribed identification of the
acting group with SL₅(2). -/
theorem ten_dimensional_equiv_of_marked_common_offender
    {K U Z : Type*} [_root_.Group K]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup Z] [Module (ZMod 2) Z]
    (τ : Representation (ZMod 2) K U) (σ : Representation (ZMod 2) K Z)
    [IsIrreducible τ] [IsIrreducible σ]
    (e : K ≃* SL5TenDimensional.Group)
    (hU : Module.finrank (ZMod 2) U = 10) (hZ : Module.finrank (ZMod 2) Z = 10)
    (A : Subgroup K) (hA : IsOffender τ A) (hB : IsOffender σ A) :
    Nonempty (Representation.Equiv τ σ) := by
  let τ' := τ.comp e.symm.toMonoidHom
  let σ' := σ.comp e.symm.toMonoidHom
  let : IsIrreducible τ' :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective τ).mpr inferInstance
  let : IsIrreducible σ' :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective σ).mpr inferInstance
  have hi (g : K) (v : U) : τ g v = τ' (e g) v := by
    simp only [τ',MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply]
  have hj (g : K) (v : Z) : σ g v = σ' (e g) v := by
    simp only [σ',MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply]
  obtain ⟨d⟩ := ten_dimensional_equiv_of_common_offender τ' σ' hU hZ
    (A.map e.toMonoidHom)
    (hA.map_equivariant τ τ' e.toMonoidHom e.injective (LinearEquiv.refl _ _) hi)
    (hB.map_equivariant σ σ' e.toMonoidHom e.injective (LinearEquiv.refl _ _) hj)
  refine ⟨Representation.Equiv.mk d.toLinearEquiv ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  change d (τ g v) = σ g (d v)
  have he := IntertwiningMap.isIntertwining _ _ d.toIntertwiningMap (e g) v
  simpa only [τ',σ',MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    e.symm_apply_apply,Representation.Equiv.toLinearEquiv_apply,
    Representation.Equiv.coe_toIntertwiningMap] using he

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
