module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.Assembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.MarkedProduct.PointRadical
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.SeedTensor
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Tensor inputs from the constructed covered product

The constructed product sends the source cubic subgroup to the literal
second-factor tensor actor and the critical two-core to the literal point
shears. Critical conjugacy, star ranks, fixed spaces, fixed codimensions and
quadraticity transport through that same equivalence. The source module and
all its vectors remain unchanged.

The literal seed is a generating point seed once its earlier plane dimension
is supplied. Its normalization, parabolic mark, cubic mark, centralization
and both commutator identities come from the constructed group geometry.
Tensor identification and the critical-pair exclusion remain with their
representation-theoretic consumers; quadraticity gives no rank-one bound.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), covered-A₆ paragraph, printed p.957, with the earlier critical
geometry through 13.8.18.
-/

public section
open Subgroup Matrix.PSL3Two Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
open ResidualPlacement ExternalModules
namespace SourceProductGeometry
variable {G : Type*} [Group G] {H K L T V₁ V₃ : Subgroup G}
    {eK : Source.starImage H K ≃* BinaryLinearThree.Group}
    (geo : SourceProductGeometry H K L T V₁ V₃ eK)

/-- The literal tensor cubic is the marked second-factor alternating subgroup. -/
theorem tensorCubic_inverse_image :
    tensorCubic.map geo.equiv.symm.toMonoidHom = Source.starImage H (plus L T V₁) := by
  have hC : tensorCubic = (⊥ : Subgroup BinaryLinearThree.Group).prod (alternatingGroup (Fin 3)) := by
    ext z
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact ⟨rfl,hs⟩
    · rintro ⟨hz,hs⟩
      exact ⟨z.2,hs,Prod.ext (mem_bot.mp hz).symm rfl⟩
  rw [hC, ← geo.plus_image, map_map]
  have he : geo.equiv.symm.toMonoidHom.comp geo.equiv.toMonoidHom = MonoidHom.id _ := by
    ext x
    exact geo.equiv.symm_apply_apply x
  rw [he, map_id]

/-- Valpha lies in the literal point-shear actor used by the tensor consumer. -/
theorem critical_image_le_tensorPointRadical [Finite G] (Vα : Subgroup G)
    (hα : Source.starImage H Vα ≤ (Source.starImage H (one L T V₁ ⊔ T)).pCoreIn 2) :
    (Source.starImage H Vα).map geo.equiv.toMonoidHom ≤ MarkedCritical.tensorPointRadical := by
  rw [← MarkedProduct.pointV_prod_eq_tensorPointRadical]
  exact geo.critical_image_le Vα hα

/-- Critical conjugacy uses the image of the original conjugator under the
same product map, preserving the two actual critical subgroups. -/
theorem critical_conjugacy (A B : Subgroup G) (c : Source.Hstar H)
    (hconj : (Source.starImage H A).map (MulAut.conj c).toMonoidHom = Source.starImage H B) :
    ((Source.starImage H A).map geo.equiv.toMonoidHom).map
      (MulAut.conj (geo.equiv c)).toMonoidHom = (Source.starImage H B).map geo.equiv.toMonoidHom := by
  have he : (MulAut.conj (geo.equiv c)).toMonoidHom.comp geo.equiv.toMonoidHom =
      geo.equiv.toMonoidHom.comp (MulAut.conj c).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change geo.equiv c * geo.equiv x * (geo.equiv c)⁻¹ = geo.equiv (c * x * c⁻¹)
    rw [map_mul, map_mul, map_inv]
  rw [map_map, he, ← map_map, hconj]

/-- Product coordinates preserve the star rank of every actual critical actor. -/
theorem critical_rank (A : Subgroup G) :
    rank ((Source.starImage H A).map geo.equiv.toMonoidHom) = rank (Source.starImage H A) :=
  rank_map_injective geo.equiv.toMonoidHom geo.equiv.injective _

variable [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- The fixed space remains the same literal subspace of U_H/V₁. -/
theorem critical_fixedSpace (act : SourceAction H V₃ V₁) (A : Subgroup G) :
    fixedSpace (act.representation.comp geo.equiv.symm.toMonoidHom)
      ((Source.starImage H A).map geo.equiv.toMonoidHom) =
        fixedSpace act.representation (Source.starImage H A) := by
  rw [fixedSpace_comp_map, map_map]
  have he : geo.equiv.symm.toMonoidHom.comp geo.equiv.toMonoidHom = MonoidHom.id _ := by
    ext x
    exact geo.equiv.symm_apply_apply x
  rw [he, map_id]

/-- The source fixed-codimension bounds require no new representation premise. -/
theorem critical_fixedCodim (act : SourceAction H V₃ V₁) (A : Subgroup G) :
    fixedCodim (act.representation.comp geo.equiv.symm.toMonoidHom)
      ((Source.starImage H A).map geo.equiv.toMonoidHom) =
        fixedCodim act.representation (Source.starImage H A) := by
  unfold fixedCodim
  rw [geo.critical_fixedSpace act A]

/-- Quadraticity transports without imposing an invalid rank-one bound. -/
theorem critical_quadratic (act : SourceAction H V₃ V₁) (A : Subgroup G)
    (hq : IsQuadratic act.representation (Source.starImage H A)) :
    IsQuadratic (act.representation.comp geo.equiv.symm.toMonoidHom)
      ((Source.starImage H A).map geo.equiv.toMonoidHom) := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
  change act.representation (geo.equiv.symm (geo.equiv a))
      (act.representation (geo.equiv.symm (geo.equiv b)) v - v) =
    act.representation (geo.equiv.symm (geo.equiv b)) v - v
  rw [geo.equiv.symm_apply_apply, geo.equiv.symm_apply_apply]
  exact hq a ha b hb v

/-- The constructed product geometry supplies the marked generating point seed.
Its plane dimension is the explicit earlier source dimension; the action,
seed, parabolic, cubic and component coordinates are unchanged. -/
theorem generating_point_seed [Finite G] (act : SourceAction H V₃ V₁)
    (hd : Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2) :
    BinaryLinearThree.PointTensor.IsGeneratingSeed
      (act.representation.comp geo.equiv.symm.toMonoidHom) (seedSpace H V₃ V₁) ∧
    seedSpace H V₃ V₁ ≤ fixedSpace act.representation (Source.starImage H (zero L)) ∧
    subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H (plus L T V₁)) = seedSpace H V₃ V₁ ∧
    subspaceCommutator act.representation ⊤ (Source.starImage H (plus L T V₁)) = ⊤ := by
  exact source_generating_point_seed H V₃ V₁ act geo.equiv (one L T V₁) T (zero L) (plus L T V₁)
    geo.parabolic_seed_normalizes geo.plus_le (geo.plus_le_one.trans le_sup_left)
    geo.oneT_image geo.tensorCubic_inverse_image hd geo.component.seed_zero_fixed geo.component.seed_moved

end SourceProductGeometry
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
