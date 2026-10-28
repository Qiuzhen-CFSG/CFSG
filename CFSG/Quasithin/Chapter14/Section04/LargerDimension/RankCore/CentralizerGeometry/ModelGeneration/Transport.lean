module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ModelGeneration
/-!
# Transporting the source marking to Hᵍ/O₂(Hᵍ)

Right conjugation is g⁻¹Hg. Its quotient equivalence carries the image of
W^(g⁻¹) in H/O₂(H) to the literal image of W in Hᵍ/O₂(Hᵍ), preserving its
cardinality. Residuals and commutators commute with these maps. Thus the
source generation statement must be invoked at transporter g⁻¹.

Source: Aschbacher–Smith 14.4.7, the symmetry step on printed p.1009.
-/

@[expose] public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ModelGeneration
variable {G : Type*} [Group G]
def conjugateEquiv (H : Subgroup G) (g : G) : H ≃* conjugate H g :=
  (MulAut.conj g⁻¹).subgroupMap H
noncomputable def starEquiv (H : Subgroup G) (g : G) :
    (H ⧸ pCore 2 H) ≃* ((conjugate H g) ⧸ pCore 2 (conjugate H g)) :=
  QuotientGroup.congr _ _ (conjugateEquiv H g) (pCore_map_iso 2 (conjugateEquiv H g))
theorem actor_map (H B : Subgroup G) (g : G) :
    ((conjugate B g⁻¹).subgroupOf H).map (conjugateEquiv H g).toMonoidHom =
      B.subgroupOf (conjugate H g) := by
  apply Subgroup.map_injective (conjugate H g).subtype_injective
  rw [map_map, subgroupOf_map_subtype]
  change ((conjugate B g⁻¹).subgroupOf H).map
    ((MulAut.conj g⁻¹).toMonoidHom.comp H.subtype) = _
  rw [← map_map, subgroupOf_map_subtype, map_inf _ _ _ (MulAut.conj g⁻¹).injective]
  change conjugate (conjugate B g⁻¹) g ⊓ conjugate H g = _
  rw [conjugate_conjugate, inv_mul_cancel, conjugate_one]
theorem star_actor_map (H B : Subgroup G) (g : G) :
    (((conjugate B g⁻¹).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).map
      (starEquiv H g).toMonoidHom =
      (B.subgroupOf (conjugate H g)).map (QuotientGroup.mk' (pCore 2 (conjugate H g))) := by
  have he : (starEquiv H g).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H)) =
      (QuotientGroup.mk' (pCore 2 (conjugate H g))).comp (conjugateEquiv H g).toMonoidHom := by
    ext x
    exact QuotientGroup.congr_mk' _ _ (conjugateEquiv H g)
      (pCore_map_iso 2 (conjugateEquiv H g)) x
  rw [map_map, he, ← map_map, actor_map]
theorem star_actor_card (H B : Subgroup G) (g : G) :
    Nat.card ((B.subgroupOf (conjugate H g)).map
      (QuotientGroup.mk' (pCore 2 (conjugate H g)))) =
      Nat.card (((conjugate B g⁻¹).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) := by
  rw [← star_actor_map]
  exact card_map_of_injective (starEquiv H g).injective
theorem star_generation_transport [Finite G] (H B : Subgroup G) (g : G)
    (h : ⁅pResidual 2 (H ⧸ pCore 2 H),
      ((conjugate B g⁻¹).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))⁆ =
      pResidual 2 (H ⧸ pCore 2 H)) :
    (pResidual 2 (conjugate H g)).map (QuotientGroup.mk' (pCore 2 (conjugate H g))) =
      ⁅(pResidual 2 (conjugate H g)).map (QuotientGroup.mk' (pCore 2 (conjugate H g))),
        (B.subgroupOf (conjugate H g)).map (QuotientGroup.mk' (pCore 2 (conjugate H g)))⁆ := by
  rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]
  have hh := congrArg (Subgroup.map (starEquiv H g).toMonoidHom) h
  rw [map_commutator, map_pResidual, star_actor_map] at hh
  exact hh.symm
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ModelGeneration
