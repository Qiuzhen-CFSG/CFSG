module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.Products
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Conjugating the marked five-normalizer

The intrinsic centralizer layer commutes with ambient isomorphisms. This
transports both marked factors and the inverting involution while retaining
the conjugacy class of the fixed source involution. Thus the geometric product
construction is needed only for five-subgroups in the selected centralizer.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), printed p.261.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer
variable {G : Type*} [Group G] [Finite G]

private theorem map_layer_le {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    (componentLayer H).map e.toMonoidHom ≤ componentLayer K := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro J hJ
  exact map_le_iff_le_comap.mp (le_sSup (hJ.map_equiv e))

private theorem map_layer {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    (componentLayer H).map e.toMonoidHom = componentLayer K := by
  apply le_antisymm (map_layer_le e)
  have hm := map_mono (f := e.toMonoidHom) (map_layer_le e.symm)
  simpa [map_map] using hm

omit [Finite G] in
private theorem map_centralizer (e : G ≃* G) (E : Subgroup G) :
    (centralizer (E : Set G)).map e.toMonoidHom = centralizer (E.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

omit [Finite G] in
/-- Transport of the literal ambient image of the intrinsic centralizer layer. -/
theorem fiveComponent_map (e : G ≃* G) (E : Subgroup G) :
    (fiveComponent E).map e.toMonoidHom = fiveComponent (E.map e.toMonoidHom) := by
  let c : centralizer (E : Set G) ≃* centralizer (E.map e.toMonoidHom : Set G) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_centralizer e E))
  rw [fiveComponent, fiveComponent, ← map_layer c, map_map, map_map]
  rfl

namespace ProductData
variable {D : Seed G} {E : Subgroup G} (W : ProductData D E)

/-- All marked product coordinates conjugate with E; the seed stays fixed. -/
noncomputable def conjugate (g : G) :
    ProductData D (E.map (MulAut.conj g).toMonoidHom) := by
  let e := MulAut.conj g
  let ne : normalizer (E : Set G) ≃* normalizer (E.map e.toMonoidHom : Set G) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_equiv_normalizer_eq _ _))
  refine {
    equiv := ne.symm.trans W.equiv
    component_factor := ?_
    inverter := e W.inverter
    inverter_conj := W.inverter_conj.trans (isConj_iff.mpr ⟨g, rfl⟩)
    inverts := ?_
    dihedral_factor := ?_ }
  · have hm := congrArg (Subgroup.map e.toMonoidHom) W.component_factor
    rw [fiveComponent_map, map_map] at hm
    exact hm
  · rintro _ ⟨x, hx, rfl⟩
    change e W.inverter * e x * (e W.inverter)⁻¹ = (e x)⁻¹
    simpa only [map_mul, map_inv] using congrArg e (W.inverts x hx)
  · have hm := congrArg (Subgroup.map e.toMonoidHom) W.dihedral_factor
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, map_map] at hm
    exact hm

end ProductData
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer
