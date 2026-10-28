module

public import Theory.Representation.SU3.CubicDegree.InnerActors.RootGeometry
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Transport of generation by three Sylow centers

Sylow conjugacy reduces the assertion to one Sylow subgroup, and an actual
group isomorphism transports it. Both operations retain the actual embedded
centers and the three literal conjugating elements.

Source: the matrix and scalar conventions of Huppert II.10.12; used in the
root-geometric degree estimate for Aschbacher--Smith K.3.3, printed p.456.
-/

public section
open Subgroup
namespace Representation.SU3.CubicDegree.InnerActors.ThreeRoots

theorem map_conjugate {G H : Type*} [Group G] [Group H]
    (f : G →* H) (U : Subgroup G) (g : G) :
    (U.map (MulAut.conj g).toMonoidHom).map f =
      (U.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem map_conjugate_mul {G : Type*} [Group G] (U : Subgroup G) (g h : G) :
    (U.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      U.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem of_one_sylow {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (c : Fin 3 → G)
    (hc : (⨆ i, (sylowCenter P).map (MulAut.conj (c i)).toMonoidHom) = ⊤) :
    ThreeRootGeneration G := by
  intro Q
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
  have hz : sylowCenter (g • P) =
      (sylowCenter P).map (MulAut.conj g).toMonoidHom :=
    (map_embeddedCenter (P : Subgroup G) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm
  refine ⟨fun i => c i * g⁻¹, ?_⟩
  simp only [hz, map_conjugate_mul, inv_mul_cancel_right]
  exact hc

theorem of_equiv {G H : Type*} [Group G] [Group H]
    [Finite G] (e : G ≃* H) (hH : ThreeRootGeneration H) : ThreeRootGeneration G := by
  intro P
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨c, hc⟩ := hH Q
  refine ⟨fun i => e.symm (c i), ?_⟩
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_iSup, map_top_of_surjective _ e.surjective]
  have hz : (sylowCenter P).map e.toMonoidHom = sylowCenter Q :=
    map_embeddedCenter (P : Subgroup G) e.toMonoidHom e.injective
  simpa only [map_conjugate, hz, MulEquiv.coe_toMonoidHom,
    e.apply_symm_apply] using hc

end Representation.SU3.CubicDegree.InnerActors.ThreeRoots
