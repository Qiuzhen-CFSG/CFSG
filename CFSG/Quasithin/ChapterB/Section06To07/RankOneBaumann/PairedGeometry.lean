module
public import Theory.SpecificGroups.SL2.PairedResidualGeneration
public import Theory.GroupTheory.SylowNormalRestriction
/-!
# The original residual conjugator for a paired Thompson image

The actual normal layer is marked as two SL₂ factors. Its embedded residual
lies in the ambient residual, so the concrete paired conjugator lifts along
the original quotient map to an element of O²(G). It makes the two actual
Thompson images generate the layer once the paired offender calculation
identifies the Thompson image with the original Sylow intersection.
That image equality is supplied by PairedImages, not assumed in final assembly.
Source: Aschbacher–Smith B.6.10 and E.2.3, pp.117 and216–217.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
open Subgroup
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [Field F] [Finite F] [CharP F 2]
theorem exists_residual_conjugate_thompson_images_sup_eq_pair
    (T : Sylow 2 G) (q : G →* H) (hq : Function.Surjective q)
    (L : Subgroup H) [L.Normal] (e : L ≃* SL(2,F) × SL(2,F))
    (J : Subgroup G) (hJ : J.map q = (T : Subgroup G).map q ⊓ L) :
    ∃ g ∈ pResidual 2 G, J.map q ⊔ (J.map (MulAut.conj g).toMonoidHom).map q = L := by
  let P := T.mapSurjective hq
  obtain ⟨Q,hQ⟩ := P.exists_sylow_map_eq_inf_of_normal L
  let R := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨z,hz,hgen⟩ := Matrix.SpecialLinearGroup.exists_residual_conjugate_paired_sylow R
  let k : (SL(2,F) × SL(2,F)) →* H := L.subtype.comp e.symm.toMonoidHom
  have hkz : k z ∈ (pResidual 2 G).map q := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact map_pResidual_le 2 k (mem_map_of_mem k hz)
  obtain ⟨g,hg,hgq⟩ := mem_map.mp hkz
  refine ⟨g,hg,?_⟩
  have hJQ : J.map q = (Q : Subgroup L).map L.subtype := hJ.trans hQ.symm
  have hRk : (R : Subgroup _).map k = J.map q := by
    change ((Q : Subgroup L).map e.toMonoidHom).map k = _
    rw [map_map,hJQ]
    congr 1
    apply MonoidHom.ext
    intro a
    exact congrArg Subtype.val (e.symm_apply_apply a)
  have hconj : ((R : Subgroup _).map (MulAut.conj z).toMonoidHom).map k =
      (J.map (MulAut.conj g).toMonoidHom).map q := by
    rw [map_map,show k.comp (MulAut.conj z).toMonoidHom =
      (MulAut.conj (q g)).toMonoidHom.comp k from by
        apply MonoidHom.ext
        intro a
        change k (z*a*z⁻¹) = q g * k a * (q g)⁻¹
        simp only [map_mul,map_inv,hgq],←map_map,hRk,map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro a
    change q g * q a * (q g)⁻¹ = q (g*a*g⁻¹)
    simp only [map_mul,map_inv]
  have htop : (⊤ : Subgroup (SL(2,F) × SL(2,F))).map k = L := by
    rw [show k = L.subtype.comp e.symm.toMonoidHom from rfl,←map_map,
      map_top_of_surjective _ e.symm.surjective,←MonoidHom.range_eq_map,range_subtype]
  have hh := congrArg (Subgroup.map k) hgen
  rwa [Subgroup.map_sup,hRk,hconj,htop] at hh
end CFSG.Quasithin.ChapterB.RankOneBaumann
