module
public import Theory.Representation.G2BinaryPointGeneration
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Residual

/-!
# Generation by an actual binary natural G₂ offender

Every natural offender is conjugate to the marked root eight. Transporting
the known two-root-eight generation statement by that same conjugator
keeps the second conjugator in G₂(2)′. Thus the original offender, with
no change of its marking, generates full G₂(2) with a derived conjugate.
This supplies the image-generation step in Aschbacher–Smith 3.3.28, p.601.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Atlas.G2.Natural.BinaryPointGeneration

theorem offender_exists_derived_conjugate_generating
    (A : Subgroup (Model (ZMod 2)))
    (hA : IsOffender (NaturalOffenders.binaryNatural (F := ZMod 2)) A) :
    ∃ c ∈ commutator (Model (ZMod 2)),
      A ⊔ A.map (MulAut.conj c).toMonoidHom = ⊤ := by
  obtain ⟨g, hg⟩ := NaturalOffenders.natural_offender_conjugate_elementary
    (F := ZMod 2) (n := 1) (by norm_num) (by decide) A hA
  rw [← BinaryModelOffenders.elementary_eq] at hg
  obtain ⟨c, hc, hgen⟩ := exists_residual_conjugate_generating
  rw [EvenFieldFixedResidual.binary_twoResidual_eq_commutator] at hc
  refine ⟨g * c * g⁻¹, (inferInstance : (commutator (Model (ZMod 2))).Normal).conj_mem c hc g, ?_⟩
  have he :
      (BinaryCore.elementary.map (MulAut.conj c).toMonoidHom).map
        (MulAut.conj g).toMonoidHom =
      (BinaryCore.elementary.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj (g * c * g⁻¹)).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hm := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hgen
  rw [Subgroup.map_sup, he, ← hg, map_top_of_surjective _ (MulAut.conj g).surjective] at hm
  exact hm

end Atlas.G2.Natural.BinaryPointGeneration
