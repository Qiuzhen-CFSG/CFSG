module
public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.VertexLocalModule
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts

/-!
# The initial graph center is the original Section Six module

For the actual ambient Section Nine context, suppose the initial vertex
stabilizer maps to P₁. Its graph center then maps to the precise ambient
Section Six module `sectionSixV S P1`. The embedding need not be surjective
onto the ambient group, and Hypothesis Two remains on that ambient group.

The edge Sylow data selects an intrinsic Sylow subgroup whose graph image
is T and whose ambient image is S. The existing vertex-local-module theorem,
proved by Sylow conjugacy, identifies the graph center with the normal
closure of that selected Sylow omega-center. Injective omega-center transport
identifies its generators with Ω₁(Z(S)). Mapping the defining conjugates
then gives exactly the P₁-conjugate closure defining Section Six V.

This is the module identification needed to apply the source-faithful (6.4)
in Stellmacher (9.2), Journal of Algebra 190 (1997), p.48, using the vertex
center definition from Section Seven. Source: `refs/files/stellmacher-n-group.pdf`.
The mapped-stabilizer equality is supplied by `nine_two_ambient_setup`;
it is explicit here so this transport leaf does not depend on that proof.
-/
open Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven
open CosetGraphContext
universe u

public theorem Stellmacher.SectionNine.nine_two_center_eq_sectionSixV
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hmapGa : (GAt ctx.Γ ctx.criticalPath.a).map embedding = P1) :
    (ZAt ctx.Γ ctx.criticalPath.a).map embedding = sectionSixV S P1 := by
  let P := GAt ctx.Γ ctx.criticalPath.a
  obtain ⟨_, U, hU⟩ := (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  let f : P →* H := embedding.comp P.subtype
  have hf : Function.Injective f := ctx.embedding_injective.comp P.subtype_injective
  have hUm : (U : Subgroup P).map f = S := by
    rw [show f = embedding.comp P.subtype from rfl, ← Subgroup.map_map, hU, ctx.map_S]
  have hOm : (omegaOneCenterAmbient (U : Subgroup P)).map f = omegaOneCenter S := by
    rw [← omegaOneCenterAmbient_map_injective f hf, hUm]
    rfl
  have hfrange : f.range = P1 := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hmapGa
  have hlocal := vertexZ_eq_local_vSubgroup ctx.Γ ctx.criticalPath.a U
  change (SectionTwo.vSubgroup U).map P.subtype = ZAt ctx.Γ ctx.criticalPath.a at hlocal
  rw [← hlocal, Subgroup.map_map]
  change (Subgroup.normalClosure
    (omegaOneCenterAmbient (U : Subgroup P) : Set P)).map f = _
  rw [Subgroup.normalClosure, MonoidHom.map_closure, sectionSixV, Stellmacher.SectionsFiveToSeven.conjugateClosure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have hgf : f g ∈ P1 := hfrange ▸ (show f g ∈ f.range from ⟨g, rfl⟩)
    have hzf : f z ∈ omegaOneCenter S := hOm ▸ Subgroup.mem_map_of_mem f hz
    refine ⟨⟨f g, hgf⟩, ⟨f z, hzf⟩, ?_⟩
    simpa only [map_mul, map_inv] using (congrArg f hg).symm
  · rintro ⟨g, z, rfl⟩
    obtain ⟨g0, hg0⟩ := (show (g : H) ∈ f.range from hfrange.symm ▸ g.property)
    obtain ⟨z0, hz0, hz0eq⟩ := Subgroup.mem_map.mp (hOm.ge z.property)
    refine ⟨g0 * z0 * g0⁻¹, ?_, ?_⟩
    · exact Group.mem_conjugatesOfSet_iff.mpr
        ⟨z0, hz0, isConj_iff.mpr ⟨g0, rfl⟩⟩
    · simp only [map_mul, map_inv, hg0, hz0eq]
