module

public import Theory.Representation.BinaryNaturalDual.FourActors.Model
public import Theory.Representation.BinaryNaturalDual.RadicalCore

/-!
# Two-space radicals in the actual automorphism action

The inner-action specification transports the radical's fixed space and full
corank-two generated core from the natural linear group to its actual inner
image. The fixed space is the product of the two-space and its annihilator,
hence has dimension four. Surjective actor transport identifies the cores.

These theorems compute every two-space radical. Identifying the distinguished
rank-four representative with such a radical remains a separate obligation;
no radical identification is included as part of a definition.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.3(4),
printed p.391, PDF p.402.
-/

@[expose] public section

namespace BinaryNaturalDual.FourActors
open BinaryLinear

variable (d : CoordinateAction 4)

/-- The natural-plus-dual action of the inner copy of the linear group. -/
theorem innerRepresentation_eq :
    d.representation.comp (MulAut.conj : G →* M) = naturalDualRepresentation := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  exact d.on_inner g v

/-- The genuine radical embedded in the ambient automorphism group. -/
noncomputable def radicalImage (U : Submodule (ZMod 2) X) : Subgroup M :=
  (radical U).map (MulAut.conj : G →* M)

/-- The marked fixed subspace survives passage to the inner automorphism image. -/
theorem actorFixed_radicalImage (U : Submodule (ZMod 2) X) (hU : U ≠ ⊥) (hUt : U ≠ ⊤) :
    actorFixed d (radicalImage U) = U.prod U.dualAnnihilator := by
  change Representation.BinaryOffender.fixedSpace d.representation
    ((radical U).map (MulAut.conj : G →* M)) = _
  rw [← Representation.BinaryOffender.fixedSpace_comp_map, innerRepresentation_eq]
  have h := fixedSpace_radical U hU hUt
  rw [Representation.BinaryOffender.fixedSpace_comp_map, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

/-- Radical cores also survive passage to the actual inner actors. -/
theorem actorCore_radicalImage (U : Submodule (ZMod 2) X)
    (hU : Module.finrank (ZMod 2) U = 2) : actorCore d (radicalImage U) 2 = ⊤ := by
  let : Finite G := Finite.of_injective (fun g : G => (g : X → X)) DFunLike.coe_injective
  let f : radical U →* radicalImage U := {
    toFun g := ⟨MulAut.conj g.val, Subgroup.mem_map_of_mem _ g.property⟩
    map_one' := Subtype.ext MulAut.conj.map_one
    map_mul' g h := Subtype.ext (MulAut.conj.map_mul g.val h.val) }
  have hf : Function.Surjective f := by
    rintro ⟨b, hb⟩
    obtain ⟨g, hg, hgb⟩ := hb
    exact ⟨⟨g, hg⟩, Subtype.ext hgb⟩
  have hc := generatedCore_map_surjective
    (naturalDualRepresentation.comp (radical U).subtype)
    (d.representation.comp (radicalImage U).subtype) f hf
    (LinearEquiv.refl (ZMod 2) V) (fun g v => (d.on_inner g.val v).symm) 2
  have hn := generatedCore_four_radical
    (by simp [X, BinaryLinear.OuterCyclic.Space] : Module.finrank (ZMod 2) X = 4)
    U hU (radical U) le_rfl
  simpa only [actorCore, hn, LinearEquiv.refl_toLinearMap, Submodule.map_id] using hc.symm

/-- The whole dimension/core calculation for every two-space radical in degree four. -/
theorem radicalImage_parameters (U : Submodule (ZMod 2) X)
    (hU : Module.finrank (ZMod 2) U = 2) :
    Module.finrank (ZMod 2) (actorFixed d (radicalImage U)) = 4 ∧
      actorCore d (radicalImage U) 2 = ⊤ := by
  have hUb : U ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hU
    contradiction
  have hUt : U ≠ ⊤ := by
    intro he
    rw [he, finrank_top] at hU
    simp [X, BinaryLinear.OuterCyclic.Space] at hU
  refine ⟨?_, actorCore_radicalImage d U hU⟩
  rw [actorFixed_radicalImage d U hUb hUt, finrank_prod_dualAnnihilator]
  simp [BinaryLinear.OuterCyclic.Space]

end BinaryNaturalDual.FourActors
