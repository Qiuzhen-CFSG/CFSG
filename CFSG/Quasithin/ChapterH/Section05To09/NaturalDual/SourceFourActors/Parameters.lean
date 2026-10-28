module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFourActors.Catalogue
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFourActors.Outer
/-!
# Source fixed spaces and generated cores for H.9.3(4–6)

All actors lie in the original source group and act through its original
representation. The simultaneous Sylow-compatible comparisons transfer the
three coordinate calculations, including the unique natural transvection
in A₁ and the literal diagonal description for every outer element of A₂.
The generated cores are identified with E.3.30, not merely with subspaces
of the same dimension.

Source: Aschbacher–Smith, H.9.3(4–6), printed pp.391–392.
-/

@[expose] public section
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceFourActors
variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup 4 M V) (T : Sylow 2 M)

theorem naturalFixed_map (H : Subgroup M) (hH : H ≤ componentLayer M) :
    (S.naturalFixed H).map (naturalCoordinates S T).toLinearMap =
      BinaryNaturalDual.FourActors.naturalFixed (H.map (group S T).toMonoidHom) := by
  ext x
  obtain ⟨u,rfl⟩ := (naturalCoordinates S T).surjective x
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
    BinaryNaturalDual.FourActors.mem_naturalFixed]
  constructor
  · intro hu g hg
    obtain ⟨a,ha,he⟩ := hg
    have hv := congrArg (coordinates S T) (hu ⟨a,ha⟩)
    change coordinates S T (S.representation a u) = coordinates S T u at hv
    rw [equivariant, natural_marking, show group S T a = MulAut.conj g from he,
      CoordinateAction.on_inner, naturalDualRepresentation_apply] at hv
    exact congrArg Prod.fst hv
  · intro hu a
    have hi := (group_inner_iff S T a).mpr (hH a.property)
    obtain ⟨g,hg⟩ := hi
    apply (coordinates S T).injective
    change coordinates S T (S.representation a u) = coordinates S T u
    rw [equivariant, natural_marking, ← hg, CoordinateAction.on_inner,
      naturalDualRepresentation_apply, map_zero, hu g]
    rw [hg]
    exact Subgroup.mem_map_of_mem _ a.property

theorem A0_parameters :
    Module.finrank (ZMod 2) (S.fixed (A0 S T)) = 4 ∧ core S (A0 S T) 2 = ⊤ ∧
    ChapterE.dualGeneratedCore (multiplicativeAction (S.representation.comp (A0 S T).subtype)) 2 = ⊤ := by
  have hp := BinaryNaturalDual.FourActors.Parameters.A0_parameters
    (AutomorphismModel.coordinateAction S.degree)
  have hdim : Module.finrank (ZMod 2) (S.fixed (A0 S T)) = 4 := by
    rw [fixed_finrank S T, actor_map]; exact hp.1
  have hc : core S (A0 S T) 2 = ⊤ := by
    apply (Submodule.map_injective_of_injective (coordinates S T).injective)
    rw [core_map, actor_map]
    change BinaryNaturalDual.FourActors.actorCore _ BinaryNaturalDual.FourActors.A0 2 = _
    rw [hp.2]
    simp
  refine ⟨hdim,hc,?_⟩
  rw [← generatedCore_subgroup]
  change subgroupOrderIso (core S (A0 S T) 2) = ⊤
  rw [hc, OrderIso.map_top]

theorem r_mem_B1 : r S T ∈ B1 S T := by
  have h : group S T (r S T) ∈ (B1 S T).map (group S T).toMonoidHom := by
    rw [r_map, B1_map]; exact BinaryNaturalDual.FourActors.r_mem_B1
  simpa only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] using h

theorem A1_transvection :
    ∃ l : componentLayer M, (l : M) = r S T ∧ BinaryLinear.OuterCyclic.IsTransvection (S.layer l) ∧
      ∀ h : componentLayer M, (h : M) ∈ A1 S T →
        BinaryLinear.OuterCyclic.IsTransvection (S.layer h) → h = l := by
  obtain ⟨g,hg,ht,hu⟩ := BinaryNaturalDual.FourActors.Parameters.A1_transvection
  let l := (layerCoordinates S T).symm g
  have hl : (l : M) = r S T := by
    apply (group S T).injective
    rw [group_layer, r_map]
    exact ((congrArg MulAut.conj ((layerCoordinates S T).apply_symm_apply g)).trans hg)
  refine ⟨l,hl,(transvection_marking S T l).mp ?_,?_⟩
  · simpa only [l, MulEquiv.apply_symm_apply] using ht
  · intro h hh hht
    apply (layerCoordinates S T).injective
    rw [show layerCoordinates S T l = g from (layerCoordinates S T).apply_symm_apply g]
    apply hu
    · rw [← group_layer]
      exact hh
    · exact (transvection_marking S T h).mpr hht

theorem A1_parameters :
    Module.finrank (ZMod 2) (S.fixed (A1 S T)) = 1 ∧
    core S (A1 S T) 2 = elementFixed S (r S T) ∧
    Module.finrank (ZMod 2) (elementFixed S (r S T)) = 6 ∧
    ChapterE.dualGeneratedCore (multiplicativeAction (S.representation.comp (A1 S T).subtype)) 2 =
      subgroupOrderIso (elementFixed S (r S T)) := by
  have hp := BinaryNaturalDual.FourActors.Parameters.A1_parameters
    (AutomorphismModel.coordinateAction S.degree)
  have hc : core S (A1 S T) 2 = elementFixed S (r S T) := by
    apply (Submodule.map_injective_of_injective (coordinates S T).injective)
    rw [core_map, actor_map, elementFixed_map, r_map]
    exact hp.2.1
  refine ⟨?_,hc,?_,?_⟩
  · rw [fixed_finrank S T, actor_map]; exact hp.1
  · rw [elementFixed_finrank S T, r_map]; exact hp.2.2
  · rw [← generatedCore_subgroup]; exact congrArg subgroupOrderIso hc

theorem A2_parameters (a : M) (ha : a ∈ A2 S T) (haB : a ∉ B2 S T) :
    (∀ v : V, v ∈ S.fixed (A2 S T) ↔ ∃ u ∈ S.naturalFixed (B2 S T),
      (u : V) + S.representation a u = v) ∧
    Module.finrank (ZMod 2) (S.fixed (A2 S T)) = 2 ∧
    core S (A2 S T) 2 = S.fixed (B2 S T) ⊔ elementFixed S a ∧
    Module.finrank (ZMod 2) ↥(S.fixed (B2 S T) ⊔ elementFixed S a) = 6 ∧
    ChapterE.dualGeneratedCore (multiplicativeAction (S.representation.comp (A2 S T).subtype)) 2 =
      subgroupOrderIso (S.fixed (B2 S T) ⊔ elementFixed S a) := by
  have ha' : group S T a ∈ BinaryNaturalDual.FourActors.A2 := ha
  have haB' : group S T a ∉ BinaryNaturalDual.FourActors.B2 := by
    intro h; exact haB ⟨ha,(group_inner_iff S T a).mp h.2⟩
  have hp := BinaryNaturalDual.FourActors.Parameters.A2_parameters
    (AutomorphismModel.coordinateAction S.degree) ha' haB'
  have hn : (S.naturalFixed (B2 S T)).map (naturalCoordinates S T).toLinearMap =
      BinaryNaturalDual.FourActors.naturalFixed BinaryNaturalDual.FourActors.B2 := by
    rw [naturalFixed_map S T (B2 S T) inf_le_right, B2_map]
  have hc : core S (A2 S T) 2 = S.fixed (B2 S T) ⊔ elementFixed S a := by
    apply (Submodule.map_injective_of_injective (coordinates S T).injective)
    rw [core_map, actor_map, Submodule.map_sup, fixed_map, B2_map, elementFixed_map]
    exact hp.2.2.1
  refine ⟨?_,?_,hc,?_,?_⟩
  · intro v
    have hv : v ∈ S.fixed (A2 S T) ↔ coordinates S T v ∈
        BinaryNaturalDual.FourActors.actorFixed (AutomorphismModel.coordinateAction S.degree)
          BinaryNaturalDual.FourActors.A2 := by
      change v ∈ S.fixed (actor S T 2) ↔ coordinates S T v ∈
        BinaryNaturalDual.FourActors.actorFixed _ (BinaryNaturalDual.FourActors.PermutationCatalogue.actor 2)
      rw [← actor_map S T 2, ← fixed_map, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
    rw [hv, hp.1]
    constructor
    · rintro ⟨x,hx,hv⟩
      rw [← hn] at hx
      obtain ⟨u,hu,rfl⟩ := hx
      refine ⟨u,hu,(coordinates S T).injective ?_⟩
      simpa only [map_add, equivariant, natural_marking, LinearEquiv.coe_coe] using hv
    · rintro ⟨u,hu,rfl⟩
      refine ⟨naturalCoordinates S T u, ?_, ?_⟩
      · rw [← hn]; exact Submodule.mem_map_of_mem hu
      · simp only [map_add, equivariant, natural_marking]
  · rw [fixed_finrank S T, actor_map]; exact hp.2.1
  · rw [← hc]
    have hd := (Submodule.equivMapOfInjective (coordinates S T).toLinearMap
      (coordinates S T).injective (core S (A2 S T) 2)).finrank_eq
    rw [core_map, actor_map] at hd
    exact hd.trans hp.2.2.2
  · rw [← generatedCore_subgroup]; exact congrArg subgroupOrderIso hc
end CFSG.Quasithin.ChapterH.NaturalDual.SourceFourActors
