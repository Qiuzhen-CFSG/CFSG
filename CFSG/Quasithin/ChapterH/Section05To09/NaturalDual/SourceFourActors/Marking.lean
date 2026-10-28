module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceSylowMarking
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.FourActors
/-!
# Sylow-compatible source coordinates for H.9.3

The constructed source model is adjusted by an inner conjugator taking the
specified Sylow to the marked tree Sylow. If an initial Sylow conjugator is
outer, multiplying it by the tree's transposition makes it inner. Consequently
the natural and dual summands retain their markings. The group, vector and
natural-space comparisons below all use this same adjustment. Fixed spaces
and the actual corank-generated core transport equivariantly.

Source: Aschbacher–Smith, H.9.3 and its proof, printed pp.391–392.
-/

@[expose] public section
open BinaryNaturalDual BinaryNaturalDual.FourActors BinaryNaturalDual.ModelOrbits
open BinaryNaturalDual.FourActors.PermutationCatalogue
open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceFourActors
private theorem inner_sylow_conjugator (T : Sylow 2 BinaryNaturalDual.FourActors.M) :
    ∃ g : G, (T : Subgroup _).map (MulAut.conj (MulAut.conj g)).toMonoidHom = T0 := by
  obtain ⟨a, hT, _⟩ := FourActors.exists_conj_elementaryThompson_eq_A0 T
  have ht : transposition ∈ (T0 : Subgroup _) := by
    change permutationEquiv transposition ∈ Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeGroup
    rw [permutationEquiv_transposition]
    exact Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeGenerator_mem 0
  have hnorm : (T0 : Subgroup _).map (MulAut.conj transposition).toMonoidHom = T0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ht)
  by_cases hi : a ∈ BinaryNaturalDual.FourActors.inner
  · obtain ⟨g, rfl⟩ := hi
    exact ⟨g, hT⟩
  · have hb : transposition * a ∈ BinaryNaturalDual.FourActors.inner :=
      (Subgroup.mul_mem_iff_of_index_two inner_index).mpr
        (iff_of_false transposition_outer hi)
    obtain ⟨g, hg⟩ := hb
    refine ⟨g, ?_⟩
    rw [hg, map_mul]
    change (T : Subgroup _).map
      ((MulAut.conj transposition).toMonoidHom.comp (MulAut.conj a).toMonoidHom) = _
    rw [← Subgroup.map_map, hT, hnorm]

variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup 4 M V) (T : Sylow 2 M)
noncomputable def adjustment : G :=
  Classical.choose (show ∃ g : G, (S.coordinateSylow T : Subgroup _).map
    (MulAut.conj (MulAut.conj g)).toMonoidHom = T0 from by
      exact inner_sylow_conjugator (S.coordinateSylow T))
noncomputable def group : M ≃* BinaryNaturalDual.FourActors.M :=
  S.model.group.trans (MulAut.conj (MulAut.conj (adjustment S T)))
noncomputable def coordinates : V ≃ₗ[ZMod 2] CoordinateSpace 4 :=
  S.model.coordinates.trans (action (AutomorphismModel.coordinateAction S.degree)
    (MulAut.conj (adjustment S T)))
noncomputable def naturalCoordinates : S.natural ≃ₗ[ZMod 2] X :=
  S.naturalCoordinates.trans (adjustment S T)
noncomputable def layerCoordinates : componentLayer M ≃* G :=
  S.layer.trans (MulAut.conj (adjustment S T))

theorem group_sylow : (T : Subgroup M).map (group S T).toMonoidHom = T0 := by
  change (T : Subgroup M).map
    ((MulAut.conj (MulAut.conj (adjustment S T))).toMonoidHom.comp S.model.group.toMonoidHom) = _
  rw [← Subgroup.map_map]
  exact Classical.choose_spec (inner_sylow_conjugator (S.coordinateSylow T))

theorem group_layer (l : componentLayer M) :
    group S T l = MulAut.conj (layerCoordinates S T l) := by
  change MulAut.conj (MulAut.conj (adjustment S T)) (S.model.group l) = _
  rw [S.model.on_layer]
  ext x : 1
  simp [layerCoordinates, MulAut.conj_apply]

theorem group_inner_iff (m : M) : group S T m ∈ BinaryNaturalDual.FourActors.inner ↔ m ∈ componentLayer M := by
  change MulAut.conj (adjustment S T) * S.model.group m * (MulAut.conj (adjustment S T))⁻¹ ∈ BinaryNaturalDual.FourActors.inner ↔ _
  have hc : MulAut.conj (adjustment S T) ∈ BinaryNaturalDual.FourActors.inner := ⟨_, rfl⟩
  rw [BinaryNaturalDual.FourActors.inner.mul_mem_cancel_right (BinaryNaturalDual.FourActors.inner.inv_mem hc),
    BinaryNaturalDual.FourActors.inner.mul_mem_cancel_left hc]
  exact S.model.inner_iff m

theorem equivariant (m : M) (v : V) :
    coordinates S T (S.representation m v) =
      (AutomorphismModel.coordinateAction S.degree).representation (group S T m) (coordinates S T v) := by
  let d := AutomorphismModel.coordinateAction S.degree
  change d.representation (MulAut.conj (adjustment S T)) (S.model.coordinates (S.representation m v)) =
    d.representation (MulAut.conj (adjustment S T) * S.model.group m * (MulAut.conj (adjustment S T))⁻¹)
      (d.representation (MulAut.conj (adjustment S T)) (S.model.coordinates v))
  rw [S.model.equivariant, ← Module.End.mul_apply, ← map_mul,
    ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

theorem natural_marking (v : S.natural) :
    coordinates S T v = (naturalCoordinates S T v, 0) := by
  change (AutomorphismModel.coordinateAction S.degree).representation
    (MulAut.conj (adjustment S T)) (S.model.coordinates v) = _
  rw [S.model.natural_marking, CoordinateAction.on_inner, naturalDualRepresentation_apply, map_zero]
  rfl

noncomputable def permutation : M ≃* Equiv.Perm (Fin 8) :=
  (group S T).trans permutationEquiv

theorem permutation_layer (l : componentLayer M) :
    permutation S T l = (linearAlternatingEquiv (layerCoordinates S T l)).val := by
  change permutationEquiv (group S T l) = _
  rw [group_layer, permutationEquiv_inner]

theorem layer_map : (componentLayer M).map (group S T).toMonoidHom =
    BinaryNaturalDual.FourActors.inner := by
  ext a
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact (group_inner_iff S T g).mpr hg
  · intro ha
    refine ⟨(group S T).symm a, (group_inner_iff S T _).mp ?_, (group S T).apply_symm_apply a⟩
    simpa using ha

theorem naturalSylow_map : (S.naturalSylowNormalizer T).map (group S T).toMonoidHom =
    (T0 : Subgroup _) ⊓ BinaryNaturalDual.FourActors.inner := by
  rw [SourceSetup.naturalSylowNormalizer, S.naturalNormalizer_eq_layer,
    Subgroup.map_inf _ _ _ (group S T).injective, group_sylow, layer_map]

noncomputable def pull (A : Subgroup BinaryNaturalDual.FourActors.M) : Subgroup M :=
  A.comap (group S T).toMonoidHom

@[simp] theorem pull_map (A : Subgroup BinaryNaturalDual.FourActors.M) :
    (pull S T A).map (group S T).toMonoidHom = A :=
  Subgroup.map_comap_eq_self_of_surjective (group S T).surjective A

@[simp] theorem mem_pull (A : Subgroup BinaryNaturalDual.FourActors.M) (a : M) :
    a ∈ pull S T A ↔ group S T a ∈ A := Iff.rfl

theorem pull_inner : pull S T BinaryNaturalDual.FourActors.inner = componentLayer M := by
  ext a; exact group_inner_iff S T a

theorem fixed_map (A : Subgroup M) :
    (S.fixed A).map (coordinates S T).toLinearMap =
      actorFixed (AutomorphismModel.coordinateAction S.degree) (A.map (group S T).toMonoidHom) :=
  Transport.fixed_map _ _ _ _ (equivariant S T) A

theorem fixed_finrank (A : Subgroup M) :
    Module.finrank (ZMod 2) (S.fixed A) =
      Module.finrank (ZMod 2)
        (actorFixed (AutomorphismModel.coordinateAction S.degree) (A.map (group S T).toMonoidHom)) :=
  Transport.fixed_finrank _ _ _ _ (equivariant S T) A

noncomputable def core (A : Subgroup M) (k : ℕ) : Submodule (ZMod 2) V :=
  generatedCore (S.representation.comp A.subtype) k

theorem core_map (A : Subgroup M) (k : ℕ) :
    (core S A k).map (coordinates S T).toLinearMap =
      actorCore (AutomorphismModel.coordinateAction S.degree) (A.map (group S T).toMonoidHom) k := by
  let := S.finite_group
  let : Finite BinaryNaturalDual.FourActors.M := Finite.of_equiv M (group S T).toEquiv
  let d := AutomorphismModel.coordinateAction S.degree
  let c := MulAut.conj (adjustment S T)
  have hc (b : BinaryNaturalDual.FourActors.M) (v : CoordinateSpace 4) :
      BinaryNaturalDual.FourActors.action d c (d.representation b v) =
        d.representation (MulAut.conj c b) (BinaryNaturalDual.FourActors.action d c v) := by
    change d.representation c (d.representation b v) =
      d.representation (c * b * c⁻¹) (d.representation c v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  rw [show (coordinates S T).toLinearMap =
    (BinaryNaturalDual.FourActors.action d c).toLinearMap.comp S.model.coordinates.toLinearMap from rfl,
    Submodule.map_comp, core, S.core_map]
  rw [Transport.core_map _ _ _ _ hc]
  change generatedCore (d.representation.comp
    ((A.map S.model.group.toMonoidHom).map (MulAut.conj c).toMonoidHom).subtype) k = _
  rw [Subgroup.map_map]
  rfl

noncomputable def elementFixed (a : M) : Submodule (ZMod 2) V :=
  BinaryNaturalDual.fixedSpace (S.linearAction a)

@[simp] theorem mem_elementFixed (a : M) (v : V) :
    v ∈ elementFixed S a ↔ S.representation a v = v :=
  BinaryNaturalDual.mem_fixedSpace _ _

theorem elementFixed_map (a : M) :
    (elementFixed S a).map (coordinates S T).toLinearMap =
      BinaryNaturalDual.fixedSpace (action (AutomorphismModel.coordinateAction S.degree) (group S T a)) := by
  ext w
  obtain ⟨v,rfl⟩ := (coordinates S T).surjective w
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_elementFixed,
    BinaryNaturalDual.mem_fixedSpace, action_apply, ← equivariant]
  exact (coordinates S T).injective.eq_iff.symm

theorem elementFixed_finrank (a : M) :
    Module.finrank (ZMod 2) (elementFixed S a) =
      Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace
        (action (AutomorphismModel.coordinateAction S.degree) (group S T a))) := by
  rw [← elementFixed_map S T]
  exact (Submodule.equivMapOfInjective _ (coordinates S T).injective _).finrank_eq

theorem natural_action (l : componentLayer M) (u : S.natural) :
    S.representation l u =
      ( (naturalCoordinates S T).symm (layerCoordinates S T l (naturalCoordinates S T u)) : V) := by
  apply S.model.coordinates.injective
  rw [S.model.equivariant, S.model.on_layer, CoordinateAction.on_inner,
    S.model.natural_marking, S.model.natural_marking, naturalDualRepresentation_apply, map_zero]
  congr 1
  simp [naturalCoordinates, layerCoordinates, MulAut.conj_apply]

theorem transvection_marking (l : componentLayer M) :
    BinaryLinear.OuterCyclic.IsTransvection (layerCoordinates S T l) ↔
      BinaryLinear.OuterCyclic.IsTransvection (S.layer l) :=
  BinaryLinear.OuterCyclic.isTransvection_map_linear (by decide)
    (MulAut.conj (adjustment S T)) (S.layer l)
end CFSG.Quasithin.ChapterH.NaturalDual.SourceFourActors
