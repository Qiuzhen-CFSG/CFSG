module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFourActors.Parameters
/-!
# The source geometric data in the continuation of H.9.3

The three source transvections have distinct natural axes, any two spanning
V₁. Every remaining nonidentity element of B₂ fixes the same two planes
on V₁ and V₂. Both planes have dimension two. Transport through the same
marked module comparison identifies each mixed fixed sum with the actual
commutator module [V,A₂], independently of the chosen outer element.

Source: Aschbacher–Smith, proof of H.9.3, printed p.392.
-/

@[expose] public section
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits Theory.GroupTheory
open Representation.RegularCyclicNormalClosure
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceFourActors
variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup 4 M V) (T : Sylow 2 M)
noncomputable def dualCoordinates : S.dual ≃ₗ[ZMod 2] Module.Dual (ZMod 2) BinaryNaturalDual.FourActors.X :=
  S.model.dualCoordinates.trans (adjustment S T).symm.dualMap

theorem dual_marking (u : S.dual) :
    coordinates S T u = (0, dualCoordinates S T u) := by
  change (AutomorphismModel.coordinateAction S.degree).representation
    (MulAut.conj (adjustment S T)) (S.model.coordinates u) = _
  rw [S.model.dual_marking, CoordinateAction.on_inner, naturalDualRepresentation_apply, map_zero]
  rfl

noncomputable def dualFixed (H : Subgroup M) : Submodule (ZMod 2) S.dual :=
  (S.fixed H).comap S.dual.subtype

noncomputable def naturalElementFixed (l : componentLayer M) : Submodule (ZMod 2) S.natural :=
  (elementFixed S l).comap S.natural.subtype
noncomputable def dualElementFixed (l : componentLayer M) : Submodule (ZMod 2) S.dual :=
  (elementFixed S l).comap S.dual.subtype

theorem naturalElementFixed_map (l : componentLayer M) :
    (naturalElementFixed S l).map (naturalCoordinates S T).toLinearMap =
      BinaryNaturalDual.fixedSpace (layerCoordinates S T l) := by
  ext x
  obtain ⟨u,rfl⟩ := (naturalCoordinates S T).surjective x
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, BinaryNaturalDual.mem_fixedSpace]
  rw [naturalElementFixed, Submodule.mem_comap, mem_elementFixed]
  change S.representation l (u : V) = (u : V) ↔ _
  rw [← (coordinates S T).injective.eq_iff, equivariant, natural_marking, group_layer,
    CoordinateAction.on_inner, naturalDualRepresentation_apply, map_zero]
  simp only [Prod.mk.injEq, and_true]

theorem dualElementFixed_map (l : componentLayer M) :
    (dualElementFixed S l).map (dualCoordinates S T).toLinearMap =
      BinaryNaturalDual.fixedSpace (layerCoordinates S T l).symm.dualMap := by
  ext x
  obtain ⟨u,rfl⟩ := (dualCoordinates S T).surjective x
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, BinaryNaturalDual.mem_fixedSpace]
  rw [dualElementFixed, Submodule.mem_comap, mem_elementFixed]
  change S.representation l (u : V) = (u : V) ↔ _
  rw [← (coordinates S T).injective.eq_iff, equivariant, dual_marking, group_layer,
    CoordinateAction.on_inner, naturalDualRepresentation_apply, map_zero]
  simp only [Prod.mk.injEq, true_and]

theorem dualFixed_map (H : Subgroup M) (hH : H ≤ componentLayer M) :
    (dualFixed S H).map (dualCoordinates S T).toLinearMap =
      BinaryNaturalDual.FourActors.A2Module.dualFixed (H.map (group S T).toMonoidHom) := by
  ext x
  obtain ⟨u,rfl⟩ := (dualCoordinates S T).surjective x
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
    BinaryNaturalDual.FourActors.A2Module.mem_dualFixed]
  constructor
  · intro hu g hg
    obtain ⟨a,ha,he⟩ := hg
    have hv := congrArg (coordinates S T) (hu ⟨a,ha⟩)
    change coordinates S T (S.representation a u) = coordinates S T u at hv
    rw [equivariant, dual_marking, show group S T a = MulAut.conj g from he,
      CoordinateAction.on_inner, naturalDualRepresentation_apply] at hv
    exact congrArg Prod.snd hv
  · intro hu a
    have hi := (group_inner_iff S T a).mpr (hH a.property)
    obtain ⟨g,hg⟩ := hi
    apply (coordinates S T).injective
    change coordinates S T (S.representation a u) = coordinates S T u
    rw [equivariant, dual_marking, ← hg, CoordinateAction.on_inner,
      naturalDualRepresentation_apply, map_zero, hu g]
    rw [hg]
    exact Subgroup.mem_map_of_mem _ a.property

/-- Three actual elements of the original layer; their fixed hyperplanes are the axes. -/
noncomputable def axis (i : Fin 3) : componentLayer M :=
  (layerCoordinates S T).symm (BinaryNaturalDual.FourActors.A2Module.axisLinear i)

@[simp] theorem axis_map (i : Fin 3) :
    layerCoordinates S T (axis S T i) = BinaryNaturalDual.FourActors.A2Module.axisLinear i :=
  (layerCoordinates S T).apply_symm_apply _

theorem A2_three_transvections :
    (∀ i : Fin 3, (axis S T i : M) ∈ B2 S T ∧
      BinaryLinear.OuterCyclic.IsTransvection (S.layer (axis S T i)) ∧
      Module.finrank (ZMod 2) (naturalElementFixed S (axis S T i)) = 3) ∧
    Function.Injective (fun i : Fin 3 => naturalElementFixed S (axis S T i)) ∧
    (∀ l : componentLayer M, (l : M) ∈ B2 S T →
      (BinaryLinear.OuterCyclic.IsTransvection (S.layer l) ↔ ∃ i : Fin 3, l = axis S T i)) := by
  have hp := BinaryNaturalDual.FourActors.Parameters.A2_three_transvections
  refine ⟨?_,?_,?_⟩
  · intro i
    have hi : group S T (axis S T i) ∈ (B2 S T).map (group S T).toMonoidHom := by
      rw [group_layer, axis_map, B2_map]; exact (hp.1 i).1
    refine ⟨?_,?_,?_⟩
    · simpa only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] using hi
    · apply (transvection_marking S T _).mp
      rw [axis_map]; exact (hp.1 i).2.1
    · have he := (Submodule.equivMapOfInjective (naturalCoordinates S T).toLinearMap
        (naturalCoordinates S T).injective (naturalElementFixed S (axis S T i))).finrank_eq
      rw [naturalElementFixed_map, axis_map] at he
      exact he.trans (hp.1 i).2.2
  · intro i j hij
    apply hp.2.1
    have he := congrArg (Submodule.map (naturalCoordinates S T).toLinearMap) hij
    simpa only [naturalElementFixed_map, axis_map] using he
  · intro l hl
    rw [← transvection_marking S T l]
    have hm : layerCoordinates S T l ∈ BinaryNaturalDual.FourActors.innerPreimage BinaryNaturalDual.FourActors.B2 := by
      change MulAut.conj (layerCoordinates S T l) ∈ BinaryNaturalDual.FourActors.B2
      rw [← group_layer, ← B2_map S T]
      exact Subgroup.mem_map_of_mem _ hl
    rw [hp.2.2 _ hm]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨i, (layerCoordinates S T).injective (hi.trans (axis_map S T i).symm)⟩
    · rintro ⟨i,rfl⟩; exact ⟨i, axis_map S T i⟩

theorem A2_axes_span {i j : Fin 3} (hij : i ≠ j) :
    naturalElementFixed S (axis S T i) ⊔ naturalElementFixed S (axis S T j) = ⊤ := by
  apply Submodule.map_injective_of_injective (naturalCoordinates S T).injective
  rw [Submodule.map_sup, naturalElementFixed_map, naturalElementFixed_map, axis_map, axis_map,
    BinaryNaturalDual.FourActors.Parameters.A2_axes_span hij]
  simp

theorem A2_fixed_planes :
    Module.finrank (ZMod 2) (S.naturalFixed (B2 S T)) = 2 ∧
    Module.finrank (ZMod 2) (dualFixed S (B2 S T)) = 2 := by
  have hp := BinaryNaturalDual.FourActors.Parameters.A2_fixed_planes
  constructor
  · have he := (Submodule.equivMapOfInjective (naturalCoordinates S T).toLinearMap
      (naturalCoordinates S T).injective (S.naturalFixed (B2 S T))).finrank_eq
    rw [naturalFixed_map S T (B2 S T) inf_le_right, B2_map] at he
    exact he.trans hp.1
  · have he := (Submodule.equivMapOfInjective (dualCoordinates S T).toLinearMap
      (dualCoordinates S T).injective (dualFixed S (B2 S T))).finrank_eq
    rw [dualFixed_map S T (B2 S T) inf_le_right, B2_map] at he
    exact he.trans hp.2.2

theorem A2_other_fixed (l : componentLayer M) (hl : (l : M) ∈ B2 S T) (h1 : l ≠ 1)
    (ht : ¬ BinaryLinear.OuterCyclic.IsTransvection (S.layer l)) :
    naturalElementFixed S l = S.naturalFixed (B2 S T) ∧
      dualElementFixed S l = dualFixed S (B2 S T) := by
  have hm : layerCoordinates S T l ∈ BinaryNaturalDual.FourActors.innerPreimage BinaryNaturalDual.FourActors.B2 := by
    change MulAut.conj (layerCoordinates S T l) ∈ BinaryNaturalDual.FourActors.B2
    rw [← group_layer, ← B2_map S T]
    exact Subgroup.mem_map_of_mem _ hl
  have hp := BinaryNaturalDual.FourActors.Parameters.A2_other_fixed hm
    (fun h => h1 ((layerCoordinates S T).map_eq_one_iff.mp h))
    (fun h => ht ((transvection_marking S T l).mp h))
  constructor
  · apply Submodule.map_injective_of_injective (naturalCoordinates S T).injective
    rw [naturalElementFixed_map, naturalFixed_map S T (B2 S T) inf_le_right, B2_map]
    exact hp.1
  · apply Submodule.map_injective_of_injective (dualCoordinates S T).injective
    rw [dualElementFixed_map, dualFixed_map S T (B2 S T) inf_le_right, B2_map]
    exact hp.2

private theorem displacement_eq_coinvariants {D W : Type*} [Group D] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W) (A : Subgroup D) :
    displacementSpan ρ A ⊤ = Representation.Coinvariants.ker (ρ.comp A.subtype) := by
  unfold displacementSpan Representation.Coinvariants.ker
  congr 1
  ext w
  constructor
  · rintro ⟨a,ha,v,_,rfl⟩
    exact ⟨(⟨a,ha⟩,v),rfl⟩
  · rintro ⟨⟨a,v⟩,rfl⟩
    exact ⟨a,a.property,v,Submodule.mem_top,rfl⟩

theorem A2_core_eq_commutator : core S (A2 S T) 2 =
    Representation.Coinvariants.ker (S.representation.comp (A2 S T).subtype) := by
  apply Submodule.map_injective_of_injective (coordinates S T).injective
  rw [core_map, Transport.commutator_map _ _ _ _ (equivariant S T), actor_map]
  exact (BinaryNaturalDual.FourActors.Parameters.A2_core_eq_displacement
    (AutomorphismModel.coordinateAction S.degree)).trans (displacement_eq_coinvariants _ _)

theorem A2_mixed_eq_commutator (a : M) (ha : a ∈ A2 S T) (haB : a ∉ B2 S T) :
    S.fixed (B2 S T) ⊔ elementFixed S a =
      Representation.Coinvariants.ker (S.representation.comp (A2 S T).subtype) :=
  (A2_parameters S T a ha haB).2.2.1.symm.trans (A2_core_eq_commutator S T)

theorem A2_mixed_independent (a b : M) (ha : a ∈ A2 S T) (haB : a ∉ B2 S T)
    (hb : b ∈ A2 S T) (hbB : b ∉ B2 S T) :
    S.fixed (B2 S T) ⊔ elementFixed S a = S.fixed (B2 S T) ⊔ elementFixed S b :=
  (A2_mixed_eq_commutator S T a ha haB).trans (A2_mixed_eq_commutator S T b hb hbB).symm
end CFSG.Quasithin.ChapterH.NaturalDual.SourceFourActors
