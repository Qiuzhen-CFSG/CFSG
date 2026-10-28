module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.KernelCover.FixedLift
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.Extensions.WholeCommutator
public import Theory.Representation.BinaryGroupAction.Subrepresentation

/-!
# The kernel equals its component commutator

Quotienting a perfect module by the component commutator of its kernel
gives a perfect central cover of its natural quotient. A Sylow-fixed vector
outside the kernel excludes the augmentation cover, so the central-cover
map is injective and the kernel already equals its component commutator.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.KernelCover
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction
open OffenderModels OffenderModels.StrongSections.Extensions
variable {H U : Type*} [Group H] [Finite H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- A Sylow-fixed lift outside a natural quotient kernel forces that kernel
to equal its component commutator, with both subrepresentations literal. -/
theorem componentCommutator_eq_of_fixed_lift
    (ρ : Representation (ZMod 2) H U) (N : Subrepresentation ρ)
    (eH : H ≃* Equiv.Perm (Fin 8)) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hQ : IsEightNatural N.quotientRepresentation eH)
    (hgen : subspaceCommutator ρ ⊤ K = ⊤)
    (P : Sylow 2 H) (x : U) (hx : ∀ g ∈ (P : Subgroup H), ρ g x = x)
    (hxN : x ∉ N.toSubmodule) : componentCommutator ρ N eH K hK = N := by
  let J := componentCommutator ρ N eH K hK
  have hJN : J.toSubmodule ≤ N.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,hv,rfl⟩
    exact N.toSubmodule.sub_mem (N.apply_mem_toSubmodule g hv) hv
  obtain ⟨e, he⟩ := hQ
  let q : U →ₗ[ZMod 2] natural (Fin 8) := e.toLinearMap.comp N.toSubmodule.mkQ
  have hq (u : U) : q u = 0 ↔ u ∈ N.toSubmodule := by
    change e (N.toSubmodule.mkQ u) = 0 ↔ _
    rw [e.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero _
  let p : (U ⧸ J.toSubmodule) →ₗ[ZMod 2] natural (Fin 8) :=
    J.toSubmodule.liftQ q (fun u hu => (hq u).mpr (hJN hu))
  have hp (g : H) (v : U ⧸ J.toSubmodule) :
      p (J.quotientRepresentation g v) = naturalRepresentation (Fin 8) (eH g) (p v) := by
    induction v using Submodule.Quotient.induction_on with
    | _ u => exact he g (N.toSubmodule.mkQ u)
  have hsur : Function.Surjective p := by
    intro v
    obtain ⟨u, hu⟩ := N.toSubmodule.mkQ_surjective (e.symm v)
    refine ⟨J.toSubmodule.mkQ u, ?_⟩
    change e (N.toSubmodule.mkQ u) = v
    rw [hu, e.apply_symm_apply]
  have hker : p.ker ≤ fixedSpace J.quotientRepresentation K := by
    intro v hv
    induction v using Submodule.Quotient.induction_on with
    | _ u =>
      have hu : u ∈ N.toSubmodule := (hq u).mp hv
      intro k
      apply (Submodule.Quotient.eq J.toSubmodule).mpr
      exact Submodule.subset_span ⟨k,k.property,u,hu,rfl⟩
  have hgenJ : subspaceCommutator J.quotientRepresentation ⊤ K = ⊤ := by
    have hh := subspaceCommutator_map_embedding J.quotientRepresentation ρ
      (MonoidHom.id H) J.toSubmodule.mkQ (fun _ _ => rfl) K ⊤
    simpa only [Subgroup.map_id,Submodule.map_top,Submodule.range_mkQ,hgen] using hh
  have hmodel := naturalOrCover_of_central_cover J.quotientRepresentation eH K hK
    p hp hsur hker hgenJ
  have hi := injective_of_naturalOrCover_fixed_lift J.quotientRepresentation eH hmodel
    p hp hsur P (J.toSubmodule.mkQ x)
    (fun g hg => congrArg J.toSubmodule.mkQ (hx g hg)) (fun hz => hxN ((hq x).mp hz))
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm hJN
  intro n hn
  apply (Submodule.Quotient.mk_eq_zero J.toSubmodule).mp
  apply hi
  exact ((hq n).mpr hn).trans (map_zero p).symm

omit [Finite H] [FiniteDimensional (ZMod 2) U] in
/-- In the intrinsic kernel coordinates, its component commutator is the
whole space once the preceding ambient equality holds. -/
theorem intrinsic_commutator_eq_top
    (ρ : Representation (ZMod 2) H U) (N : Subrepresentation ρ)
    (eH : H ≃* Equiv.Perm (Fin 8)) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (he : componentCommutator ρ N eH K hK = N) :
    subspaceCommutator N.toRepresentation ⊤ K = ⊤ := by
  apply Submodule.map_injective_of_injective N.toSubmodule.subtype_injective
  rw [BinaryGroupAction.subrepresentation_moved_map,Submodule.map_top,Submodule.range_subtype]
  exact congrArg Subrepresentation.toSubmodule he

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.KernelCover
