module

public import Theory.Representation.BinaryPermutationEightCover.Universal
public import Theory.Representation.BinaryPermutationEightCover.PairGeneration

/-!
# Marked augmentation covers and local generation for A₈

The universal augmentation cover surjects onto any perfect central cover
of the natural module, preserving the supplied actor marking and the
original map onto the natural module. A conjugate pair stabilizer generates
the augmentation core, hence every such cover. No splitting or dimension
of the covered module is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.1.5–6,
printed p.408, and the application in 13.5.21(6), printed p.924.
-/

@[expose] public section
open Subgroup Representation Representation.OneCohomology Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace BinaryPermutation.EightCover
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- The augmentation cover maps onto a perfect central cover under the given actor marking. -/
theorem core_quotient_of_marked_cover
    (ρ : Representation (ZMod 2) G U) (B : Subgroup G)
    (e : B ≃* alternatingGroup (Fin 8))
    (p : U →ₗ[ZMod 2] natural (Fin 8))
    (hp : ∀ b : B, ∀ u, p (ρ b.val u) =
      alternatingNaturalRepresentation (Fin 8) (e b) (p u))
    (hsur : Function.Surjective p)
    (hker : p.ker ≤ fixedSpace ρ B)
    (hgen : subspaceCommutator ρ ⊤ B = ⊤) :
    ∃ f : core (Fin 8) →ₗ[ZMod 2] U, Function.Surjective f ∧
      (∀ b : B, ∀ v, f (alternatingCoreRepresentation (Fin 8) (e b) v) =
        ρ b.val (f v)) ∧
      ∀ v, p (f v) = coreToNatural (Fin 8) v := by
  let a := B.subtype.comp e.symm.toMonoidHom
  let σ : Representation (ZMod 2) (alternatingGroup (Fin 8)) U := ρ.comp a
  let P : σ.IntertwiningMap (alternatingNaturalRepresentation (Fin 8)) :=
    p.intertwiningMap_of_isIntertwiningMap _ _ (fun g u => by
      change p (ρ (e.symm g).val u) = _
      rw [hp, e.apply_symm_apply])
  have hc : Coinvariants.ker σ = subspaceCommutator ρ ⊤ B := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨g, u⟩, rfl⟩
      exact Submodule.subset_span ⟨(e.symm g).val, (e.symm g).property,
        u, Submodule.mem_top, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, u, _, rfl⟩
      have hh : σ (e ⟨g, hg⟩) u = ρ g u := by
        change ρ (e.symm (e ⟨g, hg⟩)).val u = ρ g u
        rw [e.symm_apply_apply]
      rw [← hh]
      exact Coinvariants.sub_mem_ker (e ⟨g, hg⟩) u
  have hP : IsCover P := ⟨hsur, fun u hu g => hker hu (e.symm g), hc.trans hgen⟩
  obtain ⟨f, hf, hfa, hpf⟩ := core_quotient_of_alternating_cover σ P hP
  refine ⟨f, hf, ?_, hpf⟩
  intro b v
  simpa only [σ, a, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, e.symm_apply_apply, Subgroup.coe_subtype] using hfa (e b) v

omit [FiniteDimensional (ZMod 2) U] in
/-- A marked pair stabilizer generates every quotient of the augmentation cover. -/
theorem generation_of_core_surjection
    (ρ : Representation (ZMod 2) G U) (B J : Subgroup G)
    (e : B ≃* alternatingGroup (Fin 8))
    (f : core (Fin 8) →ₗ[ZMod 2] U) (hf : Function.Surjective f)
    (he : ∀ b : B, ∀ v, f (alternatingCoreRepresentation (Fin 8) (e b) v) =
      ρ b.val (f v))
    (g : alternatingGroup (Fin 8))
    (hJ : (J.subgroupOf B).map e.toMonoidHom =
      (pairStabilizer.subgroupOf (alternatingGroup (Fin 8))).map
        (MulAut.conj g).toMonoidHom) :
    subspaceCommutator ρ ⊤ J = ⊤ := by
  let C := subspaceCommutator ρ ⊤ J
  have hc : subspaceCommutator (alternatingCoreRepresentation (Fin 8)) ⊤
      ((pairStabilizer.subgroupOf (alternatingGroup (Fin 8))).map
        (MulAut.conj g).toMonoidHom) ≤ C.comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, _, rfl⟩
    rw [← hJ] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    change f (alternatingCoreRepresentation (Fin 8) (e b) v - v) ∈ C
    rw [map_sub, he]
    exact Submodule.subset_span ⟨b.val, hb, f v, Submodule.mem_top, rfl⟩
  rw [core_pairStabilizer_conjugate_generated] at hc
  apply top_unique
  intro u _
  obtain ⟨v, rfl⟩ := hf u
  exact hc (Submodule.mem_top : v ∈ ⊤)

end BinaryPermutation.EightCover
