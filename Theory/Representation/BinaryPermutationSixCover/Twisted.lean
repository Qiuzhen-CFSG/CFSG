module
public import Theory.Representation.BinaryPermutationSixCover.Universal
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.ResidualMovedGeneration
public import Theory.Representation.BinaryOffender.MovedDimension
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# A marked universal cover of a natural symmetric-six quotient

An arbitrary automorphism of S6 preserves its alternating component. Restricting
through its inverse therefore gives the universal five-dimensional augmentation
cover, retaining the original natural quotient map and marking. Only alternating
equivariance is asserted; this is enough for the kernel displacement consumer.

Source: Aschbacher--Smith I.1.5–6; MS93 (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology Representation.BinaryOffender
namespace BinaryPermutation.SixCover
local notation "S6" => Equiv.Perm (Fin 6)
local notation "A6" => alternatingGroup (Fin 6)

theorem map_alternating_six (e : S6 ≃* S6) : (A6).map e.toMonoidHom = A6 := by
  rw [←alternatingGroup.commutator_perm_eq (by simp : 5 ≤ Nat.card (Fin 6)),
    map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective, commutator_def]

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

theorem core_surjection_of_twisted_cover
    (ρ : Representation (ZMod 2) S6 U) (e : S6 ≃* S6)
    (p : U →ₗ[ZMod 2] natural (Fin 6)) (hsur : Function.Surjective p)
    (hp : ∀ g u, p (ρ g u) = naturalRepresentation (Fin 6) (e g) (p u))
    (hker : p.ker ≤ fixedSpace ρ A6)
    (hgen : subspaceCommutator ρ ⊤ A6 = ⊤) :
    ∃ f : core (Fin 6) →ₗ[ZMod 2] U, Function.Surjective f ∧
      (∀ g : S6, g ∈ A6 → ∀ v,
        f (coreRepresentation (Fin 6) (e g) v) = ρ g (f v)) ∧
      ∀ v, p (f v) = coreToNatural (Fin 6) v := by
  let a : A6 →* S6 := e.symm.toMonoidHom.comp (A6).subtype
  have ha (g : A6) : a g ∈ A6 := by
    exact (map_alternating_six e.symm).le (mem_map_of_mem e.symm.toMonoidHom g.property)
  have hr : (⊤ : Subgroup A6).map a = A6 := by
    rw [←MonoidHom.range_eq_map]
    apply le_antisymm
    · rintro _ ⟨g,rfl⟩
      exact ha g
    · intro g hg
      have hg' : e g ∈ A6 := by
        change e.toMonoidHom g ∈ A6
        simpa only [map_alternating_six e] using
          (mem_map_of_mem e.toMonoidHom hg)
      exact ⟨⟨e g, hg'⟩,e.symm_apply_apply g⟩
  let σ : Representation (ZMod 2) A6 U := ρ.comp a
  let P : σ.IntertwiningMap (alternatingNaturalRepresentation (Fin 6)) :=
    p.intertwiningMap_of_isIntertwiningMap _ _ (fun g u => by
      change p (ρ (e.symm g.val) u) = naturalRepresentation (Fin 6) g.val (p u)
      rw [hp,e.apply_symm_apply])
  have hcoin : Coinvariants.ker σ = ⊤ := by
    have hh := subspaceCommutator_top_eq_coinvariants ρ A6
    have hh' := subspaceCommutator_comp_map ρ a ⊤ ⊤
    rw [hr] at hh'
    rw [←hgen,←hh']
    unfold subspaceCommutator Coinvariants.ker
    congr 1
    ext v
    constructor
    · rintro ⟨⟨g,u⟩,rfl⟩
      exact ⟨g,mem_top _,u,Submodule.mem_top,rfl⟩
    · rintro ⟨g,_,u,_,rfl⟩
      exact ⟨(g,u),rfl⟩
  have hP : IsCover P := ⟨hsur,fun u hu g => hker hu ⟨a g,ha g⟩,hcoin⟩
  obtain ⟨f,hf,he,hpf⟩ := core_quotient_of_alternating_cover σ P hP
  refine ⟨f,hf,?_,hpf⟩
  intro g hg v
  have h := he ⟨e g,map_alternating_six e ▸ mem_map_of_mem e.toMonoidHom hg⟩ v
  change f (coreRepresentation (Fin 6) (e g) v) = ρ (e.symm (e g)) (f v) at h
  simpa only [e.symm_apply_apply] using h

end BinaryPermutation.SixCover
