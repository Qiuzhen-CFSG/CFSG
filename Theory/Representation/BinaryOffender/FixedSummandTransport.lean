module

public import Theory.Representation.BinaryOffender.FixedCodimTransport
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.GroupTheory.SylowKernelCore

/-!
# Seed stabilizers after removing a fixed direct summand

Compatible coordinates V ≃ W × F, with F fixed by the whole actor, identify
the pointwise stabilizer of a seed with that of its projection on W. The
identification carries the embedded intrinsic two-core and preserves best
offenders: every fixed codimension is unchanged by a fixed direct summand.

The application is the projection U = U_L C_U(L) in Aschbacher--Smith
15.1.28, printed p.1103. In particular a seed is not silently replaced by
its intersection with the moved space.
-/

@[expose] public section
open Subgroup
namespace Representation.BinaryOffender
variable {G H V W F : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup F] [Module (ZMod 2) F]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) H W)
  (actor : G ≃* H) (coordinates : V ≃ₗ[ZMod 2] W × F)

/-- The projected seed uses the first coordinate, not an intersection. -/
noncomputable def splitSeedProjection : V →ₗ[ZMod 2] W :=
  (LinearMap.fst (ZMod 2) W F).comp coordinates.toLinearMap

variable (he : ∀ g v, coordinates (ρ g v) =
  (σ (actor g) (coordinates v).1, (coordinates v).2))

include he

/-- Fixedness of the original seed descends to its projected seed. -/
theorem projected_seed_fixed_of_fixed_summand (P : Submodule (ZMod 2) V)
    (R : Subgroup G) (hfixed : P ≤ fixedSpace ρ R) :
    P.map (splitSeedProjection coordinates) ≤ fixedSpace σ (R.map actor.toMonoidHom) := by
  rintro _ ⟨v, hv, rfl⟩ a
  obtain ⟨g, hg, hga⟩ := a.property
  have hh := congrArg (fun w : W × F => w.1)
    ((he g v).symm.trans (congrArg coordinates (hfixed hv ⟨g, hg⟩)))
  change σ a.val (splitSeedProjection coordinates v) = splitSeedProjection coordinates v
  rw [← hga]
  exact hh

/-- A moving seed has nonzero projection after removing a fixed summand. -/
theorem projected_seed_ne_bot_of_fixed_summand (P : Submodule (ZMod 2) V)
    (hmoving : ¬ P ≤ ρ.invariants) :
    P.map (splitSeedProjection coordinates) ≠ ⊥ := by
  intro hz
  apply hmoving
  intro v hv g
  have hzero : splitSeedProjection coordinates v = 0 := by
    have hm := Submodule.mem_map_of_mem (f := splitSeedProjection coordinates) hv
    rwa [hz, Submodule.mem_bot] at hm
  apply coordinates.injective
  rw [he]
  apply Prod.ext
  · change σ (actor g) (splitSeedProjection coordinates v) = splitSeedProjection coordinates v
    rw [hzero, map_zero]
  · rfl

/-- Pointwise seed stabilizers agree under the literal actor isomorphism. -/
theorem map_seedKernel_of_fixed_summand (P : Submodule (ZMod 2) V) :
    (subspaceKernel ρ P ⊤).map actor.toMonoidHom =
      subspaceKernel σ (P.map (splitSeedProjection coordinates)) ⊤ := by
  have hfix (g : G) (v : V) :
      ρ g v = v ↔ σ (actor g) (splitSeedProjection coordinates v) =
        splitSeedProjection coordinates v := by
    rw [← coordinates.injective.eq_iff, he]
    exact Prod.ext_iff.trans (and_iff_left rfl)
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨mem_top _, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact (hfix g v).mp (hg.2 v hv)
  · intro ha
    refine ⟨actor.symm a, ⟨mem_top _, ?_⟩, actor.apply_symm_apply a⟩
    intro v hv
    apply (hfix (actor.symm a) v).mpr
    simpa only [actor.apply_symm_apply] using
      ha.2 _ (Submodule.mem_map_of_mem hv)

/-- Embedded intrinsic two-cores transport along the same stabilizer equality. -/
theorem map_seedCore_of_fixed_summand (P : Submodule (ZMod 2) V) :
    ((subspaceKernel ρ P ⊤).pCoreIn 2).map actor.toMonoidHom =
      (subspaceKernel σ (P.map (splitSeedProjection coordinates)) ⊤).pCoreIn 2 := by
  rw [map_pCoreIn_of_injective 2 _ actor.toMonoidHom actor.injective,
    map_seedKernel_of_fixed_summand ρ σ actor coordinates he]

variable [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
  [FiniteDimensional (ZMod 2) F]

omit [FiniteDimensional (ZMod 2) V] in
/-- Removing a fixed summand preserves each subgroup's fixed codimension. -/
theorem fixedCodim_of_fixed_summand (A : Subgroup G) :
    fixedCodim ρ A = fixedCodim σ (A.map actor.toMonoidHom) := by
  have h := fixedCodim_map_equivariant ρ
    (σ.prod (Representation.trivial (ZMod 2) H F)) actor.toMonoidHom coordinates he A
  rw [fixedCodim_prod] at h
  have hf : fixedSpace (Representation.trivial (ZMod 2) H F)
      (A.map actor.toMonoidHom) = ⊤ := by
    apply top_unique
    intro v _ a
    rfl
  have hz : fixedCodim (Representation.trivial (ZMod 2) H F)
      (A.map actor.toMonoidHom) = 0 := by
    rw [fixedCodim, hf]
    exact Module.finrank_zero_of_subsingleton
  simpa only [hz, add_zero] using h

/-- Every original best offender survives on the projected module. -/
theorem IsBestOffender.map_of_fixed_summand {A : Subgroup G}
    (hA : IsBestOffender ρ A) : IsBestOffender σ (A.map actor.toMonoidHom) :=
  hA.map_of_fixedCodim ρ σ actor.toMonoidHom actor.injective
    (fixedCodim_of_fixed_summand ρ σ actor coordinates he)

/-- An original offender in the seed core gives an offender in the projected
seed core, with the original subgroup's actual image. -/
theorem seed_core_offender_of_fixed_summand (P : Submodule (ZMod 2) V)
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hcore : A ≤ (subspaceKernel ρ P ⊤).pCoreIn 2) :
    IsBestOffender σ (A.map actor.toMonoidHom) ∧
      A.map actor.toMonoidHom ≤
        (subspaceKernel σ (P.map (splitSeedProjection coordinates)) ⊤).pCoreIn 2 := by
  refine ⟨hA.map_of_fixed_summand ρ σ actor coordinates he, ?_⟩
  rw [← map_seedCore_of_fixed_summand ρ σ actor coordinates he]
  exact map_mono hcore

end Representation.BinaryOffender
