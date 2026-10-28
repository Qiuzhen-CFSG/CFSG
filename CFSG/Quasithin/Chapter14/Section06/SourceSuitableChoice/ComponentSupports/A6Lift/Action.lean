module

public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.A6Lift.SylowFlag
public import Mathlib.RingTheory.SimpleModule.Rank

/-!
# The original actor on a marked A₆ central cover

The universal cover calculation belongs to the normal image L in J. Its
marked maximal kernel and scalar commutant lift the original J-action and
preserve the singular locus. An actual Sylow two-subgroup of J fixes a
nonzero natural vector; its span is an isotropic binary line with irreducible
stabilizer. I.2.3 then supplies a vector in any original central J-cover
which that Sylow fixes and L moves. The literal covering map is retained.

Source: Aschbacher--Smith I.2.3(1a),(2), printed p.413; the choice preceding
14.6.24, printed p.1038. No fixed-free assertion about the five-space is used.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.A6Lift
open Representation Representation.OneCohomology
open Representation.OneCohomology.CentralCoverOriginalAction
open Representation.SymplecticFourOrthogonalCover
open Representation.BinaryOffender ClassicalOrthogonal Module
variable {J : Type*} [Group J] [Finite J]

/-- The original ambient action lifts to the concrete universal L-cover. -/
theorem original_action (L : Subgroup J) [L.Normal] (e : L ≃* Core)
    (η : Representation (ZMod 2) J Natural)
    (hη : ∀ l : L, ∀ v, η l v = natural e l v) :
    ∃ ζ : Representation (ZMod 2) J Cover,
      (∀ l : L, ∀ u, ζ l u = cover e l u) ∧
      (∀ j u, markedProjection e (ζ j u) = η j (markedProjection e u)) ∧
      (∀ j u, formB 2 (ZMod 2) (ζ j u) = 0 ↔ formB 2 (ZMod 2) u = 0) := by
  exact exists_original_action_preserving_singular L η (natural e) (cover e) hη
    (markedProjection e) (markedProjection_isCover e) (marked_kernel_cohomology e)
    (marked_scalar_commutant e) (formD 2 (ZMod 2)).polarBilin polarD_nondegenerate
    (fun l => polar_invariant (e l)) (formB 2 (ZMod 2))
    (fun l => action_preserves (e l)) (marked_polar e)

/-- The actual Sylow action selects an isotropic line with irreducible
stabilizer. Over F₂ a line needs no additional stabilizer hypothesis. -/
theorem exists_sylow_line (η : Representation (ZMod 2) J Natural) (S : Sylow 2 J) :
    ∃ line : Submodule (ZMod 2) Natural, finrank (ZMod 2) line = 1 ∧
      S.toSubgroup ≤ subspaceStabilizer η line ∧
      (∀ v ∈ line, ∀ w ∈ line, (formD 2 (ZMod 2)).polarBilin v w = 0) ∧
      IsIrreducible (stabilizerRepresentation η line) := by
  obtain ⟨v, hv, hfix⟩ := pGroup_fix_nonzero_vector
    (by rw [ringChar.eq (ZMod 2) 2]; decide)
    (by simpa only [ringChar.eq (ZMod 2) 2] using S.isPGroup')
    (η.comp S.toSubgroup.subtype)
  let line : Submodule (ZMod 2) Natural := Submodule.span (ZMod 2) {v}
  have hd : finrank (ZMod 2) line = 1 := finrank_span_singleton hv
  refine ⟨line, hd, ?_, ?_, ?_⟩
  · apply le_subspaceStabilizer
    intro s hs w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have he : η s v = v := hfix ⟨s, hs⟩
    rw [map_smul, he]
    exact line.smul_mem c (Submodule.mem_span_singleton_self v)
  · intro x hx y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hz : (formD 2 (ZMod 2)).polarBilin v v = 0 := by
      simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self,
        two_smul, CharTwo.add_self_eq_zero]
    simp [map_smul, LinearMap.smul_apply, hz]
  · let : IsSimpleModule (ZMod 2) line := isSimpleModule_iff_finrank_eq_one.mpr hd
    let : Nontrivial line := IsSimpleModule.nontrivial (ZMod 2) line
    constructor
    intro U
    rcases IsSimpleOrder.eq_bot_or_eq_top U.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

/-- I.2.3 on an arbitrary original central cover, with all orthogonal-model
inputs and the Sylow-line stabilizer hypothesis discharged. -/
theorem fixed_moving_vector
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (L : Subgroup J) [L.Normal] (e : L ≃* Core)
    (η : Representation (ZMod 2) J Natural)
    (hη : ∀ l : L, ∀ v, η l v = natural e l v)
    (τ : Representation (ZMod 2) J V) (q : τ.IntertwiningMap η) (hq : IsCover q)
    (S : Sylow 2 J) :
    ∃ line : Submodule (ZMod 2) Natural, finrank (ZMod 2) line = 1 ∧
      (∃ v : V, q v ∈ line ∧ v ∉ fixed (τ.comp L.subtype) ∧ ∀ s : S, τ s v = v) ∧
      (∀ j : pCore 2 (subspaceStabilizer η (line.restrictScalars (ZMod 2))),
        ∀ v : V, q v ∈ line → τ j.val.val v = v) ∧
      subspaceStabilizer τ ((line.restrictScalars (ZMod 2)).comap q.toLinearMap) =
        subspaceStabilizer η (line.restrictScalars (ZMod 2)) := by
  obtain ⟨line, hd, hS, _, hirr⟩ := exists_sylow_line η S
  obtain ⟨_, _, _, _, _, hiso, _, _, _, _, _, _⟩ :=
    selected_sylow_flag L e η hη S line hd hS
  have he : line.restrictScalars (ZMod 2) = line := by ext v; rfl
  let : IsIrreducible (stabilizerRepresentation η (line.restrictScalars (ZMod 2))) := by
    rw [he]
    exact hirr
  have hne : line ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hd
    contradiction
  refine ⟨line, hd, ?_⟩
  exact ChapterI.ModuleCovers.OriginalAction.fixed_point_and_normalizer_centrality
    L η (natural e) (cover e) hη (markedProjection e) (markedProjection_isCover e)
    (marked_kernel_cohomology e) (marked_scalar_commutant e)
    (formD 2 (ZMod 2)).polarBilin polarD_nondegenerate (fun l => polar_invariant (e l))
    (formB 2 (ZMod 2)) (fun l => action_preserves (e l)) (marked_polar e)
    z rfl (by rw [formB_z]; exact one_ne_zero)
    (marked_kernel_anisotropic e) (marked_natural_fixed e)
    τ q hq line hne hiso S (by simpa only [he] using hS)

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.A6Lift
