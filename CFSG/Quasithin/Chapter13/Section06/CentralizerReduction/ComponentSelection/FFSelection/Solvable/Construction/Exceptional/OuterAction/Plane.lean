module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SourceAction

/-!
# The cubic plane inside the original ambient action

The original normal X supplies an invariant moved plane for the whole
ambient group. Its three-point permutation action is constructed from the
binary linear action. On the specified offender subgroup, its kernel is
exactly the second coordinate of the same recovered parity isomorphism.
The equality of moved spaces uses the literal subgroup inclusion.

This is the action transport consumed by `minimalSolvable_outer_starLv_eq`.
It does not extend the parity isomorphism to a larger group or split off
any global fixed space.
Source: Aschbacher–Smith, B.5.7 and 13.6.13, printed pp.106 and 929.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.OuterAction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
open ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
open SourceAction ChapterB.QuasisimpleSource

private theorem natural_three_faithful :
    Function.Injective (BinaryPermutation.naturalRepresentation (Fin 3)) := by
  intro a b hab
  apply BinaryPermutation.naturalMulAction_injective_of_odd (Fin 3) (by decide)
  apply MulEquiv.ext
  intro w
  exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun hab w.toAdd)

/-- The plane action extends to the whole ambient group, while its kernel on
I is the original second coordinate of the same recovered actor equivalence. -/
theorem extend_plane {D M : Type*} [Group D] [Finite D]
    [AddCommGroup M] [Module (ZMod 2) M] [Module.Finite (ZMod 2) M]
    (ρ : Representation (ZMod 2) D M) (I : Subgroup D)
    (X : Subgroup D) [X.Normal] (hXI : X ≤ I)
    (c : ChapterB.OuterSixThreeShape I)
    (d : RecoveredAction c (ρ.comp I.subtype))
    (hsecond : X.subgroupOf I = c.second) :
    ∃ f : D →* Equiv.Perm (Fin 3),
      (∀ g, f g = 1 ↔ ∀ w ∈ moved ρ X, ρ g w = w) ∧
      (∀ i : I, f i = 1 ↔ SixPoint.secondProjection (d.ambient.actorEquiv i) = 1) := by
  have hspace : moved (ρ.comp I.subtype) c.second = moved ρ X := by
    rw [← hsecond]
    unfold moved subspaceCommutator
    congr 1
    ext w
    constructor
    · rintro ⟨i, hi, u, hu, rfl⟩
      exact ⟨i, hi, u, hu, rfl⟩
    · rintro ⟨i, hi, u, hu, rfl⟩
      exact ⟨⟨i, hXI hi⟩, hi, u, hu, rfl⟩
  let W := normalMoved ρ X
  obtain ⟨f, _, _, hf⟩ := plane_permutation_coordinates W.toRepresentation
    (by change Module.finrank (ZMod 2) (moved ρ X) = 2; rw [← hspace]; exact d.recovered.plane)
  have hfix (g : D) : f g = 1 ↔ ∀ w ∈ moved ρ X, ρ g w = w := by
    rw [hf]
    constructor
    · intro hg w hw
      exact congrArg Subtype.val (LinearMap.congr_fun hg (⟨w, hw⟩ : W))
    · intro hg
      ext w
      exact hg w w.property
  refine ⟨f, hfix, ?_⟩
  obtain ⟨b, hb⟩ := d.ambient.cubic_action
  intro i
  rw [hfix]
  constructor
  · intro hi
    apply natural_three_faithful
    apply LinearMap.ext
    intro w
    obtain ⟨u, rfl⟩ := b.surjective w
    have hu : (secondMoved c (ρ.comp I.subtype)).toRepresentation i u = u := by
      apply Subtype.ext
      exact hi u (hspace ▸ u.property)
    simpa only [map_one, Module.End.one_apply] using (hb i u).symm.trans (congrArg b hu)
  · intro hi w hw
    let u : (secondMoved c (ρ.comp I.subtype)).toSubmodule := ⟨w, by change w ∈ moved (ρ.comp I.subtype) c.second; rwa [hspace]⟩
    have hu : (secondMoved c (ρ.comp I.subtype)).toRepresentation i u = u := by
      apply b.injective
      rw [hb, hi, map_one, Module.End.one_apply]
    exact congrArg Subtype.val hu

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.OuterAction
