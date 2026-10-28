module
public import Theory.Representation.PerfectInvolutionExtension
public import Theory.Representation.NormalInvariants
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Displacement of an actor commuting with a perfect binary factor

Each displacement image of a commuting actor is invariant under the perfect
factor. If its dimension is at most two, the perfect action is trivial on
that image. A zero fixed space then kills the displacement. Consequently a
nontrivial commuting actor has fixed codimension at least three. A normal
factor acting nontrivially on an irreducible module has the required zero
fixed space. No semisimplicity or tensor coordinates are assumed.

Source application: Aschbacher--Smith 13.1.9, printed p.871, the lower bound
in (*). The literal common-chief-section application is in
FFContradiction.SharpSection.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A nontrivial commuting actor moves at least three binary dimensions when
the perfect factor has no fixed vector. -/
theorem three_le_fixedCodim_of_perfect_fixedSpace_eq_bot
    (ρ : Representation (ZMod 2) G V)
    (S A : Subgroup G) [Group.IsPerfect S]
    (hfix : fixedSpace ρ S = ⊥) (hA : ¬ A ≤ ρ.ker) (hc : ⁅S,A⁆ = ⊥) :
    3 ≤ fixedCodim ρ A := by
  by_contra hd
  have hd2 : fixedCodim ρ A ≤ 2 := by omega
  apply hA
  intro a ha
  let D := LinearMap.range (ρ a - 1)
  have hcomm (s : S) : ρ s * ρ a = ρ a * ρ s := by
    rw [←map_mul, ←map_mul]
    exact congrArg ρ (commutator_eq_bot_iff_le_centralizer.mp hc s.property a ha).symm
  let W : Subrepresentation (ρ.comp S.subtype) := {
    toSubmodule := D
    apply_mem_toSubmodule s v hv := by
      obtain ⟨w,rfl⟩ := hv
      refine ⟨ρ s w,?_⟩
      change ρ a (ρ s w) - ρ s w = ρ s (ρ a w - w)
      rw [map_sub]
      exact congrArg (fun z => z - ρ s w) (LinearMap.congr_fun (hcomm s).symm w) }
  have hdim : Module.finrank (ZMod 2) W.toSubmodule ≤ 2 := by
    change Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 2
    rw [←fixedCodim_zpowers_eq_displacement_rank]
    have hfixle : fixedSpace ρ A ≤ fixedSpace ρ (zpowers a) :=
      fun v hv x => hv ⟨x,(zpowers_le.mpr ha) x.property⟩
    have hdimle := Submodule.finrank_mono hfixle
    have hfirst := fixedCodim_add_finrank ρ A
    have hsecond := fixedCodim_add_finrank ρ (zpowers a)
    omega
  apply LinearMap.ext
  intro v
  have hDfix : ρ a v - v ∈ fixedSpace ρ S := by
    intro s
    exact congrArg Subtype.val
      (PerfectInvolutionExtension.small_action_trivial W.toRepresentation hdim s
        ⟨ρ a v - v,⟨v,rfl⟩⟩)
  rw [hfix,Submodule.mem_bot] at hDfix
  exact sub_eq_zero.mp hDfix
/-- The fixed-space hypothesis follows from nontriviality of a normal perfect
factor in an irreducible action. -/
theorem three_le_fixedCodim_of_normal_perfect
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (S A : Subgroup G) [S.Normal] [Group.IsPerfect S]
    (hS : ¬ S ≤ ρ.ker) (hA : ¬ A ≤ ρ.ker) (hc : ⁅S,A⁆ = ⊥) :
    3 ≤ fixedCodim ρ A := by
  have hfix : fixedSpace ρ S = ⊥ := by
    by_contra hn
    exact hS (le_ker_of_normal_invariants_ne_bot ρ S hn)
  exact three_le_fixedCodim_of_perfect_fixedSpace_eq_bot ρ S A hfix hA hc
end Representation.BinaryOffender
