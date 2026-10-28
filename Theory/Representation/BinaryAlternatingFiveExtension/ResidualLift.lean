module
public import Theory.Representation.BinaryAlternatingFiveExtension.FaithfulExtension
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.ElementaryAbelian.Basic

/-!
# An actual residual four-group over the faithful natural S₅ kernel

The proved natural-kernel splitting supplies a section of the prescribed
S₅ epimorphism. Map the concrete even four-group through that section.
Functoriality of O² places this elementary subgroup in the original
residual, and the section identity retains its image order four under
the same epimorphism. No lift through an arbitrary two-core is asserted.

Application: the natural-kernel case of Aschbacher--Smith 13.2.8(1), p.880,
via the original E.1.14(1) generation obstruction, p.214.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace BinaryPermutation.AlternatingFiveExtension
variable {D : Type*} [Group D] [Finite D]

/-- The marked section constructs the four-group inside the actual residual. -/
theorem exists_residual_four_of_faithful_kernel
    (q : D →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (e : q.ker ≃* Multiplicative (core (Fin 5)))
    (he : ∀ (g : D) (v : q.ker), e (MulAut.conjNormal g v) = coreAction (q g) (e v)) :
    ∃ A : Subgroup D, IsElementaryAbelian 2 A ∧ A ≤ pResidual 2 D ∧
      Nat.card (A.map q) = 4 := by
  obtain ⟨s,hs⟩ := exists_section_of_faithful_kernel q hq e he
  let F := AlternatingFiveFlag.four
  have hp : ∀ x : F, x ^ 2 = 1 := by decide +kernel
  let : IsMulCommutative F := ⟨⟨fun a b => by
    have hh : ∀ a b : F, a * b = b * a := by decide +kernel
    exact hh a b⟩⟩
  let : IsElementaryAbelian 2 F := ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp⟩
  refine ⟨F.map s,IsElementaryAbelian.map s,?_,?_⟩
  · apply (map_mono (f := s) ?_).trans (map_pResidual_le 2 s)
    rw [Equiv.Perm.twoResidual_eq_alternating]
    exact AlternatingFiveFlag.four_even
  · rw [map_map,hs,Subgroup.map_id]
    exact AlternatingFiveFlag.four_card
end BinaryPermutation.AlternatingFiveExtension
