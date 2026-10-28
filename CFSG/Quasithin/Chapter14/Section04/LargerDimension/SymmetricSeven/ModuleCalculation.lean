module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven.Catalogue
public import Theory.Representation.AlternatingSevenConjugatePair.SourceLineGeometry

/-!
# The source moved planes for the literal residual lifts

Pulling the supplied binary conjugate-pair action back through `q : H → S₇`
identifies each actual actor commutator with its permutation residual
commutator. Consequently the first two actors give planes of dimension two,
with the displacement inclusions used by the extraspecial lift. The third
actor fixes the distinguished line. The ambient extraspecial and earlier
source premises remain with the assembly of Lemma 14.4.11.

Source: Aschbacher–Smith, Lemma 14.4.11, printed p.1011/PDF p.1028.
-/

@[expose] public section
open Representation Representation.BinaryOffender
open Representation.AlternatingSevenConjugatePair
open Representation.AlternatingSevenConjugatePair.SourceLineGeometry
open Theory.SpecificGroups.SymmetricSeven.LocalResidualModels
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven

variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]

/-- Commutators under the pullback are literally commutators under the actor image. -/
theorem subspaceCommutator_pullback (ρ : Representation (ZMod 2) S7 V)
    (q : H →* S7) (W : Submodule (ZMod 2) V) (X : Subgroup H) :
    subspaceCommutator (ρ.comp q) W X = subspaceCommutator ρ W (X.map q) := by
  apply congrArg (Submodule.span (ZMod 2))
  ext v
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    exact ⟨q x, ⟨x, hx, rfl⟩, w, hw, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, w, hw, rfl⟩
    exact ⟨x, hx, w, hw, rfl⟩

variable [Finite H]

/-- Residual-lift transport through the quotient map of the catalogue. -/
theorem residualLift_movedLine (ρ : Representation (ZMod 2) S7 V)
    (q : H →* S7) (hq : Function.Surjective q) (s : V) (P : Subgroup S7) :
    subspaceCommutator (ρ.comp q) (line s) (residualLift q P) = movedLine ρ s P := by
  rw [subspaceCommutator_pullback, residualLift_map q hq]
  rfl

variable [FiniteDimensional (ZMod 2) V]

/-- The first literal source actor moves the line in dimension two. -/
theorem firstActor_moved_finrank (D : Pair V) (q : H →* S7)
    (hq : Function.Surjective q) (s : V) (hne : s ≠ 0) :
    Module.finrank (ZMod 2)
      (subspaceCommutator (D.representation.comp q) (line s) (firstActor q)) = 2 := by
  rw [firstActor, residualLift_movedLine D.representation q hq]
  exact first_moved_finrank D s hne

/-- The second literal source actor moves the line in dimension two. -/
theorem secondActor_moved_finrank (D : Pair V) (q : H →* S7)
    (hq : Function.Surjective q) (s : V) (hne : s ≠ 0)
    (hs : ∀ t ∈ standardTwo, D.representation t s = s) :
    Module.finrank (ZMod 2)
      (subspaceCommutator (D.representation.comp q) (line s) (secondActor q)) = 2 := by
  rw [secondActor, residualLift_movedLine D.representation q hq]
  exact second_moved_finrank D s hne hs

/-- The first actor satisfies the precise linear containment used in the extraspecial lift. -/
theorem firstActor_moved_le (D : Pair V) (q : H →* S7)
    (hq : Function.Surjective q) (s : V)
    (hs : ∀ t ∈ standardTwo, D.representation t s = s) :
    subspaceCommutator (D.representation.comp q) (line s) (firstActor q) ≤
      subspaceCommutator (D.representation.comp q)
        (displacement D.representation a) (B8.comap q) := by
  rw [firstActor, residualLift_movedLine D.representation q hq,
    subspaceCommutator_pullback, Subgroup.map_comap_eq_self_of_surjective hq]
  exact first_moved_le D s hs

/-- The second actor satisfies the containment directly, without the printed false equality. -/
theorem secondActor_moved_le (D : Pair V) (q : H →* S7)
    (hq : Function.Surjective q) (s : V)
    (hs : ∀ t ∈ standardTwo, D.representation t s = s) :
    subspaceCommutator (D.representation.comp q) (line s) (secondActor q) ≤
      subspaceCommutator (D.representation.comp q)
        (displacement D.representation c) (B8.comap q) := by
  rw [secondActor, residualLift_movedLine D.representation q hq,
    subspaceCommutator_pullback, Subgroup.map_comap_eq_self_of_surjective hq]
  exact second_moved_le D s hs

/-- The third actor centralizes the source line under the literal pullback action. -/
theorem thirdActor_fixes_line (D : Pair V) (q : H →* S7)
    (hq : Function.Surjective q) (s : V)
    (hs : ∀ t ∈ standardTwo, D.representation t s = s) :
    line s ≤ fixedSpace (D.representation.comp q) (thirdActor q) := by
  apply (subspaceCommutator_eq_bot_iff _ _ _).mp
  rw [thirdActor, residualLift_movedLine D.representation q hq]
  exact (subspaceCommutator_eq_bot_iff _ _ _).mpr (third_fixes_line D s hs)

omit [Finite H] in
/-- The exact vector stabilizer pulls back to the syntheme preimage. -/
theorem source_stabilizer_iff (D : Pair V) (q : H →* S7) (s : V) (hne : s ≠ 0)
    (hs : ∀ t ∈ standardTwo, D.representation t s = s) (h : H) :
    (D.representation.comp q) h s = s ↔ h ∈ synthemeOvergroup.comap q :=
  stabilizer_iff D s hne hs (q h)

omit [Finite H] in
/-- Any actor lift of either marked swap has displacement dimension four. -/
theorem source_displacement_finrank (D : Pair V) (q : H →* S7) (h : H)
    (hh : q h = a ∨ q h = c) :
    Module.finrank (ZMod 2) (LinearMap.range ((D.representation.comp q) h - LinearMap.id)) = 4 := by
  change Module.finrank (ZMod 2) (displacement D.representation (q h)) = 4
  apply displacement_finrank D
  rcases hh with hh | hh <;> rw [hh] <;>
    exact orderOf_eq_prime (by decide) (by decide)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.SymmetricSeven
