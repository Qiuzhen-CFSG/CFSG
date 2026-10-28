module
public import CFSG.Quasithin.Chapter10.SourceA5SeparatedCoordinates.Models
public import Theory.Representation.NormalPairHomogeneous.Product
public import Theory.Representation.AlternatingFiveMovedPair.MixedTypes
public import Theory.Representation.AlternatingFiveMovedPair.SeparatedCentralizer

/-!
# Full separated coordinates in the centralizer's fixed models

The natural marking is normalized by its proved automorphism-twist equivalence;
the deleted core model is changed by the literal core-to-natural map. Combining
the complementary supports then identifies the whole module with two blocks of
equal positive multiplicity. The exact pair action matches the fixed natural
or deleted action used by the small-multiplicity centralizer theorem.

Source: Aschbacher–Smith D.3.21 and its use in the original full/local passage.
The numerical multiplicity bound remains an independent input to that consumer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Representation.NormalPairHomogeneous
open Representation.AlternatingFiveMovedPair
namespace CFSG.Quasithin.Chapter10
local instance : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) := ZMod.algebra _ 2
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) Q V)
  (i : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →* Q)

/-- The original pair action has full-module coordinates in the exact fixed
natural or deleted models used by the centralizer consumer. -/
theorem source_a5_separated_normalized_coordinates
    (hi : Function.Injective i) [i.range.Normal] [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (hL : NormalPairSupport.left ρ i ≠ ⊥)
    (exchange : NormalPairSupport.left ρ i ≃ₗ[ZMod 2] NormalPairSupport.right ρ i) :
    (∃ n : ℕ, 0 < n ∧
      ∃ c : V ≃ₗ[ZMod 2] ((Fin n → SeparatedCentralizer.Natural) ×
          (Fin n → SeparatedCentralizer.Natural)),
        ∀ d v, c (ρ (i d) v) =
          (fun j => SeparatedCentralizer.natural d.1 ((c v).1 j),
           fun j => SeparatedCentralizer.natural d.2 ((c v).2 j))) ∨
    (∃ n : ℕ, 0 < n ∧
      ∃ c : V ≃ₗ[ZMod 2] ((Fin n → SeparatedCentralizer.Deleted) ×
          (Fin n → SeparatedCentralizer.Deleted)),
        ∀ d v, c (ρ (i d) v) =
          (fun j => SeparatedCentralizer.deleted d.1 ((c v).1 j),
           fun j => SeparatedCentralizer.deleted d.2 ((c v).2 j))) := by
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hc := NormalPairSupport.support_isCompl ρ i hi
    (alternatingGroup.center_eq_bot (by simp)) hρ (Or.inl hL)
  rcases source_a5_separated_model_coordinates ρ i hi hρ hL exchange with hnat | hdel
  · obtain ⟨f,⟨C⟩⟩ := hnat
    obtain ⟨e⟩ := MixedTypes.natural_marking f
    let D : Coordinates ρ i SeparatedCentralizer.natural :=
      Coordinates.changeModel ρ i _ C e
    exact Or.inl ⟨D.multiplicity,D.positive,D.productEquiv ρ i _ hc,
      D.productEquiv_intertwines ρ i _ hc⟩
  · obtain ⟨C⟩ := hdel
    let D : Coordinates ρ i SeparatedCentralizer.deleted :=
      Coordinates.changeModel ρ i _ C MixedTypes.core_deleted
    exact Or.inr ⟨D.multiplicity,D.positive,D.productEquiv ρ i _ hc,
      D.productEquiv_intertwines ρ i _ hc⟩

end CFSG.Quasithin.Chapter10
