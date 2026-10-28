module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates
public import Mathlib.SetTheory.Cardinal.Finite
/-!
# Point coinvariants of the natural symplectic four-space

An additive homomorphism invariant under the literal vector stabilizer depends
only on the opposite coordinate. The point-radical matrices move the opposite
basis vector by every vector in its perpendicular hyperplane. Its image
therefore has order at most the field size. This is the natural-module bound
in MS93 (3.10)(i), printed p.880.
-/
public section
open Matrix
open scoped Matrix
namespace Theory.SpecificGroups.SymplecticFour
variable {F P : Type*} [Field F] [CharP F 2] [Group P]

private theorem point_displacement (v : Vector F) (hv : v (.inr 0) = 0) :
    ((pointRadicalElement (v (.inl 1)) (v (.inr 1)) (v (.inl 0))).val •
      (Pi.single (.inr 0) 1 : Vector F)) = Pi.single (.inr 0) 1 + v := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec_single,hv]

/-- An additive character invariant under the actual point stabilizer
factors through the single opposite coordinate. -/
theorem pointInvariantHom_eq_coordinate
    (f : Multiplicative (Vector F) →* P)
    (hf : ∀ g : pointLocal (F := F), ∀ v : Vector F,
      f (Multiplicative.ofAdd (g.val • v)) = f (Multiplicative.ofAdd v))
    (v : Vector F) :
    f (Multiplicative.ofAdd v) =
      f (Multiplicative.ofAdd (Pi.single (.inr 0) (v (.inr 0)))) := by
  have hz (w : Vector F) (hw : w (.inr 0) = 0) : f (Multiplicative.ofAdd w) = 1 := by
    have he := hf (pointRadicalElement (w (.inl 1)) (w (.inr 1)) (w (.inl 0)))
      (Pi.single (.inr 0) 1)
    rw [point_displacement w hw] at he
    change f (Multiplicative.ofAdd (Pi.single (.inr 0) 1) * Multiplicative.ofAdd w) = _ at he
    rw [map_mul] at he
    exact mul_left_cancel (he.trans (mul_one _).symm)
  let w : Vector F := v - Pi.single (.inr 0) (v (.inr 0))
  have hw : w (.inr 0) = 0 := by simp [w]
  have he : v = w + Pi.single (.inr 0) (v (.inr 0)) := by simp [w]
  calc
    _ = f (Multiplicative.ofAdd w *
          Multiplicative.ofAdd (Pi.single (.inr 0) (v (.inr 0)))) := congrArg f (congrArg Multiplicative.ofAdd he)
    _ = _ := by rw [map_mul,hz w hw,one_mul]

/-- The point-fixed character has image of order at most the coefficient field. -/
theorem pointInvariantHom_card_le [Finite F]
    (f : Multiplicative (Vector F) →* P)
    (hf : ∀ g : pointLocal (F := F), ∀ v : Vector F,
      f (Multiplicative.ofAdd (g.val • v)) = f (Multiplicative.ofAdd v)) :
    Nat.card f.range ≤ Nat.card F := by
  let c : F → f.range := fun t =>
    ⟨f (Multiplicative.ofAdd (Pi.single (.inr 0) t)),⟨_,rfl⟩⟩
  apply Nat.card_le_card_of_surjective c
  rintro ⟨u,⟨v,rfl⟩⟩
  exact ⟨v.toAdd (.inr 0),Subtype.ext (pointInvariantHom_eq_coordinate f hf v.toAdd).symm⟩
end Theory.SpecificGroups.SymplecticFour
