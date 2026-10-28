module

public import Theory.SpecificGroups.AlternatingSix.M10.Action.Extension
public import Theory.SpecificGroups.AlternatingSix.M10.LocalGeometry.Coordinates

/-!
# Three-Sylow subgroups of the genuine automorphism group of A₆

The two disjoint three-cycles give a copy of C₃ × C₃ in Aut(A₆).
Its order makes it Sylow. Conjugacy of Sylow subgroups then identifies
every three-Sylow with this copy, and normality of the specified M₁₀
places every such subgroup inside M₁₀.

These are the quotient inputs in the final cubic argument of
Aschbacher–Smith, J.2.7, printed p.437 (PDF p.448).
-/

@[expose] public section
noncomputable section

namespace AlternatingSix.M10.ThreeSylow
open Subgroup ShadowLocal LocalGeometry

/-- The standard nine-group in the actual automorphism group. -/
def standard : Sylow 3 AutA6 :=
  Sylow.ofCard (nine standardNine) (by
    rw [Action.card_nine standardNine card_standardNine, card_aut]
    decide +kernel)

/-- The marked nine-group retains its actual two cyclic coordinates. -/
def standardEquiv : standard ≃* NineCoordinates :=
  ((MonoidHom.ofInjective nineEmbedding_injective).trans
    (Subgroup.equivMapOfInjective standardNine permutationAction
      permutationAction_injective)).symm

/-- Every three-Sylow of Aut(A₆) is elementary abelian of order nine. -/
def equiv (P : Sylow 3 AutA6) : P ≃* NineCoordinates :=
  (P.equiv standard).trans standardEquiv

theorem card (P : Sylow 3 AutA6) : Nat.card P = 9 := by
  rw [Nat.card_congr (equiv P).toEquiv, Nat.card_eq_fintype_card]
  decide +kernel

/-- All three-Sylows lie in the specified normal M₁₀. -/
theorem le_extension (P : Sylow 3 AutA6) : (P : Subgroup AutA6) ≤ extension := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq AutA6 standard P
  change (nine standardNine).map (MulAut.conj g).toMonoidHom ≤ extension
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.Normal.conj_mem inferInstance x
    (Action.nine_le_extension standardNine card_standardNine hx) g

end AlternatingSix.M10.ThreeSylow
