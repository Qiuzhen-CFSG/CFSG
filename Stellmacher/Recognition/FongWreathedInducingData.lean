module

public import Mathlib.Data.Complex.Basic
public import Stellmacher.Recognition.FongWreathedCoordinates

/-!
# Local input for Fong's inducing functions

The input records an actual subgroup, its odd normal subgroup, the unique
normal forms F^i X^j u, and linear homomorphisms with the prescribed values.
No scalar products or induced-character conclusions are assumed.
`IsActual` identifies these witnesses with the normalizer of the specified
Sylow element; `HasSpecialSupport` states the transporter property used to
prove induction isometry on functions supported on the odd F cosets.

Source: Fong (1967), printed p. 72, first two paragraphs.
-/

@[expose] public section

noncomputable section
namespace Stellmacher.Recognition.FongWreathedInduction

/-- The local group and character data used in Fong's induction calculation.
The normal-form condition is a genuine enumeration of the group, not a
character-norm assumption. -/
structure InducingData (G : Type*) [Group G] where
  H : Subgroup G
  f : H
  x : H
  U : Subgroup H
  normal_U : U.Normal
  odd_U : Odd (Nat.card U)
  order_f : orderOf f = 8
  square_x : x ^ 2 = 1
  conjugate_f : x * f * x⁻¹ = f ^ 5
  commute_U : ∀ u : U, Commute f (u : H)
  normal_form : Function.Bijective
    (fun p : Fin 8 × Fin 2 × U => f ^ p.1.val * x ^ p.2.1.val * p.2.2.val)
  alpha : H →* ℂ
  beta : H →* ℂ
  alpha_f : alpha f = Complex.I
  alpha_x : alpha x = 1
  beta_f : beta f = 1
  beta_x : beta x = -1
  alpha_U : ∀ u : U, alpha u = 1
  beta_U : ∀ u : U, beta u = 1

variable {G : Type*} [Group G]

namespace InducingData

def support (d : InducingData G) : Set d.H :=
  {h | ∃ i : Fin 8, Odd i.val ∧ ∃ u : d.U, h = d.f ^ i.val * u.val}

/-- The special-set transporter assertion needed for induction isometry. -/
def HasSpecialSupport (d : InducingData G) : Prop :=
  ∀ a b : d.H, a ∈ d.support → b ∈ d.support →
    ∀ g : G, g⁻¹ * (a : G) * g = (b : G) → g ∈ d.H

/-- Link the local witnesses to the prescribed actual Sylow coordinates. -/
def IsActual (d : InducingData G) (S : Sylow 2 G)
    (P : ABG.Wreathed.Presentation S 2) : Prop :=
  d.H = Subgroup.normalizer (Subgroup.zpowers ((FongWreathedIntrinsic.F P : S) : G) : Set G) ∧
    (d.f : G) = (FongWreathedIntrinsic.F P : S) ∧
    (d.x : G) = (FongWreathedIntrinsic.X P : S)

end InducingData
end Stellmacher.Recognition.FongWreathedInduction
