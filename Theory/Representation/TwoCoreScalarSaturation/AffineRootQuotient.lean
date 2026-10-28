module

public import Theory.Representation.TwoCoreScalarSaturation
public import Theory.Representation.AffineRootQuotient

/-!
# Affine-root quotient-rank exclusion for faithful linear actions

Scalar saturation of the intrinsic two-core discharges the `hs` premise of
`Representation.affine_root_quotient_rank_ne_one`. For a finite faithful linear
group over a finite characteristic-two field with more than two elements, a full
root line acting by `1 + t D` cannot have rank one in a quotient whose kernel is
precisely the intrinsic two-core. All other hypotheses and the literal composite
quotient map of the conditional theorem are retained.

This is the reusable linear step for Aschbacher--Smith E.1.2(E1) and E.1.14(1),
printed pp.210 and 214. The source G₂ consumer supplies the actual octonion
operators, conjugation transport, and intrinsic quotient-kernel equality.
-/

public section

namespace Representation
universe u v w z
variable {F : Type u} {X : Type v} {V : Type w} {Y : Type z}
  [Field F] [Finite F] [CharP F 2] [Group X] [Finite X]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Group Y] [Finite Y]

/-- A full affine root line in a faithful finite-dimensional action has quotient
rank different from one modulo the intrinsic two-core. -/
theorem affine_root_quotient_rank_ne_one_of_faithful
    (ρ : X →* Module.End F V) (hρ : Function.Injective ρ)
    (r : Multiplicative F →* X) (D : Module.End F V)
    (hr : ∀ a, ρ (r a) - 1 = a.toAdd • D)
    (q : X →* Y) (hq : q.ker = pCore 2 X) (hF : 2 < Nat.card F) :
    Group.rank (q.comp r).range ≠ 1 :=
  affine_root_quotient_rank_ne_one ρ
    (mem_twoCore_of_displacement_eq_smul ρ hρ) r D hr q hq hF

end Representation
