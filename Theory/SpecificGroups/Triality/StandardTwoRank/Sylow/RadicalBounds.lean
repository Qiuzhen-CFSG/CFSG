module

public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow.RadicalBounds.Arms
public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow.RadicalBounds.Central

/-!
# Elementary subgroup bounds in both genuine binary triality radicals

Every elementary abelian two-subgroup of either marked parabolic radical
has order at most q⁵. The arms branch uses its nondegenerate commutator form.
The central branch splits according to the actual first cubic coordinate,
using the trace hyperbolic form or the tail kernel and trace annihilator.
The endpoint q = 2 is included.

`binary_radical_elementary_card_le` discharges precisely the `hbound` input
of `TwoRank.twoRank_le_of_radical_bounds`. Sylow placement is independent
and remains with that theorem's assembly owner. This module deliberately
imports no Sylow umbrella, so the umbrella can re-export this bound.

Source: GLS3 §§2.4–2.6 (`refs/KGroup/GLS3/chapter2.tex`), and the triality
rank used in Aschbacher–Smith G.9, printed p.356 (`refs/quasithin.pdf`).
-/

public section

open Triality.Standard.Parabolics
namespace Triality.Standard.TwoRank

/-- The unconditional cardinality bound for both radicals in characteristic two. -/
theorem radical_elementary_card_le (P : Parameters) (hp : P.prime = 2)
    (a : Node) (E : Subgroup (radical P a)) (hE : IsElementaryAbelian 2 E) :
    Nat.card E ≤ P.q ^ 5 := by
  let : IsElementaryAbelian 2 E := hE
  cases a with
  | arms => exact RadicalBounds.arms_radical_card_le P hp E
  | central => exact RadicalBounds.central_radical_card_le P hp E

/-- The exact radical-bound input to the binary Sylow two-rank assembly. -/
theorem binary_radical_elementary_card_le (n : ℕ) (hn : 0 < n)
    (a : Node) (E : Subgroup (radical (binaryParameters n hn) a))
    (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ (binaryParameters n hn).q ^ 5 :=
  radical_elementary_card_le (binaryParameters n hn) rfl a E hE

end Triality.Standard.TwoRank
