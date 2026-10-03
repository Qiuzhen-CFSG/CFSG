module

public import Stellmacher.Recognition.SuzukiThreeLocalStructure
public import Stellmacher.Recognition.SuzukiThreeRecognitionCoordinates

/-!
# Suzuki's projective-unitary recognition theorem at q = 3

A faithful doubly transitive action on 28 points, with a normal regular
subgroup of a point stabilizer and cyclic quotient of order eight, identifies
the acting group with `ABG.PSU3 3 1 (by decide)`.

The local-structure theorem supplies the root group and swapping involution
from these action hypotheses. Hermitian coordinates identify the entire group
with `PGU3Three`. The explicit equality of the full and special projective
unitary images at q = 3 then gives the project's PSU model. No simplicity or
additional local-structure hypothesis is required.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965), 1–14,
the theorem in Section I and its proof in Sections II–VI. Suzuki's full
projective isometry group is PGU; the final PGU-to-PSU step is specific to q = 3.
-/

namespace Stellmacher.Recognition.SuzukiThreeHypotheses

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω] [FaithfulSMul G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

include h

/-- Suzuki's recognition theorem at q = 3, in the full projective unitary
convention of the original paper. -/
public theorem nonempty_equiv_pgu3Three : Nonempty (G ≃* PGU3Three) := by
  let : Finite Ω := Nat.finite_of_card_ne_zero (by rw [h.degree]; decide)
  let : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by rw [h.degree]; decide)
  obtain ⟨b, hb⟩ := exists_ne a
  exact h.nonempty_equiv_pgu3Three_of_local_structure b hb (h.local_structure b hb)

/-- A faithful Suzuki degree-28 action recognizes the project's PSU₃(3).
The full-to-special projective unitary identification is explicit. -/
public theorem nonempty_equiv_psu3Three :
    Nonempty (G ≃* ABG.PSU3 3 1 (by decide)) := by
  obtain ⟨e⟩ := h.nonempty_equiv_pgu3Three
  exact ⟨e.trans pgu3ThreeEquivPSU3Three⟩

end Stellmacher.Recognition.SuzukiThreeHypotheses
