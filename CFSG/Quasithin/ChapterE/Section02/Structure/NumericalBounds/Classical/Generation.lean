module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Classical
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Actual E-generation in the original normal classical parabolic

The positive, proved value on H/J supplies an attained generation witness.
Solvability of the actual maximal core then lifts this witness to H. Thus
consumers can use E-generation directly without a general E.1.11 existence
or attainment assumption for H.

Source: Aschbacher–Smith E.1.10–14 and E.2.2, printed pp.212–216.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- An explicit generation witness at the original selected model exponent. -/
theorem normal_classical_isEGenerated
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ}
    (hm :
      (2 ≤ f ∧ ClassicalGroup.IsPSL
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2 ^ f)) ∨
      (2 ≤ f ∧ ClassicalGroup.IsPSU
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 (2 ^ f)) ∨
      (0 < f ∧ ClassicalGroup.IsPSL
        (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 (2 ^ f))) :
    IsEGenerated f H := by
  have hf : 0 < f := by rcases hm with h | h | h <;> have := h.1 <;> omega
  exact isEGenerated_of_star_parameter T hP hf
    (normal_classical_star_value hA hH T hP hs K hK hgen hm)

end CFSG.Quasithin.ChapterE.Structure.NumericalBounds
