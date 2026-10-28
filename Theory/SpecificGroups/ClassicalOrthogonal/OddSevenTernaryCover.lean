module

public import Theory.SpecificGroups.ClassicalOrthogonal.OddSevenTernaryCover.Elementary
public import Theory.Quasithin.CentralExtensionRankFour

/-!
# Odd central covers of the ternary odd-seven group are not quasithin

The actual projective odd-seven model has an involution centralizing an
elementary subgroup of order 3⁴. Its involution lifts uniquely through an
odd central kernel, and the entire inverse image of that elementary subgroup
centralizes the lift. The rank-four central-extension theorem forces
three-rank at least three in this genuine involution centralizer.

Both endpoints retain the literal surjection or marked central quotient.
No perfectness, multiplier, or quasithinness-of-quotients premise is needed.
This discharges the Ω₇(3) exception in Aschbacher–Smith A.2.17, printed p.39,
using concrete geometry for the local step accompanying I.2.1, printed p.409.
-/

public section
open Subgroup
namespace ClassicalOrthogonal.OddSevenTernaryCover
variable {F : Type} [Field F] [Finite F]
variable {E : Type*} [Group E] [Finite E]

theorem not_isQuasithin_of_central_cover (hcard : Nat.card F = 3)
    (q : E →* POmegaOdd 3 F) (hq : Function.Surjective q)
    (hc : q.ker ≤ center E) (ho : Odd (Nat.card q.ker)) : ¬ IsQuasithin E := by
  obtain ⟨z,hz,A,hG,hfin,hA,hAc,j,hj⟩ := exists_elementary_four_involution_centralizer hcard
  let := hG
  let := hfin
  let := hA
  exact CentralExtension.not_isQuasithin_of_elementary_centralizer q hq hc ho
    (by decide : 3 ≠ 2) hz j hj hAc.ge

theorem not_isQuasithin_of_quotient_equiv (hcard : Nat.card F = 3)
    (e : (E ⧸ center E) ≃* POmegaOdd 3 F) (ho : Odd (Nat.card (center E))) :
    ¬ IsQuasithin E := by
  obtain ⟨z,hz,A,hG,hfin,hA,hAc,j,hj⟩ := exists_elementary_four_involution_centralizer hcard
  let := hG
  let := hfin
  let := hA
  exact CentralExtension.not_isQuasithin_of_center_quotient_model e ho
    (by decide : 3 ≠ 2) hz j hj hAc.ge

end ClassicalOrthogonal.OddSevenTernaryCover
