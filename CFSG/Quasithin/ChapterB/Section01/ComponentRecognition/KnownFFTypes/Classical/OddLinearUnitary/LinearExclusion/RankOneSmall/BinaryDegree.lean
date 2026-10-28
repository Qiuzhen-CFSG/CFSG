module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.SourceBounds
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.Representation.BinaryPrimeDegree

/-!
# Binary degree obstructions for the six small odd PSL₂ parameters

The order formula for the actual central quotient, followed by Lagrange in
the covering group and its ambient group, supplies odd prime divisors of G.
Their multiplicative orders of two bound every faithful binary degree. This
proves lower bounds 10, 12, 8, 18, 11, 12 for parameters 11, 13, 17, 19, 23,
25, respectively. In the last case use the torus prime 13.

These bounds retain central covers and outer actors. They do not classify
irreducible modules or prove the outstanding common fixed-space calculations.
In particular the parameter 13 bound excludes a six-dimensional binary
module directly, without assuming absolute irreducibility on the component.

Source: Aschbacher--Smith K.2, printed p.453; Guralnick--Malle,
*Classification of 2F-modules I*, Proposition 4.1, manuscript pp.8--9.
The degree argument itself is the elementary GL order obstruction G.7.1(1).
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Odd divisors of the actual PSL₂ order bound the original binary degree. -/
theorem binary_degree_of_quotient_prime (hf : Function.Injective ρ) {q p : ℕ}
    (ho : Odd q) (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 q)
    (hp : p.Prime) (hp2 : p ≠ 2) (hdiv : p ∣ q * (q ^ 2 - 1)) :
    orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (hF.symm ▸ ho)
  rw [← Nat.card_congr e.toEquiv, hF] at hc
  rw [← hc] at hdiv
  have hd : p ∣ Nat.card ((generalizedFitting G) ⧸ center (generalizedFitting G)) :=
    (hp.dvd_mul.mp hdiv).resolve_right
      (fun hh => hp2 ((Nat.dvd_prime Nat.prime_two).mp hh |>.resolve_left hp.ne_one))
  apply BinaryPrimeDegree.orderOf_le_finrank ρ hf hp hp2
  exact hd.trans ((center (generalizedFitting G)).card_quotient_dvd_card.trans
    (generalizedFitting G).card_subgroup_dvd_card)

/-- The two degree-five constituents at parameter 11 cannot be binary modules. -/
theorem ten_le_degree_eleven (hf : Function.Injective ρ)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 11) :
    10 ≤ Module.finrank (ZMod 2) V := by
  simpa only [BinaryPrimeDegree.orderOf_two_mod_eleven] using
    binary_degree_of_quotient_prime ρ hf (by decide) hm
      (by decide : Nat.Prime 11) (by decide) (by decide)

/-- A faithful binary module at parameter 13 has degree at least twelve. -/
theorem twelve_le_degree_thirteen (hf : Function.Injective ρ)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 13) :
    12 ≤ Module.finrank (ZMod 2) V := by
  simpa only [BinaryPrimeDegree.orderOf_two_mod_thirteen] using
    binary_degree_of_quotient_prime ρ hf (by decide) hm
      (by decide : Nat.Prime 13) (by decide) (by decide)

/-- The Frobenius calculation at parameter 17 starts at binary degree eight. -/
theorem eight_le_degree_seventeen (hf : Function.Injective ρ)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17) :
    8 ≤ Module.finrank (ZMod 2) V := by
  simpa only [BinaryPrimeDegree.orderOf_two_mod_seventeen] using
    binary_degree_of_quotient_prime ρ hf (by decide) hm
      (by decide : Nat.Prime 17) (by decide) (by decide)

private theorem orderOf_two_mod_nineteen : orderOf (2 : ZMod 19) = 18 := by
  apply (orderOf_eq_iff (by decide : 0 < 18)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

/-- The defining prime at parameter 19 forces binary degree at least eighteen. -/
theorem eighteen_le_degree_nineteen (hf : Function.Injective ρ)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 19) :
    18 ≤ Module.finrank (ZMod 2) V := by
  simpa only [orderOf_two_mod_nineteen] using
    binary_degree_of_quotient_prime ρ hf (by decide) hm
      (by decide : Nat.Prime 19) (by decide) (by decide)

/-- The defining prime at parameter 23 forces binary degree at least eleven. -/
theorem eleven_le_degree_twentyThree (hf : Function.Injective ρ)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 23) :
    11 ≤ Module.finrank (ZMod 2) V := by
  simpa only [BinaryPrimeDegree.orderOf_two_mod_twentyThree] using
    binary_degree_of_quotient_prime ρ hf (by decide) hm
      (by decide : Nat.Prime 23) (by decide) (by decide)

/-- The nonsplit torus prime 13 forces degree at least twelve at parameter 25. -/
theorem twelve_le_degree_twentyFive (hf : Function.Injective ρ)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25) :
    12 ≤ Module.finrank (ZMod 2) V := by
  simpa only [BinaryPrimeDegree.orderOf_two_mod_thirteen] using
    binary_degree_of_quotient_prime ρ hf (by decide) hm
      (by decide : Nat.Prime 13) (by decide) (by decide)

/-- Uniform numerical obstruction for the three cases treated by degree eight. -/
theorem eight_lt_degree_of_thirteen_nineteen_twentyThree (hf : Function.Injective ρ)
    {q : ℕ} (hq : q = 13 ∨ q = 19 ∨ q = 23)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 q) :
    8 < Module.finrank (ZMod 2) V := by
  rcases hq with rfl | rfl | rfl
  · exact lt_of_lt_of_le (by decide) (twelve_le_degree_thirteen ρ hf hm)
  · exact lt_of_lt_of_le (by decide) (eighteen_le_degree_nineteen ρ hf hm)
  · exact lt_of_lt_of_le (by decide) (eleven_le_degree_twentyThree ρ hf hm)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall
