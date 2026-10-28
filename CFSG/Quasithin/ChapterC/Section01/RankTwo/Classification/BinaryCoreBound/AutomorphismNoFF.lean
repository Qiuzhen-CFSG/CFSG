module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AutomorphismNoFF.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AutomorphismNoFF.InnerGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AutomorphismNoFF.SingerBound

/-!
# Binary FF exclusion for the automorphism group of SL₃(2)

The actual automorphism group of SL₃(2) has no faithful finite-dimensional binary
FF-module. The Singer actor displaces at least six dimensions: its nonzero odd
support has square order congruent to one modulo seven. Generation by conjugate
inner elementary subgroups, together with the outer-involution commutator bound,
then makes every nontrivial elementary actor displace more than its rank.

Both concrete inputs to `Reduction` are discharged here. The argument applies
to arbitrary modules, including reducible modules and nonsplit extensions.
Transport to the binary linear group uses the actual equivalence
`MulAut.congr (BinaryLinear.OuterCyclic.slEquivLinear 3)`.

Source: Aschbacher–Smith, C.1.32 proof, printed pp.135–136, and the binary SL₃
case of B.4.2/B.5.1, printed pp.86 and 99–103, combined manuscript of 1 March
2004. This direct proof does not require the hypothesis `G = J(G,V)` of B.5.1.
-/

public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.AutomorphismNoFF

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every nontrivial elementary actor on a faithful binary module for the actual
automorphism group of SL₃(2) has fixed codimension strictly greater than its rank. -/
theorem rank_lt_fixedCodim_of_faithful (ρ : Representation (ZMod 2) AutSL V)
    (hfaith : Function.Injective ρ) (A : Subgroup AutSL) (hA : IsElementaryTwo A) :
    rank A < fixedCodim ρ A :=
  rank_lt_fixedCodim_of_singer_bound ρ innerGeneration
    (six_le_singer_fixedCodim ρ hfaith) A hA

/-- The strict source cardinality inequality for every nontrivial elementary
two-subgroup in a faithful binary action of the actual automorphism group. -/
theorem card_mul_fixed_lt_of_faithful (ρ : Representation (ZMod 2) AutSL V)
    (hfaith : Function.Injective ρ) (A : Subgroup AutSL) (hA : IsElementaryTwo A) :
    Nat.card A * Nat.card (fixedSpace ρ A) < Nat.card V :=
  card_mul_fixed_lt_of_singer_bound ρ innerGeneration
    (six_le_singer_fixedCodim ρ hfaith) A hA

/-- The actual matrix automorphism group has no faithful finite-dimensional
binary FF-module, without any irreducibility or splitting hypothesis. -/
theorem not_isFFModule_of_faithful (ρ : Representation (ZMod 2) AutSL V)
    (hfaith : Function.Injective ρ) : ¬ IsFFModule ρ :=
  not_isFFModule_of_singer_bound ρ innerGeneration (six_le_singer_fixedCodim ρ hfaith)

/-- Faithful FF exclusion on the exact linear-group automorphism model used by
the binary MS quotient, transported through `MulAut.congr (slEquivLinear 3)`. -/
theorem not_isFFModule_linear_of_faithful
    (ρ : Representation (ZMod 2) (MulAut (BinaryLinear.OuterCyclic.LinearGroup 3)) V)
    (hfaith : Function.Injective ρ) : ¬ IsFFModule ρ :=
  not_isFFModule_linear_of_singer_bound ρ innerGeneration
    (six_le_singer_fixedCodim (ρ.comp linearAutEquiv.toMonoidHom)
      (hfaith.comp linearAutEquiv.injective))

end CFSG.Quasithin.ChapterC.BinaryMS.AutomorphismNoFF
