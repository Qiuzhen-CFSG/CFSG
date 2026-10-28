module
public import Theory.SpecificGroups.Classical.LinearFundamental
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupTheory.PrimeRankSquareFree
public import Theory.GroupTheory.QuasithinBasic
public import Theory.SpecificGroups.Alternating.TwoThreeCycles

/-!
# Odd rank bounds for the binary projective group of degree five

The proper four-dimensional block embeds SL₄(2), identified with A₈,
faithfully into PSL₅(2). Two independent three-cycles give cubic rank at
least two. The exact projective order has only one factor of five, giving
five-rank at most one. These are the two bounds consumed by the constrained
SL₅(2) row of the original A₅ C.4.8 argument.

Source: Aschbacher–Smith C.2.7(3h) and C.4.5, printed pp.147,152.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.Classical.BinaryFiveRanks

theorem projective_threeRank_ge_two :
    2 ≤ primeRank 3 (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) := by
  let f := (Matrix.SpecialLinearGroup.LinearFundamental.projectiveReindex
    (F := ZMod 2) (finSumFinEquiv (m := 4) (n := 1))).toMonoidHom.comp
      (Matrix.SpecialLinearGroup.LinearFundamental.projectLeft
        (m := Fin 4) (n := Fin 1) (F := ZMod 2))
  have hi : Function.Injective f :=
    (Matrix.SpecialLinearGroup.LinearFundamental.projectiveReindex
      (F := ZMod 2) (finSumFinEquiv (m := 4) (n := 1))).injective.comp
        Matrix.SpecialLinearGroup.LinearFundamental.projectLeft_injective
  have hr : 2 ≤ primeRank 3 (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
    rw [primeRank_equiv 3 (Atlas.Order20160A8.sl4TwoEquivPSL.trans
      Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm)]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  exact hr.trans (Theory.GroupTheory.primeRank_le_of_injective 3 f hi)

private theorem projective_fiveRank_le_one_of_card_two
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2) :
    primeRank 5 (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F) ≤ 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply primeRank_le_one_of_square_not_dvd
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
  norm_num [hF,Fin.prod_univ_succ] at hc
  rw [hc]
  decide

theorem projective_fiveRank_le_one :
    primeRank 5 (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) ≤ 1 :=
  projective_fiveRank_le_one_of_card_two (by simp)

end Theory.SpecificGroups.Classical.BinaryFiveRanks
