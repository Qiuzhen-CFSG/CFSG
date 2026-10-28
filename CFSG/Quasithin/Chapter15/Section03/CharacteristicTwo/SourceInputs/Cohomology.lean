module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve.Source
public import Theory.Representation.SLHigherNaturalFirstCohomology
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Duality

/-!
# The dual natural cohomology input to Section 15.3

The dot-product pairing identifies the natural SLₙ(2) action with its dual
after inverse transpose. Transport through `H1Congr` and the actual quotient
SLₙ(2) → PSLₙ(2) therefore gives the literal dual-action vanishing required
by `Sieve.UniversalNaturalCohomology`, in dimensions four and five.

The natural-module dimensions come from the checked elementary-transvection
calculation. The pairing argument extends the rank-four transport used in
`LinearFourFive.FourModules.Splitting`; the projective step verifies the
existing `Sieve.natural` action pointwise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.1.5 and
I.1.6(6), printed p.408; their uses in 15.3.24 and 15.3.32,
printed pp.1129–1133. Classification and local recognition remain separate.
-/

public section

open Representation Representation.OneCohomology BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs
open RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
private theorem graph_pairing (n : ℕ) (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (x : Space n) :
    dotProductEquiv (ZMod 2) (Fin n) (specialLinearNatural n g x) =
      (specialLinearNatural (k := ZMod 2) n).dual (graphSL n g)
        (dotProductEquiv (ZMod 2) (Fin n) x) := by
  apply LinearMap.ext
  intro y
  have hs : graphLinear n (slEquivLinear n (graphSL n g)) = slEquivLinear n g := by
    rw [graphLinear_slEquivLinear]
    change slEquivLinear n (graphSL n (graphSL n g)) = _
    exact congrArg (slEquivLinear n) (MulEquiv.congr_fun (graphSL_sq n) g)
  have he := graphLinear_dotProduct (slEquivLinear n (graphSL n g)) x
    ((slEquivLinear n (graphSL n g)).symm y)
  rw [hs, LinearEquiv.apply_symm_apply] at he
  exact he

private theorem dual_projective (n : ℕ) [NeZero n]
    (g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (f : Module.Dual (ZMod 2) (Fin n → ZMod 2)) :
    (specialLinearNatural (k := ZMod 2) n).dual g f =
      (Sieve.natural n).dual
        (Chapter2.ComponentRefinement.LieType.Binary.slEquivPSL n g) f := by
  apply LinearMap.ext
  intro v
  change f (specialLinearNatural n g⁻¹ v) =
    f (Chapter2.ComponentRefinement.LieType.Binary.pslEquivLinear n
      ((Chapter2.ComponentRefinement.LieType.Binary.slEquivPSL n g)⁻¹) v)
  rw [← map_inv, Chapter2.ComponentRefinement.LieType.Binary.slEquivPSL_apply,
    Chapter2.ComponentRefinement.LieType.Binary.pslEquivLinear_project]
  rfl

/-- I.1.6(6) on the exact dual projective actions used by the local sieve. -/
theorem universalNaturalCohomology : Sieve.UniversalNaturalCohomology := by
  intro n _ hn
  let e := H1Congr (specialLinearNatural (k := ZMod 2) n)
    (specialLinearNatural (k := ZMod 2) n).dual (graphSL n)
    (dotProductEquiv (ZMod 2) (Fin n)) (graph_pairing n)
  let e' := H1Congr (specialLinearNatural (k := ZMod 2) n).dual (Sieve.natural n).dual
    (Chapter2.ComponentRefinement.LieType.Binary.slEquivPSL n)
    (LinearEquiv.refl (ZMod 2) _) (dual_projective n)
  rw [← e'.finrank_eq, ← e.finrank_eq]
  rcases hn with rfl | rfl
  · exact SLHigherNatural.finrank_H1_sl4_two
  · exact SLHigherNatural.finrank_H1_sl5_two
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs

end
