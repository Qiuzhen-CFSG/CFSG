module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.Reduction
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.SmallParameter
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.QuadraticTori
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal

/-!
# Prime-to-two central covers of binary triality groups

The center of every finite quasisimple group with central quotient
³D₄(2ⁿ), n > 0, is a two-group. The three-primary, quadratic-torus and
cyclotomic-torus constructions supply every odd-prime branch of the local
transfer reduction. This includes n = 1 and every central cover.

`Reduction` applies these actual Sylow geometries to the literal projection
R → R/Z(R), whose kernel is exactly Z(R). No multiplier table, covering
certificate, model simplicity proof or representation hypothesis is an input.
The earlier conditional reductions and small-parameter results remain available.

Source: Guralnick--Malle II §8, internal p.53; GLS3 Theorem 6.1.4 and
Tables 6.1.2--3, which include no triality odd-multiplier exception at q = 2.
-/

public section

namespace Triality.InnerDisplacement.PrimeToTwoCovers

/-- Every finite quasisimple cover of the genuine binary triality group has
two-group center, for every positive exponent, including n = 1. -/
theorem center_isTwoGroup {R : Type*} [Group R] [Finite R]
    [Theory.GroupTheory.IsQuasisimple R] (n : ℕ) (hn : 0 < n)
    (hmodel : Standard.IsTrialityGroupAt (2 ^ n) (R ⧸ Subgroup.center R)) :
    IsPGroup 2 (Subgroup.center R) :=
  center_isTwoGroup_of_prime_branches n hn hmodel
    (ThreeLocal.geometry n hn)
    (fun _ _ hp hd => Standard.QuadraticTori.geometry n hn hp hd)
    (fun _ _ hp hd hc => CyclotomicTori.geometry n hn hp hd hc)

end Triality.InnerDisplacement.PrimeToTwoCovers
