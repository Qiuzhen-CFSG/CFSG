module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Fixed
public import Theory.GroupTheory.PResidual.PrimeToIntersection
public import Theory.GroupTheory.PResidual.TwoThreeComparison
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# The prime-to-three residual in the diagonal centralizer

Original 10.1.3 identifies O^{3′}(M) with L₀. Intersecting with C_G(z)
preserves the embedded prime-to-three residual. Once the natural-action
calculation establishes that C_{L₀}(z) is a {2,3}-group, O² and O^{3′}
agree there. Hence X = O^{3′}(C_G(z) ∩ M).

For any intermediate X ≤ C ≤ C_G(z) ∩ M, monotonicity and idempotence
give O^{3′}(C) = X. If C is normalized by C_G(z), characteristicity then
gives the normality required in 10.2.11(2). The prime-spectrum input is
explicit; these deductions do not assume the desired normality conclusion.

Source: Aschbacher--Smith 10.1.3 and 10.2.11, printed pp.742,753.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G}

/-- The actual linear-three quotient supplies the cubic divisibility in 10.1.3. -/
theorem orbit_eq_cubic_residual (s : SourceLinearThreeSurvivor T D) :
    (primeToResidual 3 D.maximalLocal).map D.maximalLocal.subtype = localOrbit T L := by
  apply source_nonnormal_cubic_residual D (survivor_nonnormal s)
  rw [Nat.card_congr s.quotient.toEquiv, Matrix.PSL3Two.card_SL]
  decide

/-- Literal residual comparison; only the local prime-spectrum calculation remains. -/
theorem seed_eq_cubic_residual (s : SourceLinearThreeSurvivor T D)
    (h23 : IsPiGroup twoThreePrimes
      (localOrbit T L ⊓ centralizer ({a*b} : Set G) : Subgroup G)) :
    (primeToResidual 3 (centralizer ({a*b} : Set G) ⊓ D.maximalLocal : Subgroup G)).map
      (centralizer ({a*b} : Set G) ⊓ D.maximalLocal).subtype =
        centralizerSeed T L (a*b) := by
  have he := embedded_primeToResidual_intersection 3 D.maximalLocal
    (centralizer ({a*b} : Set G))
  rw [orbit_eq_cubic_residual s, inf_comm D.maximalLocal] at he
  rw [centralizerSeed, twoResidual_eq_primeToResidual_three h23]
  exact he.symm

/-- The third SeedAnalysis field follows from the actual prime-to-three calculation. -/
theorem normal_in_kernel_of_twoThree (s : SourceLinearThreeSurvivor T D)
    (h23 : IsPiGroup twoThreePrimes
      (localOrbit T L ⊓ centralizer ({a*b} : Set G) : Subgroup G))
    (C : Subgroup G)
    (hC : C ≤ centralizer ({a*b} : Set G) ⊓ D.maximalLocal)
    (hHC : centralizer ({a*b} : Set G) ≤ normalizer (C : Set G))
    (hXC : centralizerSeed T L (a*b) ≤ C) :
    centralizer ({a*b} : Set G) ≤ normalizer (centralizerSeed T L (a*b) : Set G) := by
  let K := centralizer ({a*b} : Set G) ⊓ D.maximalLocal
  let X := centralizerSeed T L (a*b)
  have hK : (primeToResidual 3 K).map K.subtype = X := seed_eq_cubic_residual s h23
  have hX : (primeToResidual 3 X).map X.subtype = X := by
    have he := congrArg (fun A : Subgroup K => A.map K.subtype)
      (embedded_primeToResidual_eq_of_normal 3 (primeToResidual 3 K) le_rfl)
    rw [map_embedded_primeToResidual_of_hom, hK] at he
    exact he
  have he : (primeToResidual 3 C).map C.subtype = X := by
    apply le_antisymm ((embedded_primeToResidual_mono 3 hC).trans_eq hK)
    rw [← hX]
    exact embedded_primeToResidual_mono 3 hXC
  change centralizer ({a*b} : Set G) ≤ normalizer (X : Set G)
  rw [← he]
  exact hHC.trans (normalizer_le_normalizer_characteristic_image C (primeToResidual 3 C))

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed
