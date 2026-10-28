module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalUnitaryLocal
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.UnitaryClosure

/-!
# Large binary unitary-four components under local fixation

The actual Sylow automorphism theorem makes the outer action soluble.
Local placement then puts the fixed residual in the component, where
unitary parabolic odd-rank bounds contradict its two simple factors.
Source: Aschbacher--Smith 4.4.10--12 and 10.2.3(2), pp.621--623,745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.LocalFixed
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual local module suffices to exclude every large binary unitary-four row. -/
theorem source_nonnormal_oddNormalizer_no_large_unitary_four_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
    (hVX : V = ⁅V,localOrbit T L⁆)
    (hNV : localJoin T L ≤ normalizer (V : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (V : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {n : ℕ} (hn' : 1 < n)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ n)) : False := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsSolvable (MulAut.Outer (K ⧸ center K)) :=
    source_unitary_four_outer_solvable hn' hm
  let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  have hplaced := source_local_oddPrimeActor_residual_le_of_solvable_outer
    D hn V hVV hne hVX hNV hp B hB hBC hBV hperm K hK hout
  have hodd : Odd (Nat.card B) := by
    obtain ⟨k,hk⟩ := hB.exists_card_eq
    rw [hk]
    exact hp.pow
  exact source_nonnormal_oddNormalizer_no_placed_unitary_four_component
    D hn V hVV hne hVX hNV B hBC hodd hBV K hplaced (by omega) hm

end CFSG.Quasithin.Chapter10.LocalFixed
