module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeConstructionGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The source right family in the original chosen-module application

These applications construct the prime pair from the selected source family,
including B-normalization, the right Borel and the relative normalizer index.
They retain the actual component choice and family geometry, without assuming
normalization by the left Cartan. The remaining construction and classification
are discharged by qt-d-1222-rankone-cartan-local-to-global, using the shared
family producer qt-d-1222-rankone-generic-global.

Source: Aschbacher--Smith, 5.2.2, pp.647--648, and 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B E R : Subgroup G} {ℛ : Set (Subgroup G)}
  (D : ChosenModule T L V)
include D

/-- The literal F.1.1 consumer with the right clauses constructed from source-family geometry. -/
theorem rankOne_prime_hypothesisF11_of_right_family
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (he : CartanPrimeActor A H p E)
    (d : Global.RightGeometry T L H ℛ) (hR : R ∈ ℛ)
    (hC : (R.subgroupOf (R ⊔ Prime.normalizingSylow T R)).IsCComponent)
    (hz : (Prime.generated L H E R).pCoreIn 2 = ⊥) :
    ChapterF.Source.HypothesisF11 ![E ⊔ Global.sourceS L H, R] (Global.sourceS L H) :=
  d.prime_hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hH c he hR hC hz

/-- The actual chosen module reduces to a genuine amalgam or the two-factor moving branch. -/
theorem rankOne_prime_pair_of_right_family
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (he : CartanPrimeActor A H p E)
    (d : Global.RightGeometry T L H ℛ) (hR : R ∈ ℛ)
    (hC : (R.subgroupOf (R ⊔ Prime.normalizingSylow T R)).IsCComponent) :
    ChapterF.Source.HypothesisF11 ![E ⊔ Global.sourceS L H, R] (Global.sourceS L H) ∨
      ((Prime.generated L H E R).pCoreIn 2 ≠ ⊥ ∧
        ℛ.ncard = 2 ∧ ¬ E ≤ normalizer (R : Set G) ∧
        (Prime.normalizingSylow T R).relIndex (T : Subgroup G) = 2) :=
  d.prime_pair_dichotomy (D.rankOne_generic_input_of_many h hmany hn hpsl) hH c he hR hC

/-- The same selected factor and one element of T give the literal residual-generating pair. -/
theorem rankOne_prime_two_factors_of_right_family
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (he : CartanPrimeActor A H p E)
    (d : Global.RightGeometry T L H ℛ) (hR : R ∈ ℛ)
    (hC : (R.subgroupOf (R ⊔ Prime.normalizingSylow T R)).IsCComponent)
    (hz : (Prime.generated L H E R).pCoreIn 2 ≠ ⊥) :
    ∃ t ∈ (T : Subgroup G), t ∉ Prime.normalizingSylow T R ∧
      ℛ = {R, R.map (MulAut.conj t).toMonoidHom} ∧
      residual H = R ⊔ R.map (MulAut.conj t).toMonoidHom :=
  d.prime_nonzero_core_two_factors
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH c he hR hC hz

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
