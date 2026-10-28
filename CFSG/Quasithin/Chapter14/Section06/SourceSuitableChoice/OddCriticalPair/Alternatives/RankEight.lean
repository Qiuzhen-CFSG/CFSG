module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Sylow
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Targets
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Dimensions
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCritical

/-!
# Excluding the original rank-eight critical endpoint

The complete second alternative of 14.6.13 supplies a nontrivial first-factor
actor and the central point inside its support. The denominator-to-core
identity and the constructed relative Sylow placement give the noncentral
point contradiction. This uses the literal endpoint and its single conjugator.

The theorem is conditional on the earlier exchanged factors and the fitting,
cubic-prime and normalizer conclusions of 14.6.14--16. It does not claim that
14.6.13 has been proved, nor assume a rank-four action or a Sylow placement.

Source: Aschbacher--Smith 14.6.17(1--2), printed pp.1035--1036.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open OddNormalizer SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))

include hG hempty hM hunique hmany hcard e hab hH

omit hG hempty hM hunique hmany hcard e hab in
/-- The numerical dichotomy for the actual source action. The endpoint and
orthogonal-coordinate assertions of 14.6.13 are separate obligations. -/
theorem source_exchanged_moved_dimension
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    (p = 3 ∧ Module.finrank (ZMod 2)
      (subspaceCommutator a.representation ⊤ ⊤) = 4) ∨
      Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 8 :=
  exchanged_moved_dimension a (T : Subgroup G) hH.1.2 p H0 H1 H2 d

/-- The second alternative of 14.6.13 is impossible after the separate
14.6.14--16 inputs. No Sylow placement or fixed-vector premise remains. -/
theorem source_rankEight_impossible
    (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hF : residual H ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hN : Mc ⊓ normalizer
      (((T : Subgroup G) ⊓ normalizer (H1 : Set G) : Subgroup G) : Set G) =
        (T : Subgroup G)) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    letI : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    ¬ Nonempty (RankEightCriticalPlacement h a Mc H1) := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  change ¬ Nonempty (RankEightCriticalPlacement h a Mc H1)
  intro ⟨c⟩
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds
    hG T hempty hM hunique hmany hcard e hab H hH
  have hγ : c.endpoint.conjugate D.UH ≤ D.H :=
    c.endpoint.large_le hb
  have hd := c.strict
  rw [critical_denominator_eq h _ hγ] at hd
  exact source_critical_point_not_le_first_support
    hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 d hF hN
    c.endpoint.representative c.outside hγ c.first_actor hd c.point

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
