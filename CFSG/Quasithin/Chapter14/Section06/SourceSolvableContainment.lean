module
public import CFSG.Quasithin.Chapter14.Section06.SourceSolvableSelection
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.CubicBorelCompletion
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.SwappingTerminal
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Source

/-!
# Original 14.6.11 and 14.6.18 from the earlier exchanged factors

A solvable outside subgroup supplies a minimal outside subgroup at the largest
odd prime occurring in any outside two-core quotient. Earlier 14.6.12 gives its
literal exchanged factors and also applies to each fresh cubic subgroup used by
14.6.14. The proved normalizer and Fitting results therefore construct the same
terminal witness. The rank-three theorem contradicts its rank-four residual
span. This proves solvable containment in the original selected M, and then
odd-core triviality by the original odd-core descent.

The earlier 14.6.12 family and whole-core A6 reconstruction remain independent
source premises. In particular, neither maximal-prime selection, fitting
containment, normalizer equality nor terminal geometry is an extra premise.
Source: Aschbacher--Smith, 14.6.11--18, printed pp.1030--1037.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open OddNormalizer
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal earlier 14.6.12 conclusion for each primitive minimal outside
subgroup, with its actual span, central line, quotient action and factor preimages.
The prime remains the one supplied by the primitive reduction. -/
@[expose] def SourceExchangedFactorFamily (T : Sylow 2 G) (M : Subgroup G) : Prop :=
  ∀ J : Subgroup G, J ∈ Chapter3.HStar (T : Subgroup G) M →
    ∀ p : ℕ, (p = 3 ∨ p = 5) → PrimitiveResidual J p →
      pResidual 2 (J ⧸ pCore 2 J) ≠ ⊥ →
      ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J),
        let := hU
        ∃ a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T),
          ∃ J0 J1 J2 : Subgroup G, ExchangedFactorSetup a (T : Subgroup G) p J0 J1 J2

omit [Finite G] in
/-- The earlier factor family applies to every fresh cubic subgroup in the
Borel argument, not only to the subsequently selected maximal-prime witness. -/
theorem source_earlier_cubic_orders_of_factor_family
    {T : Sylow 2 G} {M : Subgroup G} (h12 : SourceExchangedFactorFamily T M) :
    EarlierCubicFactorOrders (T : Subgroup G) M := by
  intro J hJ hp hne
  obtain ⟨hU,a,J0,J1,J2,d⟩ := h12 J hJ 3 (Or.inl rfl) hp hne
  let := hU
  exact cubic_orders_of_exchanged_factors (T : Subgroup G) J _ _ J0 J1 J2 a d

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

/-- A solvable outside member constructs the original terminal witness from
14.6.12; all intervening 14.6.13--17 inputs are discharged on the same J. -/
theorem source_terminal_witness_of_solvable_outside
    (h12 : SourceExchangedFactorFamily T M)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hs : Group.IsSolvable H) :
    SourceTerminalWitness hG T hempty hM hu hmany hcard e hab := by
  obtain ⟨J,hJ,_hs,p,hp,hprim,hne,hmax⟩ := source_maximal_primitive_outside_of_solvable
    hG T hempty hM hu hmany hcard e hab H hH hs
  obtain ⟨hU,a,J0,J1,J2,d⟩ := h12 J hJ p hp hprim hne
  let := hU
  obtain ⟨hp3,_hindex,hN⟩ := source_prime_normalizer_of_earlier_cubic_orders
    hG T hempty hM hu hmany hcard e hab J hJ.1 a p J0 J1 J2 hprim d hmax
      (source_earlier_cubic_orders_of_factor_family h12)
  subst p
  exact OddCriticalPair.Selection.source_terminal_witness_of_exchanged_factors
    hG T hempty hM hu hmany hcard e hab J hJ.1 a J0 J1 J2 d
    (source_residual_le_fittingPreimage hG T hempty hM hu hmany hcard e hab
      J hJ.1 a 3 J0 J1 J2 hprim d) hN

/-- Original 14.6.18, conditional only on the independent earlier factor and
whole-core reconstruction families. The overgroup M is the original one. -/
theorem source_solvable_le_selected_of_earlier_factors
    (h12 : SourceExchangedFactorFamily T M)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hs : Group.IsSolvable H) : H ≤ M := by
  by_contra hout
  exact source_terminal_contradiction_of_a6_reconstruction
    hG T hempty hM hu hmany hcard e hab ha
    (source_terminal_witness_of_solvable_outside hG T hempty hM hu hmany hcard e hab
      h12 H ⟨hH,hout⟩ hs)

/-- Original 14.6.11 on the literal quotient H/O2(H), under the same independent
source premises as the solvable-containment corollary. -/
theorem source_oddCore_eq_bot_of_earlier_factors
    (h12 : SourceExchangedFactorFamily T M)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G)) :
    pPrimeCore 2 (H ⧸ pCore 2 H) = ⊥ := by
  by_contra hne
  obtain ⟨J,_hJH,hJ,hs⟩ := source_solvable_minimal_outside_of_oddCore
    hG T hempty hM hu hmany hcard e hab H hH hne
  exact hJ.1.2 (source_solvable_le_selected_of_earlier_factors
    hG T hempty hM hu hmany hcard e hab h12 ha J hJ.1.1 hs)

end CFSG.Quasithin.Chapter14.Section06
