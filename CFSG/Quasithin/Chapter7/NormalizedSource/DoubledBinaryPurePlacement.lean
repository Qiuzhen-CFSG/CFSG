module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryComponentModels
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryG2Placement
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryTrialityPlacement
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryReePlacement
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryClassicalExclusion

/-!
# Root centralization and central-cover lifting for the H1 component

Apply the concrete Sylow root calculations to every actual surviving
nonbinary Lie carrier. In the linear-three, linear-two, and Suzuki rows,
the central sixteen first rules out the exceptional small multipliers.
The remaining models have the required odd covering center directly.
All calculations use the given quotient Sylow, not an unmarked conjugate.

Odd kernel makes the literal quotient map injective on the original
component Sylow. Its marked inner action therefore lifts centralization
of the moving sixteen. Since K centralizes the pure line Z, that same
Sylow centralizes the hyperplane Z ∨ A. Trivial odd core of the original
H then also removes the entire component center. The genuine Cartan
index remains available for the subsequent ambient normalizer argument.

NonFFSourceDoubledBinaryPurePlacement applies these results to the original
chosen module and identifies the hyperplane centralizer with its core.
Source: Aschbacher–Smith, 7.7.3 H1 argument, printed p.706,
refs/quasithin.pdf; the multiplier inputs are I.1.3, printed p.407.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPurePlacement
open DoubledBinaryComponentModels DoubledBinaryRootCentralization DoubledBinaryCoverPlacement
open DoubledBinaryCartan DoubledBinaryG2Placement DoubledBinaryTrialityPlacement DoubledBinaryReePlacement

/-- Every surviving actual model centralizes the sixteen in its original
quotient Sylow, has odd covering center, and has the required large Cartan action. -/
theorem root_cover_and_cartan {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : NonbinaryLieModel (K ⧸ center K))
    (P : Sylow 2 (K ⧸ center K)) (A : Subgroup (K ⧸ center K))
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hAP : A ≤ (P : Subgroup _))
    (hi : ((centralizer (A : Set (K ⧸ center K))).subgroupOf (P : Subgroup _)).index ≤ 2) :
    A ≤ (center P).map (P : Subgroup _).subtype ∧
      Odd (Nat.card (center K)) ∧
      6 < ((centralizer (A : Set (K ⧸ center K))).subgroupOf
        (normalizer (P : Set (K ⧸ center K)))).index := by
  rcases hm with hm | ⟨n,hn,hm | hm | hm | hm⟩ | ⟨m,hm,he⟩
  · refine ⟨bender_centralizes hm P A hAP, ?_,
      lt_of_lt_of_le (by decide) (bender_normalizer_index hm P A hAP hA)⟩
    cases hm with
    | linear n hn he => exact linearTwo_odd_center (linearTwo_degree_ge_four hn he P A hAP hA) he
    | unitary n hn he => exact unitary_odd_center hn he
    | suzuki m hm he => exact suzuki_odd_center (suzuki_parameter_ge_two hm he P A hAP hA) he
  · exact ⟨linear_centralizes hn hm P A hAP hi,
      linearThree_odd_center (linear_degree_ge_four hn hm P A hAP hA hi) hm,
      lt_of_lt_of_le (by decide) (linear_normalizer_index hn hm P A hAP hA hi)⟩
  · exact ⟨symplectic_centralizes hn hm P A hAP hi, symplectic_odd_center hn hm,
      lt_of_lt_of_le (by decide) (symplectic_normalizer_index hn hm P A hAP hA hi)⟩
  · have hz := g2_center_eq_bot (g2_degree_ge_four hn hm P A hA hAP hi) hm
    refine ⟨g2_centralizes hn hm P A hAP hi, ?_,
      lt_of_lt_of_le (by decide) (g2_normalizer_index hn hm P A hA hAP hi)⟩
    rw [hz,card_bot]
    decide
  · exact ⟨triality_centralizes hn hm P A hAP hi,triality_center_odd hn hm,
      lt_of_lt_of_le (by decide) (triality_normalizer_index hn hm P A hA hAP hi)⟩
  · have hne : A ≠ ⊥ := by intro hh; rw [hh,card_bot] at hA; omega
    exact ⟨ree_centralizes hm he P A hAP hi,ree_center_odd hm he,
      lt_of_lt_of_le (by decide) (ree_normalizer_index hm he P A hne hAP hi)⟩

/-- The literal central quotient and its original Sylow suffice for lifting;
no placement of the ambient actor in the component is assumed. -/
theorem original_sylow_centralizes_join
    {G : Type*} [Group G] [Finite G] (H K Z A : Subgroup G)
    (hK : IsComponentIn K H) (hodd : pPrimeCore 2 H = ⊥)
    (hKZ : K ≤ centralizer (Z : Set G))
    (hm : NonbinaryLieModel (K ⧸ center K))
    (hAN : A ≤ normalizer (K : Set G)) (j : A →* K ⧸ center K)
    (hact : ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
      K.normalizerMonoidHom (inclusion hAN a))
    [IsElementaryAbelian 2 j.range] (hcard : Nat.card j.range = 16)
    (P : Sylow 2 K)
    (hAP : j.range ≤ (P.mapSurjective (QuotientGroup.mk'_surjective (center K)) : Subgroup _))
    (hi : ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
      (P.mapSurjective (QuotientGroup.mk'_surjective (center K)) : Subgroup _)).index ≤ 2) :
    center K = ⊥ ∧
      (P : Subgroup K).map K.subtype ≤ centralizer ((Z ⊔ A : Subgroup G) : Set G) ∧
      let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
      j.range ≤ (center Q).map (Q : Subgroup _).subtype ∧
      6 < ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
        (normalizer (Q : Set (K ⧸ center K)))).index := by
  let := hK.quasisimple
  obtain ⟨hcent,ho,hlarge⟩ := root_cover_and_cartan hm _ j.range hcard hAP hi
  have hPA := centralizes_original_sylow K A ho hAN j hact P hcent
  refine ⟨DoubledBinaryClassicalExclusion.component_centerless H K hK hodd ho, ?_,hcent,hlarge⟩
  exact le_centralizer_iff.mpr (sup_le
    (le_centralizer_iff.mp ((map_subtype_le _).trans hKZ))
    (le_centralizer_iff.mp hPA))

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPurePlacement
