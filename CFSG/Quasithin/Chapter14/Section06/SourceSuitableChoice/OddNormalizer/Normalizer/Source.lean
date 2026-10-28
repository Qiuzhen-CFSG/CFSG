module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Normalizer.InH
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Alternatives

/-!
# The first normalizer equality in original 14.6.16

For the actual outside H, set S = N_T(H₁). Its index two follows from
14.6.12. The two dihedral factors in H/O₂(H) give N_H(S) = T, without
assuming any containment of N_Mc(S). The original core Q_H lies in S,
and T lies in N_Mc(S), providing the inclusions needed for both later
closure branches.

The solvable and parabolic cases of 14.6.14 must still prove the reverse
inclusion in Mc. This module does not assert (U3) or suitability.

Source: Aschbacher--Smith, 14.6.16, printed p.1035.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
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

/-- The literal index, H-normalizer and core inclusions used by both
remaining closure cases. All ambient source choices are retained. -/
theorem source_exchanged_normalizer_initial
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    S.relIndex (T : Subgroup G) = 2 ∧
      H ⊓ normalizer (S : Set G) = (T : Subgroup G) ∧
      H.pCoreIn 2 ≤ S ∧
      (T : Subgroup G) ≤ Mc ⊓ normalizer (S : Set G) := by
  let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
  obtain ⟨_,_,_,_,hi,_,_⟩ := source_exchanged_support_premises
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 d
  have hn := exchanged_factor_normalizer_in_H a T hH.1.2 p H0 H1 H2 d
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hH.1.2)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.2] at hh
  have hQS : H.pCoreIn 2 ≤ S :=
    le_inf hQT (d.core_le_first.trans H1.le_normalizer)
  have hHMc : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e
      H hH.1 hH.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  have hTN : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    hn.symm.le.trans inf_le_right
  exact ⟨hi,hn,hQS,le_inf (hH.1.2.trans hHMc) hTN⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
