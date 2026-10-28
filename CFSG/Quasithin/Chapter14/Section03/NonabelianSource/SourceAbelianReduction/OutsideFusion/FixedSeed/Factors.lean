module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorNormalizerSylow
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorConjugacySolvable

/-!
# The specified outside element exchanges the original factors

The two maximal elementary factors of R are intrinsic. Any element of T
outside RQ fails to normalize either factor, since T ∩ N_G(A) = RQ.
Its conjugate of A must therefore be the other maximal factor. The result
retains the specified element, rather than choosing a new conjugator.

This is the opening factor-exchange step of Aschbacher--Smith 14.3.21(2),
printed p.998, using 14.3.18(4) and 14.3.19(3).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition
variable {G : Type*} [Group G] [Finite G]

/-- Every specified element outside RQ exchanges the original elementary
factors; no order or seed-centralization assumption is needed for this step. -/
theorem source_outside_element_exchanges_factors_of_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (t : G) (ht : t ∈ (T : Subgroup G))
    (htout : t ∉ (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2) :
    let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
    ∃ A B : Subgroup G,
      A ≤ R ∧ B ≤ R ∧ IsElementaryAbelian 2 A ∧ IsElementaryAbelian 2 B ∧
      Nat.card A = 16 ∧ Nat.card B = 16 ∧
      A ⊓ B = rankTwoSeed T M ∧ A ⊔ B = R ∧ Nat.card R = 64 ∧
      F.I₂ (sourceResidual M Mc) ⊔ F.H.pCoreIn 2 ≤ normalizer (A : Set G) ∧
      F.I₂ (sourceResidual M Mc) ⊔ F.H.pCoreIn 2 ≤ normalizer (B : Set G) ∧
      (∀ E : Subgroup G, IsElementaryAbelian 2 E → E ≤ R → E ≤ A ∨ E ≤ B) ∧
      conjugate A t = B := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨A,B,hAR,hBR,hVA,hVB,hEA,hEB,hAc,hBc,hi,hAB,hRc,hAN,hBN,hmax⟩ :=
    maximal_elementary_factors_of_full_orthogonal hG T hempty hM hu hmany hcard e hnot
      F dg hZ hne g hgP hgH hr
  let := hEA
  let := hEB
  obtain ⟨hAU,_⟩ := elementary_factor_core_intersections_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
      A B hAR hBR hVA hVB hEA hEB hmax
  have hnorm := (factor_automizer_sylow_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
      A hAR hVA hAc hAU hAN).1
  have htn : t ∉ normalizer (A : Set G) := fun hh => htout (hnorm ▸ ⟨ht,hh⟩)
  let L := sourceResidual M Mc
  let R := (F.I₂ L).pCoreIn 2
  let : Fact (IsPGroup 2 F.U) := ⟨dg.two⟩
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [dg.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy _ _))
  have hcomm : ⁅F.U,F.U⁆ ≤ F.Vi 1 := by
    rw [←F.U.map_subtype_commutator]
    exact (map_mono (f:=F.U.subtype) (commutator_le_frattini_of_isPGroup (p:=2))).trans hPhi.le
  obtain ⟨_,hIG,hIN⟩ := F.binary_parabolic_span_normality (by decide) L
    h.L_normalizes_seed (h.binarySeedAction_surjective F) hcomm
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    ((F.invariant 2).trans ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN)).trans
      (normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L)))
  let : IsElementaryAbelian 2 (conjugate A t) :=
    IsElementaryAbelian.map (MulAut.conj t⁻¹).toMonoidHom
  have hct : conjugate A t ≤ R := conjugate_le_of_normalizes hAR t (hTR ht)
  have hcc : Nat.card (conjugate A t) = Nat.card A :=
    card_map_of_injective (MulAut.conj t⁻¹).injective
  have heq : conjugate A t = B := by
    rcases hmax (conjugate A t) inferInstance hct with ha | hb
    · exact (htn ((conjugate_eq_iff A t).mp
        (eq_of_le_of_card_ge ha (by rw [hcc])))).elim
    · exact eq_of_le_of_card_ge hb (by rw [hcc,hAc,hBc])
  exact ⟨A,B,hAR,hBR,hEA,hEB,hAc,hBc,hi,hAB,hRc,hAN,hBN,hmax,heq⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
