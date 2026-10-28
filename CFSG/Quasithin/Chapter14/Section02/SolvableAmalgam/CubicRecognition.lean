module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.Source
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.CentralOmegaCubic

/-!
# Actual marked recognition for the cubic branch of 14.2.20

The selected outside subgroup centralizes the original Sylow omega-center.
Together with the proved characteristic-two and core-free pair hypotheses,
this removes both small residuals and gives the actual G₂ or Mathieu marked
amalgam. All geometric recognition inputs are proved; the subsequent local
rigidity and ambient completion arguments remain separate source steps.

Source: Aschbacher--Smith14.2.21, printed p.988, the cubic F.1.12 application.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G]

/-- Original cubic marked recognition from the full selected source context. -/
theorem source_cubic_marked_amalgam
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eH : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    ExceptionalMarkedAmalgam H X ∨ ExceptionalMarkedAmalgam X H := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hXM : X ≤ M := sup_le (sourceResidual_le _ _) hM.1.2
  obtain ⟨hF,hHX,_,_,_,_,hHZ⟩ := source_hypothesis_F_1_1 hG T hempty hM hu hmany hcard e
    H hH (Or.inr (Or.inr ⟨eH⟩))
  have hXH : X ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T hTX hXM
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  have hc (A : Subgroup G) (hA : A ∈ Chapter1.HOver G (T : Set G)) :
      centralizer (pCore 2 A : Set A) ≤ pCore 2 A :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hA)
  obtain ⟨_,⟨eX⟩⟩ := source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  exact ChapterF.Source.exceptional_cubic_of_centralized_omegaCenter H X T
    hH.1.1.2 hTX hHX eH eX (hc H hH.1.1)
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 (hc X hXH))
    (source_solvable_amalgam_twoCore_eq_bot hG T hempty hM hu hmany hcard e H hH.1.2) hHZ

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
