module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondNoncommuting
public import Theory.GroupTheory.PResidual.IndexThreeCommutator
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# Thompson movement in the actual second amalgam

The original solvable join normalizes ordinary J(T), hence so does its
plane parabolic. The first flag and that plane parabolic generate LT.
If the first flag also normalized J(T), uniqueness over LT would put the
original escaping join inside N_G(L). Thus J(T) escapes the first flag's
two-core, and the index-three commutator criterion gives L₁=[L₁,J(T)].
The second vertex normalizes J(T), so its core contains J(T). Consequently
the two vertex cores differ, as required for the genuine F.6.11 quotient.

This uses the literal original residual and ordinary Thompson subgroup.
It supplies no model selection or completed plane exclusion.
Source: Aschbacher--Smith 13.4.7(3), printed p.903, using 13.2.2(4).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

theorem original_plane_second_thompson
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hs : Group.IsSolvable (A ⊔ B : Subgroup G))
    (hcomm : ¬ ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G))
    (Wplane : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hWplane : Module.finrank (ZMod 2) Wplane = 2)
    (hTplane : (T : Subgroup G) ≤ normalizer (m.naturalPreimage Wplane : Set G))
    (hBplane : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage Wplane : Set G))
 :
    let X := A ⊔ B
    let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
    let P := firstFlagNormalizer T L V
    let Q := Y₂ ⊔ (T : Subgroup G)
    let L₁ := (pResidual 2 P).map P.subtype
    let J := elementaryAbelianMaxJ (T : Subgroup G)
    ¬ P ≤ normalizer (J : Set G) ∧ ¬ J ≤ P.pCoreIn 2 ∧
      ⁅L₁,J⁆ = L₁ ∧ P.pCoreIn 2 ≠ Q.pCoreIn 2 := by
  let X := A ⊔ B
  let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
  let P := firstFlagNormalizer T L V
  let Q := Y₂ ⊔ (T : Subgroup G)
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  have hTP : (T : Subgroup G) ≤ P := sylow_le_firstFlagNormalizer
  have hJT : J ≤ (T : Subgroup G) := sSup_le fun _ hA => hA.1
  obtain ⟨_,⟨ep⟩,_,_,_,_,_,_,_,_,_,hQJ⟩ := original_plane_second_amalgam
    h₀ h structural D m hTA hTB eA eB hne hindexL hindexA hindexB hcentral
    hs hcomm Wplane hWplane hTplane hBplane
  have hgen := (original_plane_second_noncommuting h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
    Wplane hWplane hTplane hBplane).1
  obtain ⟨_,_,_,hXJ⟩ := original_pair_solvable_case_three h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
  have hout := (original_pair_outside h.toHypothesis1221 D m hTA hTB eA eB hne
    hindexL hindexA hindexB hcentral).2
  have hJne : J ≠ ⊥ := elementaryAbelianMaxJ_ne_bot_of_finite_pGroup
    (T : Subgroup G) T.isPGroup' (fun he => D.ne_bot (le_bot_iff.mp (he ▸ D.le_sylow)))
  have hnot : ¬ P ≤ normalizer (J : Set G) := by
    intro hn
    have hMJ : L ⊔ (T : Subgroup G) ≤ normalizer (J : Set G) := by
      rw [←hgen]
      exact sup_le hn (le_sup_right.trans hXJ)
    exact hout (hXJ.trans (D.normal_subgroup_normalizer_le h.toHypothesis1221
      (hJT.trans le_sup_right) hJne hMJ))
  have hQPT : P.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow P (T.subtype hTP)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTP] at hh
  have hnotcore : ¬ J ≤ P.pCoreIn 2 := by
    intro hj
    apply hnot
    have he := elementaryAbelianMaxJ_eq_of_intermediate_finite (T : Subgroup G)
      (P.pCoreIn 2) hj hQPT
    change P ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)
    rw [←he]
    exact (P.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image P (pCore 2 P))).trans
        (normalizer_le_normalizer_elementaryAbelianMaxJ (P.pCoreIn 2))
  have hJQ : J ≤ Q.pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le hJT) (hJT.trans le_sup_right) hQJ
  have hdiff : P.pCoreIn 2 ≠ Q.pCoreIn 2 := fun he => hnotcore (he.symm ▸ hJQ)
  refine ⟨hnot,hnotcore,?_,hdiff⟩
  let S := T.subtype hTP
  let R := elementaryAbelianMaxJ (S : Subgroup P)
  have hm : R.map P.subtype = J := by
    rw [←elementaryAbelianMaxJ_map_injective P.subtype P.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTP]
  have hr : ¬ R ≤ pCore 2 P := by
    intro hh
    apply hnotcore
    rw [←hm]
    exact map_mono hh
  have hc := residual_commutator_of_index_three S
    (SymmetricThreeTwoCore.sylow_index_three ep S) R
    (sSup_le fun _ hA => hA.1)
    ((S : Subgroup P).le_normalizer.trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ (S : Subgroup P))) hr
  have hh := congrArg (Subgroup.map P.subtype) hc
  simpa only [map_commutator,hm] using hh

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
