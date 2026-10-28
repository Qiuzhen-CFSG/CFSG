module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourOddProducts
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.ResidualComponentBender
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.ResidualSymplectic
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThreeResidual
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.OddTwo
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.OddThree
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Classical.Generation
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NumericalBinarySix
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NumericalPairedPrime
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.PairedMarked
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.OddFamilies
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Rank-one generation for the original Hermitian parabolic

The marked image of V in the full maximal-core quotient has order two.
The maximal subgroup normalizes it, hence centralizes it. The actual E.2.2
component catalogue and the central-point model calculations exclude the
Bender and nonbinary symplectic rows, and force field two in the binary
linear-three row. Every remaining row supplies E-generation at one.

Generation lifts through the full solvable maximal core. Even order then
makes the attained minimum exactly one in the original H; no equality of
generation parameters across a quotient is assumed. The literal
chosen-module application is in NonFFSourceNonMathieuHermitianFieldFourGeneration.

Source: Aschbacher–Smith 8.2.9, printed p.720, using E.1.10–14 and E.2.2,
printed pp.212–216, refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]
set_option backward.isDefEq.respectTransparency false

private theorem generation_one_of_central_marker
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (W : Subgroup X) [IsElementaryAbelian 2 W] (hWS : W ≤ S)
    (hWN : (W.subgroupOf (S : Subgroup X)).Normal)
    (hout : ¬W ≤ minimalParabolicCore S hP)
    (hcent : minimalParabolicMax S hP ≤ centralizer (W : Set X)) :
    IsEGenerated 1 X := by
  by_cases hs : Group.IsSolvable X
  · let := hs
    exact isEGenerated_one_of_solvable
  have hres : (pResidual 2 (minimalParabolicMax S hP)).map
      (minimalParabolicMax S hP).subtype ≤ centralizer (W : Set X) :=
    (map_subtype_le _).trans hcent
  obtain ⟨K,hK,_,hgen,_⟩ := Structure.source_original_component hX S hP hs
  by_cases hn : K.Normal
  · let := hn
    rcases source_normal_geometric_cases ChapterA.Section02.theoremA_knownSimple
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hX S hP hs K hK hgen with
      h2 | h3 | hb | hl | hsp | hbi
    · obtain ⟨p,d,hp,hp3,hd,hd2,hmod,F,hF,hfin,hcard,e,_⟩ := h2
      have ho : Odd p := hp.odd_of_ne_two (by omega)
      have hlarge : 5 < p^d := by
        rcases (show d=1 ∨ d=2 by omega) with hd | hd
        · subst d; simp only [pow_one] at hmod ⊢; omega
        · subst d; nlinarith
      exact Structure.NumericalBounds.normal_odd_two_isEGenerated
        ChapterA.Section02.theoremA_knownSimple hX S hP hs K hK hgen ho.pow hlarge
        ⟨F,hF,hfin,hcard,⟨e⟩⟩
    · obtain ⟨p,hp,ho,_,hu | hl⟩ := h3
      · exact Structure.NumericalBounds.normal_odd_three_isEGenerated
          ChapterA.Section02.theoremA_knownSimple hX S hP hs K hK hgen hp ho (.inr hu.2)
      · obtain ⟨_,F,hF,hfin,hcard,e,_⟩ := hl
        exact Structure.NumericalBounds.normal_odd_three_isEGenerated
          ChapterA.Section02.theoremA_knownSimple hX S hP hs K hK hgen hp ho
          (.inl ⟨F,hF,hfin,hcard,⟨e⟩⟩)
    · exact (Witnesses.PairedBender.source_original_component_bender_residual_exclusion
        ChapterA.Section02.theoremA_knownSimple hX S hP hs K hK hgen hb
        W hWS hWN hout hres).elim
    · obtain ⟨f,hf,hm⟩ := hl
      have he := Witnesses.source_linear_three_parameter_eq_one_of_residual_centralizes
        S hP hs K hK hgen (by omega) hm W hWS hWN hout hres
      subst f
      exact Structure.NumericalBounds.normal_classical_isEGenerated
        ChapterA.Section02.theoremA_knownSimple hX S hP hs K hK hgen
        (.inr (.inr ⟨by decide,hm⟩))
    · obtain ⟨f,hf,hm⟩ := hsp
      exact (Witnesses.source_not_nonbinary_symplectic_of_residual_centralizes
        S hP hs K hK hgen (by omega) hm W hWS hWN hout hres).elim
    · exact normal_binary_six_isEGenerated S hP hs K hK hgen hbi
  · rcases source_exchanged_marked_cases ChapterA.Section02.theoremA_knownSimple
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hX S hP hs K hK hgen hn with
      ⟨f,_,hm⟩ | ⟨p,hp,_,hp7,hm⟩
    · have hb : ClassificationModels.IsBenderModel
          (K.map (QuotientGroup.mk' (minimalParabolicCore S hP))) := by
        rcases hm with ⟨F,hF,hfin,hchar,hf,hcard,e,_⟩ | ⟨m,hm,_,e,_⟩
        · exact .linear f hf ⟨F,hF,hfin,hcard,⟨e⟩⟩
        · exact .suzuki m hm ⟨e⟩
      exact (Witnesses.PairedBender.source_original_component_bender_residual_exclusion
        ChapterA.Section02.theoremA_knownSimple hX S hP hs K hK hgen hb
        W hWS hWN hout hres).elim
    · let : Fact p.Prime := ⟨hp⟩
      exact paired_prime_isEGenerated_one ChapterA.Section02.theoremA_knownSimple
        hX S hP hs K hK hgen hn (by omega) hm

/-- A marked involution in the full star quotient forces E-generation at one
in the original minimal parabolic, through its full solvable core. -/
theorem parabolic_generation_one_of_star_involution
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (W : Subgroup X) [IsElementaryAbelian 2 W] (hWS : W ≤ S)
    (hMW : minimalParabolicMax S hP ≤ normalizer (W : Set X))
    (hcard : Nat.card (W.map (QuotientGroup.mk' (minimalParabolicCore S hP))) = 2) :
    IsEGenerated 1 X ∧ generationParameter X = 1 := by
  let J := minimalParabolicCore S hP
  let q := QuotientGroup.mk' J
  let A := W.map q
  let R := S.mapSurjective (QuotientGroup.mk'_surjective J)
  have hgen : IsEGenerated 1 X := by
    by_cases hs : Group.IsSolvable X
    · let := hs
      exact isEGenerated_one_of_solvable
    let : Group.IsSolvable J := minimalParabolic_core_solvable S hP
    apply IsEGenerated.of_normal_solvable_subgroup (by decide) J
    obtain ⟨hPs,hJs⟩ := Structure.source_star_minimal_core_free S hP
    have hmax : minimalParabolicMax R hPs = (minimalParabolicMax S hP).map q :=
      (minimalParabolicMax_map_core S hP q (QuotientGroup.mk'_surjective J)
        (by rw [QuotientGroup.ker_mk'])).symm
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
    have hAR : A ≤ (R : Subgroup (X ⧸ J)) := map_mono hWS
    have hN : minimalParabolicMax R hPs ≤ normalizer (A : Set (X ⧸ J)) := by
      rw [hmax]
      exact (map_mono hMW).trans (le_normalizer_map q)
    have hAN : (A.subgroupOf (R : Subgroup (X ⧸ J))).Normal :=
      (normal_subgroupOf_iff_le_normalizer hAR).mpr
        ((minimalParabolicMax_spec R hPs).2.trans hN)
    have hout : ¬A ≤ minimalParabolicCore R hPs := by
      intro ha
      have hb : A = ⊥ := bot_unique (ha.trans hJs.le)
      change Nat.card A = 2 at hcard
      rw [hb,card_bot] at hcard
      omega
    exact generation_one_of_central_marker
      (Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple hX S hP hs)
      R hPs A hAR hAN hout
      (hN.trans (normalizer_le_centralizer_of_card_two A hcard))
  have heven : 2 ∣ Nat.card X := by
    have ha : Nat.card A ∣ Nat.card (X ⧸ J) := A.card_subgroup_dvd_card
    change Nat.card A = 2 at hcard
    rw [hcard] at ha
    exact ha.trans (card_dvd_of_surjective q (QuotientGroup.mk'_surjective J))
  exact ⟨hgen, (generationParameter_eq_one_iff_of_even heven).mpr hgen⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
