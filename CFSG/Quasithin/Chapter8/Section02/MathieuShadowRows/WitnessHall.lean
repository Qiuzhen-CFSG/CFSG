module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceWitnessSelection
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ParameterBound
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.Bender
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.LinearThree
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.SymplecticFour
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.ComponentBorels
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.ExchangedClauses
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Keeping Hall control with the original geometric witness

The original E.2.2 catalogue gives either a degree-one witness or Hall
control on the actual maximal overgroup. The binary classical and exchanged
branches use their marked, covered Borel calculations. The odd branches
construct a dihedral pair directly. No equality of generation parameters
across a quotient is asserted. All original subgroups and kernels are retained.

This is the source input for bounding a Mathieu pair by its faithful torus
and the full original automizer, rather than by a quotient degree rule.
Source: Aschbacher--Smith E.2.2, E.2.7--14 and 8.2.2--3,
printed pp.215--228,714--716, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterB ChapterE Chapter8.Section02.HermitianSource
open Witnesses Witnesses.BenderPlacement
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]

/-- Construct the original witness together with the Hall control needed
for its higher-degree torus. There is no generation-parameter premise. -/
theorem original_witness_one_or_hall
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (R : Sylow 2 X)
    (hP : IsMinimalParabolicOver R ⊤)
    (V : Subgroup X) [IsElementaryAbelian 2 V] (hVR : V ≤ R)
    (hcore : V ≤ (minimalParabolicMax R hP).pCoreIn 2)
    (hout : ¬ V ≤ minimalParabolicCore R hP)
    (hMV : minimalParabolicMax R hP ≤ normalizer (V : Set X))
    (hfit : generalizedFitting X = pCore 2 X)
    (hret : ∀ x : X, V.map (MulAut.conj x).toMonoidHom ≤ R →
      V.map (MulAut.conj x).toMonoidHom ≤ centralizer (V : Set X)) :
    ∃ (n : ℕ) (w : OriginalWitness R (minimalParabolicMax R hP) V n),
      w.degree = 1 ∨ HallControl R hP := by
  have hRV := (minimalParabolicMax_spec R hP).2.trans hMV
  have hvn := (normal_subgroupOf_iff_le_normalizer hVR).mpr hRV
  have hTI : ∀ x ∈ minimalParabolicMax R hP,
      V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj x).toMonoidHom = V := by
    intro x hx
    exact .inr (mem_normalizer_iff_map_conj_eq.mp (hMV hx))
  have one (hw : Nonempty (OriginalWitness R (minimalParabolicMax R hP) V 1)) :
      ∃ (n : ℕ) (w : OriginalWitness R (minimalParabolicMax R hP) V n),
        w.degree = 1 ∨ HallControl R hP := by
    obtain ⟨w⟩ := hw
    exact ⟨1,w,.inl (Nat.dvd_one.mp w.degree_dvd)⟩
  have hall (hc : HallControl R hP) :
      ∃ (n : ℕ) (w : OriginalWitness R (minimalParabolicMax R hP) V n),
        w.degree = 1 ∨ HallControl R hP := by
    obtain ⟨n,⟨w⟩⟩ := exists_original_witness_of_normalized_returns
      hX R hP V hVR hcore hout hMV hfit hret
    exact ⟨n,w,.inr hc⟩
  by_cases hs : Group.IsSolvable X
  · obtain ⟨w⟩ := Solvable.solvable_witness R hP hs V hVR hvn hcore hout
    exact one ⟨OriginalWitness.of_dihedral w⟩
  obtain ⟨K,hK,hqs,hgen,_⟩ := Structure.source_original_component hX R hP hs
  by_cases hn : K.Normal
  · let := hn
    have hc := source_single_clauses R hP hs K hK hqs hgen
    rcases source_normal_geometric_cases ChapterA.Section02.theoremA_knownSimple
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hX R hP hs K hK hgen with
      h2 | h3 | hb | hl | hsp | hbi
    · obtain ⟨p,d,hp,hp3,hd,hd2,hmod,F,hF,hfin,hcard,e,_⟩ := h2
      have ho : Odd p := hp.odd_of_ne_two (by omega)
      have hlarge : 5 < p^d := by
        rcases (show d=1 ∨ d=2 by omega) with hd | hd
        · subst d; simp only [pow_one] at hmod ⊢; omega
        · subst d; nlinarith
      have hnine : p^d ≠ 9 := by
        intro he
        rcases (show d=1 ∨ d=2 by omega) with hd | hd
        · subst d; simp only [pow_one] at he; rw [he] at hp; norm_num at hp
        · subst d; nlinarith
      obtain ⟨w⟩ := OddLinearTwo.source_original ChapterA.Section02.theoremA_knownSimple
        hX R hP hs K hK hgen hp ho hlarge hnine ⟨F,hF,hfin,hcard,⟨e⟩⟩
        V hVR hvn hcore hout
      exact one ⟨OriginalWitness.of_dihedral w⟩
    · obtain ⟨p,hp,ho,_,hu | hl⟩ := h3
      · obtain ⟨w⟩ := OddDegreeThree.unitary_source_original R hP hs K hK hgen
          hp ho hu.2 V hVR hvn hcore hout
        exact one ⟨OriginalWitness.of_dihedral w⟩
      · obtain ⟨_,F,hF,hfin,hcard,e,_⟩ := hl
        obtain ⟨w⟩ := OddDegreeThree.linear_source_original_of_ti R hP hs K hK hgen
          hp ho ⟨F,hF,hfin,hcard,⟨e⟩⟩ V hVR hvn hcore hout hTI
        exact one ⟨OriginalWitness.of_dihedral w⟩
    · obtain ⟨f,hm⟩ := source_bender_model R hP hs K hK hgen hb
      exact hall (bender_hallControl R hP hK hc hm)
    · obtain ⟨f,hf,hm⟩ := hl
      by_cases he : f = 1
      · subst f
        exact one (LinearThree.source_original R hP hs K hK hgen (by decide)
          hm V hVR hvn hcore hout)
      have hmodel := source_binary_linear_three_model R hP hs K hK hgen (by omega) hm
      rcases hmodel with ⟨F,hF,hfin,hchar,_,hcard,e,he,_⟩ | ⟨F,hF,hfin,hchar,_,hcard,e,he,_⟩
      · exact hall (DiagramHall.linear_hallControl (by omega) hcard R hP K hK hc e he)
      · exact hall (DiagramHall.symplectic_hallControl R hP hK hc (by omega) hcard e he)
    · obtain ⟨f,hf,hm⟩ := hsp
      have hmodel := source_binary_symplectic_model R hP hs K hK hgen hf hm
      rcases hmodel with ⟨F,hF,hfin,hchar,_,hcard,e,he,_⟩ | ⟨F,hF,hfin,hchar,_,hcard,e,he,_⟩
      · exact hall (DiagramHall.linear_hallControl (by omega) hcard R hP K hK hc e he)
      · exact hall (DiagramHall.symplectic_hallControl R hP hK hc (by omega) hcard e he)
    · obtain ⟨eK⟩ := hbi
      rcases Witnesses.SymplecticFour.Binary.source_original R hP hs K hK hgen eK
        V hVR hvn hcore hout with hw | ⟨w,ξ,S,hVS⟩
      · exact one hw
      · have hNV := minimalParabolic_normalizer_le R hP V
          (IsElementaryAbelian.isPGroup 2 V) hRV hout
        exact (original_pair_symplectic_excluded w hVR hRV hcore hNV hMV hfit hret
          1 (by decide) (by simp) ξ S hVS).elim
  · obtain ⟨n,hm,hw⟩ := PairedBender.original_source ChapterA.Section02.theoremA_knownSimple
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hX R hP hs K hK hgen hn
      V hVR hvn hcore hout
    have hc := source_exchanged_clauses (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      hX R hP hs hK hqs hgen hn
    have hall_of_model {f : ℕ} (hm : ExchangedModel (minimalParabolicMax R hP) K f) :
        HallControl R hP := by
      obtain ⟨N,hNM,hn,hgen,hd⟩ := ExchangedHall.normal_section hc hK hqs
        (minimalParabolicMax_spec R hP).2 (ExchangedHall.model_overlap_commutator hm)
      exact ExchangedHall.hallControl_of_normal_section R hP N hNM hn hgen hd
    cases hm with
    | linear hf hm =>
      exact hall (hall_of_model (source_component_linear_borel_model
        ChapterA.Section02.theoremA_knownSimple hX R hP hs K hK hgen hf hm))
    | suzuki hf hm =>
      exact hall (hall_of_model (source_component_suzuki_borel_model
        ChapterA.Section02.theoremA_knownSimple hX R hP hs K hK hgen (by omega) hm))
    | odd p hp ho hl hm => exact one hw

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
