module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.BinaryRecognition.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.BinaryRecognition.DiagramAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.BinaryRecognition.InnerGeometry

/-!
# Binary recognition in the final paragraph of 15.3.35

Conditionally on the selected binary model, the actual Sylow conjugation
action is inner: the Frattini shadow constructs two individually fixed minimal
parabolics, excluding the graph automorphism. The self-centralizing component
therefore fills the centralizer quotient. Maximality subject to F*=O₂ then
excludes dimension five and identifies M_I⁺ = Y₊⁺S⁺ with a two-plane stabilizer
in dimension four. Changing plane coordinates gives the literal marked
equivalence consumed by `Parabolics.no_endNodeParabolic`.

The source adapter derives normalization from 15.3.11(4) and the
generalized-Fitting equality from the quasisimple component and Sylow
supplement. All normality is relative to the intrinsic ambient I. The initial
selection of the small binary model and the terminal four-group contradiction
remain with the caller; neither is assumed in place of geometric recognition.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final paragraph
of the proof of 15.3.35, printed p.1139.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.BinaryRecognition

variable {X I : Type*} [Group X] [Group I] [Finite X] [Finite I]

/-- Inner action fills the ambient group with its component. The source's
maximal local is then precisely the binary end-node parabolic; the
five-dimensional model is excluded during the construction. -/
theorem recognition_of_localConfiguration
    (D M Y S : Subgroup X) [D.Normal] [IsSimpleGroup D] [Group.IsPerfect D]
    (hF : generalizedFitting X = D)
    (hc : centralizer (D : Set X) = ⊥) (hgen : D ⊔ S = ⊤)
    (hmodel : SmallBinaryModel D) (c : LocalConfiguration D M Y S)
    (hn : S ≤ normalizer (Y : Set X)) :
    D = ⊤ ∧ M = Y ⊔ S ∧
      ∃ e : X ≃* BinaryLinear.FourParabolicRadical.Lin,
        (Y ⊔ S).map e.toMonoidHom =
          BinaryLinear.parabolic BinaryLinear.FourParabolicRadical.plane := by
  have hinner := DiagramAction.inner_of_localConfiguration D M Y S hF hc hgen
    hmodel c hn
  have hD := eq_top_of_inner_action D S hc hgen hinner
  have ctop : LocalConfiguration (⊤ : Subgroup X) M Y S := hD ▸ c
  obtain ⟨n, hn, ⟨a⟩⟩ := smallBinaryModel_linear hmodel
  rcases hn with rfl | rfl
  · let e := ambientEquivOfComponentEqTop D hD a
    obtain ⟨hM, W, hW, hYS⟩ := InnerGeometry.four_plane_marking ctop e
    obtain ⟨b, hb⟩ := exists_marked_equiv_of_plane (Y ⊔ S) e W hW hYS
    exact ⟨hD, hM, b, hb⟩
  · exact (InnerGeometry.not_equiv_linear_five ctop
      (ambientEquivOfComponentEqTop D hD a)).elim

/-- Recognition in the actual centralizer quotient, with the subgroup marking
composed with its original quotient map. The input F* equality is 15.3.41(1),
the local configuration is 15.3.41(2), and normalization comes from 15.3.11(4).
The component's simplicity and faithful conjugation action are derived from L. -/
theorem recognize_quotient
    (L MI Yplus S : Subgroup I) [L.Normal] [IsQuasisimple L]
    (hgen : L ⊔ S = ⊤)
    (hF : generalizedFitting (CentralizerQuotient L) = centralizerQuotientComponent L)
    (hmodel : SmallBinaryModel (centralizerQuotientComponent L))
    (c : LocalConfiguration (centralizerQuotientComponent L)
      (MI.map (centralizerQuotientMap L)) (Yplus.map (centralizerQuotientMap L))
      (S.map (centralizerQuotientMap L)))
    (hn : S ≤ normalizer (Yplus : Set I)) :
    centralizerQuotientComponent L = ⊤ ∧
      MI.map (centralizerQuotientMap L) = (Yplus ⊔ S).map (centralizerQuotientMap L) ∧
      ∃ e : CentralizerQuotient L ≃* BinaryLinear.FourParabolicRadical.Lin,
        (Yplus ⊔ S).map (e.toMonoidHom.comp (centralizerQuotientMap L)) =
          BinaryLinear.parabolic BinaryLinear.FourParabolicRadical.plane := by
  let q := centralizerQuotientMap L
  let D := centralizerQuotientComponent L
  let : D.Normal := (inferInstance : L.Normal).map q (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup D := centralizerQuotientComponent_simple L
  let : IsQuasisimple D := IsQuasisimple.of_surjective (q.subgroupMap L)
    (q.subgroupMap_surjective L)
  have hnq : S.map q ≤ normalizer (Yplus.map q : Set (CentralizerQuotient L)) :=
    (map_mono hn).trans (Yplus.le_normalizer_map q)
  obtain ⟨hD, hMI, e, he⟩ := recognition_of_localConfiguration D (MI.map q)
    (Yplus.map q) (S.map q) hF (centralizerQuotientComponent_centralizer L)
    (component_join_eq_top L S hgen) hmodel c hnq
  refine ⟨hD, ?_, e, ?_⟩
  · simpa only [Subgroup.map_sup] using hMI
  · simpa only [← Subgroup.map_sup, Subgroup.map_map] using he

/-- The binary branch of the final paragraph of 15.3.35, using the original
Sylow subgroup, relative quasisimple component and normalizer conclusion.
The kernel centralizes Y₊, so quotient containment lifts S into M_I. This
discharges normalization; the Sylow supplement also supplies the F* equality.
No inner action, parabolic witness or dimension-five exclusion is assumed. -/
theorem recognize_quotient_of_source
    (L MI Yplus S : Subgroup I) [L.Normal] [IsQuasisimple L]
    (hYL : Yplus ≤ L) (hgen : L ⊔ S = ⊤)
    (hS : ∃ P : Sylow 2 I, (P : Subgroup I) = S)
    (hN : normalizer (Yplus : Set I) = MI)
    (hmodel : SmallBinaryModel (centralizerQuotientComponent L))
    (c : LocalConfiguration (centralizerQuotientComponent L)
      (MI.map (centralizerQuotientMap L)) (Yplus.map (centralizerQuotientMap L))
      (S.map (centralizerQuotientMap L))) :
    centralizerQuotientComponent L = ⊤ ∧
      MI.map (centralizerQuotientMap L) = (Yplus ⊔ S).map (centralizerQuotientMap L) ∧
      ∃ e : CentralizerQuotient L ≃* BinaryLinear.FourParabolicRadical.Lin,
        (Yplus ⊔ S).map (e.toMonoidHom.comp (centralizerQuotientMap L)) =
          BinaryLinear.parabolic BinaryLinear.FourParabolicRadical.plane := by
  have hker : (centralizerQuotientMap L).ker ≤ MI := by
    rw [centralizerQuotientMap, QuotientGroup.ker_mk', ← hN]
    exact (centralizer_le hYL).trans (Subgroup.centralizer_le_normalizer _)
  have hSM : S ≤ MI := by
    have h := map_le_iff_le_comap.mp c.sylow_le
    rwa [comap_map_eq, sup_eq_left.mpr hker] at h
  have hn : S ≤ normalizer (Yplus : Set I) := hN ▸ hSM
  obtain ⟨P, hP⟩ := hS
  have hF : generalizedFitting (CentralizerQuotient L) = centralizerQuotientComponent L :=
    centralizerQuotient_generalizedFitting L
      (isPGroup_quotient_of_sup_eq_top L S (hP ▸ P.isPGroup') hgen)
  exact recognize_quotient L MI Yplus S hgen hF hmodel c hn

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.BinaryRecognition
