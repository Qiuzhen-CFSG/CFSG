module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateCentralizers

/-!
# Conditional conjugate geometry for the contained case of 6.1.15

For A = B^g ≤ T, A normalizes B. If B also normalizes A, the fusion
conclusion of 6.1.11 and C_G(Z_S) ≤ M contradict noncentralization,
because every M-conjugate of B centralizes B.

Otherwise pull C_A(B) back by g⁻¹. The ordinary and line rows of
6.1.13 force B to normalize A after all. The field row invokes the
independent source argument 6.1.14(5), with B^(g⁻¹) as its conjugate.
This proves the assembly, not its corank, fusion, fixed-space-classification
or field-escape inputs. Their source producers remain to be supplied.

Source: Aschbacher--Smith, proof of 6.1.15, printed p.672.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G]

private theorem map_conj_inverse (B : Subgroup G) (g : G) :
    (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = B := by
  rw [map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, map_id]

private theorem inverse_conjugate_normalizes_iff (B : Subgroup G) (g : G) :
    B.map (MulAut.conj g⁻¹).toMonoidHom ≤ normalizer (B : Set G) ↔
      B ≤ normalizer (B.map (MulAut.conj g).toMonoidHom : Set G) := by
  have he : (B.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = B := by
    simpa only [inv_inv] using map_conj_inverse B g⁻¹
  rw [← map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective,
    he, map_equiv_normalizer_eq]

private theorem inverse_conjugate_centralizes_iff (B : Subgroup G) (g : G) :
    B.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer (B : Set G) ↔
      B.map (MulAut.conj g).toMonoidHom ≤ centralizer (B : Set G) := by
  have step (k : G)
      (hc : B.map (MulAut.conj k⁻¹).toMonoidHom ≤ centralizer (B : Set G)) :
      B.map (MulAut.conj k).toMonoidHom ≤ centralizer (B : Set G) := by
    have hh := (map_mono (f := (MulAut.conj k).toMonoidHom) hc).trans
      (map_centralizer_le_centralizer_image (B : Set G) (MulAut.conj k).toMonoidHom)
    have he : (B.map (MulAut.conj k⁻¹).toMonoidHom).map
        (MulAut.conj k).toMonoidHom = B := by
      simpa only [inv_inv] using map_conj_inverse B k⁻¹
    rw [he] at hh
    exact le_centralizer_iff.mp hh
  refine ⟨step g, fun hc => ?_⟩
  apply step g⁻¹
  simpa only [inv_inv] using hc

variable [Finite G] {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- Assemble 6.1.10(3), 6.1.11, 6.1.13 and 6.1.14(5), retaining their
unproved source inputs explicitly. No 6.1.12(1) escape premise is used. -/
theorem conjugate_layer_centralizes_of_source_geometry
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V))
    (hr : (n : ℕ∞) ≤ ChapterE.globalR (layer L V))
    (hI : centralizer (ZS (T : Subgroup G) L V : Set G) ≤ M)
    (hcorank : ConjugateCorankFormula (T : Subgroup G) (layer L V) n)
    (hfusion : MutualConjugateFusion (T : Subgroup G) (layer L V)
      (ZS (T : Subgroup G) L V))
    (hfixed : FixedSpaceAlternatives L M (layer L V) (ZS (T : Subgroup G) L V) n)
    (hfield : FieldConjugateEscape L M (layer L V) (ZS (T : Subgroup G) L V) n)
    (hn : 2 < n) (g : G)
    (hg : (layer L V).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    (layer L V).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L V : Set G) := by
  by_contra hnon
  have hnot : ¬ layer L V ≤
      normalizer ((layer L V).map (MulAut.conj g).toMonoidHom : Set G) := by
    intro hnorm
    obtain ⟨c, hc, he⟩ := hfusion g hg hnon hnorm
    exact hnon (he.symm ▸ M_conjugate_layer_centralizes h hnatural (hI hc))
  let A := (layer L V).map (MulAut.conj g⁻¹).toMonoidHom
  let U := layer L V ⊓ centralizer (A : Set G)
  have hAU : A ≤ centralizer (U : Set G) := le_centralizer_iff.mpr inf_le_right
  obtain ⟨hU, hcor⟩ := hcorank g hg hnon
  have hordinary (hc : centralizer (U : Set G) ≤ normalizer (layer L V : Set G)) :
      False := hnot ((inverse_conjugate_normalizes_iff (layer L V) g).mp (hAU.trans hc))
  rcases hfixed U inf_le_left hU hcor with hlocal | ⟨l, hl, he⟩ | hfx
  · exact hordinary (source_ordinary_fixed_space_centralizer h hE hr hU inf_le_left hlocal)
  · apply hordinary
    rw [he]
    have hc := conjugate_line_centralizer_le_normalizer h hnatural hE hI 1 l hl
    simpa using hc
  · have hnorm : layer L V ≤ normalizer (A : Set G) := by
      apply (inverse_conjugate_normalizes_iff (layer L V) g⁻¹).mp
      simpa only [inv_inv] using hg.trans h.sylow_normalizes_layer
    have hnon' : ¬ A ≤ centralizer (layer L V : Set G) :=
      fun hc => hnon ((inverse_conjugate_centralizes_iff (layer L V) g).mp hc)
    exact hfield hn g⁻¹ U hU hcor hfx hAU hnorm hnon' hI

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
