module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionModel

/-!
# The source corank and common-line conclusions

The actual natural automizer supplies the upper action-rank bound, while
s(G,B)=n supplies the lower bound. This proves 6.1.10(3) whenever the
conjugate normalizes B, without requiring it to lie in the chosen Sylow.

For 6.1.11, the printed nonzero-commutator and intersection hypotheses give
mutual normalization. The proved natural-offender geometry identifies both
centralizers, the commutator, and the intersection with Z_S. The earlier
normalizer factorization supplies fusion by C_G(Z_S). That factorization
remains explicit here and is discharged in the Chapter 12 application.

Source: Aschbacher--Smith, 6.1.10(3) and 6.1.11, printed p.670
(PDF p.687). Conjugation here is the left action of `MulAut.conj`.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- Source 6.1.10(3), for every normalizing noncentralizing conjugate. -/
theorem conjugate_action_corank_eq_of_natural
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n)
    (g : G)
    (hg : (layer L V).map (MulAut.conj g).toMonoidHom ≤ normalizer (layer L V : Set G))
    (hnon : ¬ (layer L V).map (MulAut.conj g).toMonoidHom ≤
      centralizer (layer L V : Set G)) :
    ChapterE.subgroupCorank ((layer L V).map (MulAut.conj g).toMonoidHom)
      ((layer L V).map (MulAut.conj g).toMonoidHom ⊓ centralizer (layer L V : Set G)) = n := by
  let := h.layer_elementary
  exact conjugate_action_corank_eq_of_rank_bound (layer L V) hs
    (elementaryActionRankBound_of_natural h hnatural hE) g hg hnon

/-- All conclusions of source 6.1.11, including both common centralizers.
The only local input beyond naturality and E.6.1 is the earlier 6.1.9(5)
factorization, whose Chapter 12 construction is independent of fusion. -/
theorem mutual_conjugate_source_of_natural
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n)
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L V))
    (g : G) (hg : (layer L V).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (hnon : ⁅layer L V, (layer L V).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hcomm : ⁅layer L V, (layer L V).map (MulAut.conj g).toMonoidHom⁆ ≤
      layer L V ⊓ (layer L V).map (MulAut.conj g).toMonoidHom) :
    let B := layer L V
    let A := B.map (MulAut.conj g).toMonoidHom
    let Z := ZS (T : Subgroup G) L V
    B ⊓ centralizer (A : Set G) = Z ∧ A ⊓ centralizer (B : Set G) = Z ∧
      ⁅B, A⁆ = Z ∧ B ⊓ A = Z ∧
      ∃ c ∈ centralizer (Z : Set G), A = B.map (MulAut.conj c).toMonoidHom := by
  have hnon' : ¬ (layer L V).map (MulAut.conj g).toMonoidHom ≤
      centralizer (layer L V : Set G) := by
    intro hc
    exact hnon (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))
  have hmut : layer L V ≤
      normalizer ((layer L V).map (MulAut.conj g).toMonoidHom : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr (hcomm.trans inf_le_right)
  obtain ⟨hfix, hcentral, hbracket, hinter, _⟩ :=
    mutual_conjugate_line_geometry h hnatural hs
      (elementaryActionRankBound_of_natural h hnatural hE)
      (naturalOffenderFixedLines_of_natural h hnatural hE) g hg hnon' hmut
  exact ⟨hfix, hcentral, hbracket, hinter,
    mutualConjugateFusion_of_natural_action h hnatural hE hs hfactor g hg hnon' hmut⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
