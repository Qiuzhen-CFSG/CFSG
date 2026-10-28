module
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.AmbientActors.GlobalActors
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.InnerActors.Transport

/-!
# Ambient minima and corrected threshold actors for the orthogonal branch

The cyclic field quotient separates odd and even extensions. In odd extensions
all elementary actors lie in the layer. In even extensions, the actual pure
involution constructs X, and global placement reduces every outer actor to its
calculated subgroups. Combining those calculations with the proved inner bounds
gives q=2s/(s+1) and qhat=min(3/2,2s/(s+1)). In particular qhat>1 for s>1,
without the unfinished H.1 bound. The quadratic minimizers are exactly the
layer conjugates of X; the threshold family is strictly broader.

All premises of the local action calculations are discharged here. The final
orthogonal family assembly, including the s=1 comparison, remains a consumer.
Source: Aschbacher–Smith, K.3.1.2 p.454 and D.2.1 p.178, manuscript 1 March 2004.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.RankOne
open Representation Representation.BinaryOffender Subgroup
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne
open Matrix.SpecialLinearGroup
open scoped ENNReal
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {s : ℕ} [NeZero s] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
local instance ambientRatioFixedAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance ambientRatioBinarySpace : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))
namespace OrthogonalModel
variable (M : OrthogonalModel s ρ L) [L.Normal]

omit [NeZero s] in
/-- The sharp outer value is strictly between one and two for s>1. -/
theorem outer_ratio_bounds (hs : 1 < s) :
    1 < (2 * s : ℕ) / (s + 1 : ℝ≥0∞) ∧
      (2 * s : ℕ) / (s + 1 : ℝ≥0∞) < 2 := by
  constructor
  · apply (ENNReal.lt_div_iff_mul_lt (Or.inl (by positivity)) (Or.inl (by simp))).mpr
    have hn : 1 * (s + 1) < 2 * s := by omega
    exact_mod_cast hn
  · apply (ENNReal.div_lt_iff (Or.inl (by positivity)) (Or.inl (by simp))).mpr
    have hn : 2 * s < 2 * (s + 1) := by omega
    exact_mod_cast hn

include M in
omit [Finite G] in
/-- Odd field extensions have the same exact ratios as the marked layer. -/
theorem odd_extension_ratios (hodd : Odd L.index) :
    quadraticRatio ρ = 2 ∧ cubicRatio ρ = 3 / 2 := by
  apply M.ambient_inner_ratios
  intro A hA
  let : IsElementaryAbelian 2 A := hA.2
  exact elementary_le_layer_of_odd_index hodd A

/-- Exact ambient minima in the presence of the actual canonical outer involution. -/
theorem pure_extension_ratios (h : SourceHypotheses ρ L) (hs : 1 < s)
    {t : G} (ht2 : t ^ 2 = 1) (htL : t ∉ L)
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s)) :
    quadraticRatio ρ = (2 * s : ℕ) / (s + 1 : ℝ≥0∞) ∧
      cubicRatio ρ = min (3 / 2) ((2 * s : ℕ) / (s + 1 : ℝ≥0∞)) := by
  have hreal := M.coordinates_pure_involution ht2 ht
  have hX := M.outerActor_elementary ht2 htL ht
  have hXq := M.outerActor_quadratic ht2 htL ht hreal
  have hXr := M.outerActor_actionRatio ht2 htL ht hreal
  have hb := outer_ratio_bounds hs
  have hqu : quadraticRatio ρ ≤ (2 * s : ℕ) / (s + 1 : ℝ≥0∞) :=
    iInf_le_of_le _ (iInf_le_of_le ⟨hX, hXq⟩ hXr.le)
  constructor
  · apply le_antisymm hqu
    refine le_iInf fun A => le_iInf fun hA => ?_
    by_cases hAL : A ≤ L
    · exact hb.2.le.trans (M.inner_quadratic_calculation hAL hA.1 hA.2).2
    · exact (M.outer_minimum h hs ht2 htL ht A hA.1 hAL).1
  · apply le_antisymm
    · exact le_min M.ratio_upper_bounds.2 ((cubicRatio_le_quadraticRatio ρ).trans hqu)
    · refine le_iInf fun A => le_iInf fun hA => ?_
      by_cases hAL : A ≤ L
      · exact (min_le_left _ _).trans (M.inner_actionRatio_bound hAL hA.1)
      · exact (min_le_right _ _).trans (M.outer_minimum h hs ht2 htL ht A hA.1 hAL).1

/-- The global quadratic minimizers are precisely the genuine layer conjugates of X. -/
theorem pure_extension_quadratic_minimizer (h : SourceHypotheses ρ L) (hs : 1 < s)
    {t : G} (ht2 : t ^ 2 = 1) (htL : t ∉ L)
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s)) (A : Subgroup G) :
    (IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A = quadraticRatio ρ) ↔
      ∃ c : L, A = (M.outerActor t).map (MulAut.conj (c : G)).toMonoidHom := by
  let : FiniteDimensional (ZMod 2) V :=
    FiniteDimensional.of_injective M.coordinates.toLinearMap M.coordinates.injective
  rw [(M.pure_extension_ratios h hs ht2 htL ht).1]
  constructor
  · rintro ⟨hA, hq, hr⟩
    have hout : ¬ A ≤ L := by
      intro hAL
      have hh := (M.inner_quadratic_calculation hAL hA hq).2
      rw [hr] at hh
      exact (not_le_of_gt (outer_ratio_bounds hs).2) hh
    exact (M.outer_minimum h hs ht2 htL ht A hA hout).2.mp hr
  · rintro ⟨c, rfl⟩
    have hreal := M.coordinates_pure_involution ht2 ht
    rw [InnerTransport.quadratic_conj_iff, InnerTransport.ratio_conj]
    exact ⟨(M.outerActor_elementary ht2 htL ht).map_conj _,
      M.outerActor_quadratic ht2 htL ht hreal, M.outerActor_actionRatio ht2 htL ht hreal⟩

/-- The complete threshold family, with distinct inner and outer alternatives.
The outer alternative retains the cyclic transvections for s=2. -/
theorem pure_extension_quadratic_threshold (h : SourceHypotheses ρ L) (hs : 1 < s)
    {t : G} (ht2 : t ^ 2 = 1) (htL : t ∉ L)
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s)) (A : Subgroup G) :
    (IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A ≤ 2) ↔
      (∃ g : Matrix.SpecialLinearGroup (Fin 2) (Field s),
        A = M.modelImage ((fixedRootGroup s).map (MulAut.conj g).toMonoidHom)) ∨
      (IsElementaryTwo A ∧ ¬ A ≤ L ∧
        (rank A = s ∨ rank A = s + 1 ∨ (s = 2 ∧ rank A = 1))) := by
  constructor
  · intro hA
    by_cases hAL : A ≤ L
    · exact Or.inl ((M.inner_quadratic_threshold hAL).mp hA)
    · exact Or.inr ⟨hA.1, hAL, (M.outer_threshold_iff h hs ht2 htL ht A hA.1 hAL).mp hA.2⟩
  · rintro (⟨g, rfl⟩ | ⟨hA, hout, hr⟩)
    · exact (M.inner_quadratic_threshold (M.modelImage_le_layer _)).mpr ⟨g, rfl⟩
    · exact ⟨hA, (M.outer_threshold_iff h hs ht2 htL ht A hA hout).mpr hr⟩

end OrthogonalModel

/-- The source hypotheses and actual marked model now give both ambient cases,
including the strict cubic lower bound without any H.1 input. -/
theorem SourceHypotheses.orthogonal_ambient_ratios
    (h : SourceHypotheses ρ L) (M : OrthogonalModel s ρ L) (hs : 1 < s) :
    (Odd L.index → quadraticRatio ρ = 2 ∧ cubicRatio ρ = 3 / 2) ∧
      (Even L.index → quadraticRatio ρ = (2 * s : ℕ) / (s + 1 : ℝ≥0∞) ∧
        cubicRatio ρ = min (3 / 2) ((2 * s : ℕ) / (s + 1 : ℝ≥0∞))) ∧
      1 < cubicRatio ρ ∧ cubicRatio ρ ≤ 3 / 2 := by
  let : L.Normal := h.layer_normal
  have hodd := M.odd_extension_ratios
  have heven (he : Even L.index) :
      quadraticRatio ρ = (2 * s : ℕ) / (s + 1 : ℝ≥0∞) ∧
      cubicRatio ρ = min (3 / 2) ((2 * s : ℕ) / (s + 1 : ℝ≥0∞)) := by
    obtain ⟨t, ht2, htL, ht⟩ := M.exists_outer_involution h he
    exact M.pure_extension_ratios h hs ht2 htL ht
  refine ⟨hodd, heven, ?_, M.ratio_upper_bounds.2⟩
  have hthree : (1 : ℝ≥0∞) < 3 / 2 := by
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by simp))]
    norm_num
  rcases Nat.even_or_odd L.index with he | ho
  · rw [(heven he).2]
    exact lt_min hthree (OrthogonalModel.outer_ratio_bounds hs).1
  · rw [(hodd ho).2]
    exact hthree

/-- The complete even-extension quadratic actor classification on the original
source group. The pure involution and every realization premise are constructed. -/
theorem SourceHypotheses.orthogonal_even_actors
    (h : SourceHypotheses ρ L) (M : OrthogonalModel s ρ L)
    (hs : 1 < s) (heven : Even L.index) :
    let : L.Normal := h.layer_normal
    ∃ t : G, t ^ 2 = 1 ∧ t ∉ L ∧
      M.ambientAut t = Theory.PSL2.fieldAut (conjugation s) ∧
      IsElementaryTwo (M.outerActor t) ∧ IsQuadratic ρ (M.outerActor t) ∧
      Module.finrank (fixedField s) (M.fixedModelSpace (M.outerActor t)) = 2 ∧
      rank (M.outerActor t) = s + 1 ∧
      fixedCodim ρ (M.outerActor t) = 2 * s ∧
      actionRatio ρ (M.outerActor t) = (2 * s : ℕ) / (s + 1 : ℝ≥0∞) ∧
      (∀ A : Subgroup G,
        (IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A ≤ 2) ↔
          (∃ g : Matrix.SpecialLinearGroup (Fin 2) (Field s),
            A = M.modelImage ((fixedRootGroup s).map (MulAut.conj g).toMonoidHom)) ∨
          (IsElementaryTwo A ∧ ¬ A ≤ L ∧
            (rank A = s ∨ rank A = s + 1 ∨ (s = 2 ∧ rank A = 1)))) ∧
      (∀ A : Subgroup G,
        (IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A = quadraticRatio ρ) ↔
          ∃ c : L, A = (M.outerActor t).map (MulAut.conj (c : G)).toMonoidHom) := by
  let : L.Normal := h.layer_normal
  obtain ⟨t, ht2, htL, ht⟩ := M.exists_outer_involution h heven
  have hreal := M.coordinates_pure_involution ht2 ht
  exact ⟨t, ht2, htL, ht, M.outerActor_elementary ht2 htL ht,
    M.outerActor_quadratic ht2 htL ht hreal, M.outerActor_fixed_Kfinrank ht2 htL ht hreal,
    M.outerActor_rank ht2 htL ht,
    M.outerActor_fixedCodim ht2 htL ht hreal, M.outerActor_actionRatio ht2 htL ht hreal,
    M.pure_extension_quadratic_threshold h hs ht2 htL ht,
    M.pure_extension_quadratic_minimizer h hs ht2 htL ht⟩

end CFSG.Quasithin.ChapterK.RankOne
