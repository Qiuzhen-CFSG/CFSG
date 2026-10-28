module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.SylowGeometry
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.FivePoint

/-!
# Completion of the marked orthogonal case of K.3.1.2

The actual Hermitian layer model supplies all inner actors, while its ambient
field quotient separates odd and even extensions. The five-point comparison
handles s=1: the alternating action has ratios two and 3/2, and the symmetric
action has exactly the commuting-transposition best offenders, generating G.
For s>1 the cubic minimum exceeds one, proving the absence of FF-offenders
without an H.1 parameter bound. These facts give the orthogonal row of B.4.5.

The threshold family Q retains D.2.1's definition. Its inner actors have rank s
and cannot be conjugate to X of rank s+1. The corrected threshold classification
is reexported separately from the global quadratic minimizing-actor theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, K.3.1.2 p.454,
D.2.1 p.178, B.3.2(4), B.4.2(5), and B.4.5 pp.84, 86–87.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.RankOne
open Representation Representation.BinaryOffender BinaryPermutation
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne
open Matrix.SpecialLinearGroup ChapterB.QuasisimpleSource ChapterB.Offenders
open scoped ENNReal
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {s : ℕ} [NeZero s] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
local instance orthogonalAssemblyAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance orthogonalAssemblySpace : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

namespace OrthogonalModel
variable (M : OrthogonalModel s ρ L)

include M in
omit [Finite G] in
/-- The inner case, including the orthogonal A₅ endpoint. -/
theorem layer_eq_top_ratios (hL : L = ⊤) :
    quadraticRatio ρ = 2 ∧ cubicRatio ρ = 3 / 2 :=
  M.ambient_inner_ratios (fun _ _ => hL ▸ le_top)

omit [Finite G] in
/-- Odd extensions have the complete inner threshold and minimizing families.
The premise that every elementary actor lies in L is discharged by odd index. -/
theorem odd_extension_actors [L.Normal] (ho : Odd L.index) (A : Subgroup G) :
    ((IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A ≤ 2) ↔
      ∃ g : Matrix.SpecialLinearGroup (Fin 2) (Field s),
        A = M.modelImage ((fixedRootGroup s).map (MulAut.conj g).toMonoidHom)) ∧
    ((IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A = quadraticRatio ρ) ↔
      ∃ g : Matrix.SpecialLinearGroup (Fin 2) (Field s),
        A = M.modelImage ((fixedRootGroup s).map (MulAut.conj g).toMonoidHom)) ∧
    ((IsElementaryTwo A ∧ IsCubic ρ A ∧ actionRatio ρ A = cubicRatio ρ) ↔
      ∃ g : Matrix.SpecialLinearGroup (Fin 2) (Field s),
        A = M.modelImage
          ((upperUnipotent (Field s)).map (MulAut.conj g).toMonoidHom)) := by
  have hi (B : Subgroup G) (hB : IsElementaryTwo B) : B ≤ L := by
    let : IsElementaryAbelian 2 B := hB.2
    exact elementary_le_layer_of_odd_index ho B
  exact ⟨M.ambient_inner_quadratic_threshold hi A,
    M.ambient_inner_quadratic_minimizer hi A, M.ambient_inner_cubic_minimizer hi A⟩

omit [Finite G] in
/-- A concrete threshold actor contradicts the printed universal conjugacy
claim: its rank is s, whereas every conjugate of X has rank s+1. -/
theorem fixedRoot_not_conjugate_outerActor [L.Normal]
    {t : G} (ht2 : t ^ 2 = 1) (htL : t ∉ L)
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s)) :
    (IsElementaryTwo (M.modelImage (fixedRootGroup s)) ∧
      IsQuadratic ρ (M.modelImage (fixedRootGroup s)) ∧
      actionRatio ρ (M.modelImage (fixedRootGroup s)) ≤ 2) ∧
    ∀ g : G, M.modelImage (fixedRootGroup s) ≠
      (M.outerActor t).map (MulAut.conj g).toMonoidHom := by
  have hc := M.fixedRoot_calculation
  refine ⟨⟨hc.1, hc.2.1, hc.2.2.2.2.le⟩, ?_⟩
  intro g he
  have hr := congrArg rank he
  rw [hc.2.2.1, rank_map_conj, M.outerActor_rank ht2 htL ht] at hr
  omega

end OrthogonalModel

/-- The source's s>1 assertion that V is not an FF-module, proved directly
from the model's exact ambient ratios rather than unfinished H.1 bounds. -/
theorem SourceHypotheses.orthogonal_not_ff (h : SourceHypotheses ρ L)
    (M : OrthogonalModel s ρ L) (hs : 1 < s) : ¬ IsFFModule ρ := by
  let : FiniteDimensional (ZMod 2) V :=
    FiniteDimensional.of_injective M.coordinates.toLinearMap M.coordinates.injective
  exact fun hf => (not_le_of_gt (h.orthogonal_ambient_ratios M hs).2.2.1)
    ((isFFModule_iff_cubicRatio_le_one ρ).mp hf)

/-- Completion of both five-point cases, including the A₅ ratios.
The S₅ action equivalence is on the original group and representation. -/
theorem SourceHypotheses.orthogonal_fivePoint_case (h : SourceHypotheses ρ L)
    (M : OrthogonalModel 1 ρ L) :
    (L = ⊤ ∧ Nonempty (ActionEquiv ρ
      ((naturalRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype)) ∧
      quadraticRatio ρ = 2 ∧ cubicRatio ρ = 3 / 2) ∨
    ∃ e : ActionEquiv ρ (naturalRepresentation (Fin 5)),
      L.map e.groupEquiv.toMonoidHom = alternatingGroup (Fin 5) ∧
      quadraticRatio ρ = 1 ∧ offenderSubgroup ρ = ⊤ ∧
      (∀ A : Subgroup G, IsBestOffender ρ A ↔
        CaseAFamily 5 (A.map e.groupEquiv.toMonoidHom)) ∧
      ∀ A : Subgroup G, IsBestOffender ρ A →
        A = Subgroup.closure {a | a ∈ A ∧ (e.groupEquiv a).IsSwap} ∧
          ∀ a ∈ A, ∀ b ∈ A, Commute a b := by
  rcases h.fivePoint_alternatives M with ⟨hL, he⟩ | he
  · exact Or.inl ⟨hL, he, M.layer_eq_top_ratios hL⟩
  · exact Or.inr he

/-- The orthogonal row of B.4.5, with the symmetric-five FF exception kept
separate. The model hypothesis is an actual group equivalence and intertwiner. -/
theorem SourceHypotheses.orthogonal_table_bounds (h : SourceHypotheses ρ L)
    (M : OrthogonalModel s ρ L) (hn : 1 < s ∨ L = ⊤) :
    Module.finrank (ZMod 2) V = 4 * s ∧ quadraticRatio ρ ≤ 2 ∧
      1 < cubicRatio ρ ∧ cubicRatio ρ ≤ 3 / 2 ∧ ¬ IsFFModule ρ := by
  let : FiniteDimensional (ZMod 2) V :=
    FiniteDimensional.of_injective M.coordinates.toLinearMap M.coordinates.injective
  have hlo : 1 < cubicRatio ρ := by
    rcases hn with hs | hL
    · exact (h.orthogonal_ambient_ratios M hs).2.2.1
    · rw [(M.layer_eq_top_ratios hL).2]
      rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by simp))]
      norm_num
  exact ⟨M.finrank_eq, M.ratio_upper_bounds.1, hlo, M.ratio_upper_bounds.2,
    fun hf => (not_le_of_gt hlo) ((isFFModule_iff_cubicRatio_le_one ρ).mp hf)⟩

/-- K.3.1.2 on the original source domain, after Hermitian recognition.
It supplies exactly the B.4.5 row or the actual symmetric-five B.4.2(5) action,
including its entire best-offender family and generated subgroup. -/
theorem SourceHypotheses.orthogonal_case (h : SourceHypotheses ρ L)
    (M : OrthogonalModel s ρ L) :
    Module.finrank (ZMod 2) V = 4 * s ∧
      ((1 < cubicRatio ρ ∧ cubicRatio ρ ≤ 3 / 2 ∧ quadraticRatio ρ ≤ 2 ∧
        ¬ IsFFModule ρ) ∨
      (s = 1 ∧ ∃ e : ActionEquiv ρ (naturalRepresentation (Fin 5)),
        L.map e.groupEquiv.toMonoidHom = alternatingGroup (Fin 5) ∧
        quadraticRatio ρ = 1 ∧ offenderSubgroup ρ = ⊤ ∧
        (∀ A : Subgroup G, IsBestOffender ρ A ↔
          CaseAFamily 5 (A.map e.groupEquiv.toMonoidHom)) ∧
        ∀ A : Subgroup G, IsBestOffender ρ A →
          A = Subgroup.closure {a | a ∈ A ∧ (e.groupEquiv a).IsSwap} ∧
            ∀ a ∈ A, ∀ b ∈ A, Commute a b)) := by
  refine ⟨M.finrank_eq, ?_⟩
  by_cases hs : s = 1
  · subst s
    rcases h.orthogonal_fivePoint_case M with ⟨hL, _, _, _⟩ | he
    · have hb := h.orthogonal_table_bounds M (Or.inr hL)
      exact Or.inl ⟨hb.2.2.1, hb.2.2.2.1, hb.2.1, hb.2.2.2.2⟩
    · exact Or.inr ⟨rfl, he⟩
  · have hpos := NeZero.pos s
    have hb := h.orthogonal_table_bounds M (Or.inl (by omega))
    exact Or.inl ⟨hb.2.2.1, hb.2.2.2.1, hb.2.1, hb.2.2.2.2⟩

end CFSG.Quasithin.ChapterK.RankOne
