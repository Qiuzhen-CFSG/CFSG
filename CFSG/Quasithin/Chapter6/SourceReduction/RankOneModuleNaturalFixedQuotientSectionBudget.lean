module

public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.ReducedNumericalSource
public import Theory.Representation.BinaryOffender.TwoSectionBudget
public import Theory.GroupTheory.GeneralizedFitting.CenterlessTwoQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson
-- The original centralizer-kernel calculation is used to construct the
-- literal LT/O₂(LT) action; its visibility and statement remain unchanged.
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson

/-!
# The common-offender budget on two noncentral original sections

A normal quasisimple component with trivial centralizer acts nontrivially
on each section. The normal-kernel dichotomy therefore makes both section
actions faithful. The genuine reduced minimal-parabolic B.6.9 theorem gives
a lower bound of one actor rank on each section. Their fixed codimensions
add to at most the whole codimension, so a two-rank upper bound forces
equality and makes the same elementary subgroup an offender on both.

The original rank-one input constructs every structural hypothesis on
the literal LT/O₂(LT) action on the original reduced subgroup. No section
faithfulness, numerical lower bound, or classification result is assumed.
Source: Aschbacher--Smith, 5.1.3, printed p.631, using B.6.9, pp.115--116.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ChapterB.SourceInduction
variable {Q X : Type*} [Group Q] [Finite Q]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]

omit [Finite Q] [FiniteDimensional (ZMod 2) X] in
private theorem faithful_of_nontrivial_component
    (ρ : Representation (ZMod 2) Q X) (K : Subgroup Q)
    [K.Normal] [IsQuasisimple K] (hC : centralizer (K : Set Q) = ⊥)
    (hnon : ¬ K ≤ ρ.ker) : Function.Injective ρ := by
  apply ρ.ker_eq_bot_iff.mp
  have hk : IsComponent Q K := ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩
  rcases hk.normal_dichotomy ρ.ker with hle | hc
  · exact (hnon hle).elim
  · apply bot_unique
    exact (commutator_eq_bot_iff_le_centralizer.mp
      ((commutator_comm _ _).trans hc)).trans hC.le

/-- Two noncentral sections consume exactly one rank each. Their
faithfulness and the same-actor FF conclusions are derived from the
normal component and the genuine minimal-parabolic source theorem. -/
theorem section_offenders_of_component_nontrivial
    (ρ : Representation (ZMod 2) Q X) (P : Sylow 2 Q)
    (hP : ChapterB.IsMinimalParabolicOver P ⊤)
    (hcore : pCore 2 Q = ⊥)
    (hcover : Nonempty (SQTKQuotient KnownSimple.IsKnownSimple Q))
    (K : Subgroup Q) [K.Normal] [IsQuasisimple K]
    (hC : centralizer (K : Set Q) = ⊥)
    (U : Subrepresentation ρ) (hU : ¬ K ≤ U.toRepresentation.ker)
    (hquot : ¬ K ≤ U.quotientRepresentation.ker)
    (A : Subgroup Q) (hA : IsElementaryTwo A)
    (hbudget : fixedCodim ρ A ≤ 2 * rank A) :
    Function.Injective U.toRepresentation ∧
      Function.Injective U.quotientRepresentation ∧
      fixedCodim U.toRepresentation A = rank A ∧
      fixedCodim U.quotientRepresentation A = rank A ∧
      fixedCodim ρ A = 2 * rank A ∧
      IsOffender U.toRepresentation A ∧ IsOffender U.quotientRepresentation A ∧
      IsFFModule U.toRepresentation ∧ IsFFModule U.quotientRepresentation := by
  have hfU := faithful_of_nontrivial_component U.toRepresentation K hC hU
  have hfQ := faithful_of_nontrivial_component U.quotientRepresentation K hC hquot
  have hnU := ChapterB.reduced_minimalParabolic_not_strong
    hcover P hP hcore U.toRepresentation hfU
  have hnQ := ChapterB.reduced_minimalParabolic_not_strong
    hcover P hP hcore U.quotientRepresentation hfQ
  have hloU : rank A ≤ fixedCodim U.toRepresentation A :=
    le_of_not_gt (fun hh => hnU ⟨A,hA,hh⟩)
  have hloQ : rank A ≤ fixedCodim U.quotientRepresentation A :=
    le_of_not_gt (fun hh => hnQ ⟨A,hA,hh⟩)
  have hadd := fixedCodim_quotient_add_subrepresentation_le ρ U A
  have heU : fixedCodim U.toRepresentation A = rank A := by omega
  have heQ : fixedCodim U.quotientRepresentation A = rank A := by omega
  have he : fixedCodim ρ A = 2 * rank A := by omega
  have hoU : IsOffender U.toRepresentation A := ⟨hA,heU.le⟩
  have hoQ : IsOffender U.quotientRepresentation A := ⟨hA,heQ.le⟩
  exact ⟨hfU,hfQ,heU,heQ,he,hoU,hoQ,⟨A,hoU⟩,⟨A,hoQ⟩⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterB.SourceInduction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}

/-- The common-offender conclusion on the literal original LT/O₂(LT)
action. Both section kernels are determined from their nontrivial
component actions, with all structural source hypotheses constructed. -/
theorem Input.original_section_offender_budget
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    let J := L ⊔ (T : Subgroup G)
    let V₀ := W.subgroupOf J
    letI := h.reduced_internal.normal
    letI := h.reduced_internal.elementary
    let q := QuotientGroup.mk' (pCore 2 J)
    let hq := QuotientGroup.mk'_surjective (pCore 2 J)
    let hk : q.ker = centralizer (V₀ : Set J) :=
      by exact (QuotientGroup.ker_mk' _).trans h.reduced_centralizer_core.symm
    let ρ := NormalElementaryQuotient.representation V₀ q hq hk
    let K := (L.subgroupOf J).map q
    ∀ (U : Subrepresentation ρ), ¬ K ≤ U.toRepresentation.ker →
      ¬ K ≤ U.quotientRepresentation.ker →
      ∀ A : Subgroup (J ⧸ pCore 2 J), IsElementaryTwo A →
        fixedCodim ρ A ≤ 2 * rank A →
        Function.Injective U.toRepresentation ∧
          Function.Injective U.quotientRepresentation ∧
          fixedCodim U.toRepresentation A = rank A ∧
          fixedCodim U.quotientRepresentation A = rank A ∧
          fixedCodim ρ A = 2 * rank A ∧
          IsOffender U.toRepresentation A ∧ IsOffender U.quotientRepresentation A ∧
          IsFFModule U.toRepresentation ∧ IsFFModule U.quotientRepresentation := by
  let J := L ⊔ (T : Subgroup G)
  let V₀ := W.subgroupOf J
  let B := L.subgroupOf J
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer h.sylow_normalizes)
  let Q := J ⧸ pCore 2 J
  let q : J →* Q := QuotientGroup.mk' _
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : q.ker = centralizer (V₀ : Set J) :=
    (QuotientGroup.ker_mk' _).trans h.reduced_centralizer_core.symm
  let ρ := NormalElementaryQuotient.representation V₀ q hq hk
  let K := B.map q
  let : K.Normal := (inferInstance : B.Normal).map q hq
  change ∀ (U : Subrepresentation ρ), ¬ K ≤ U.toRepresentation.ker →
    ¬ K ≤ U.quotientRepresentation.ker → ∀ A : Subgroup Q,
    IsElementaryTwo A → fixedCodim ρ A ≤ 2 * rank A → _
  intro U hU hquot A hA hbudget
  let eb : B ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let eqB := QuotientGroup.congr (pCore 2 B) (pCore 2 L) eb (pCore_map_iso 2 eb)
  let := h.quotient_quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eqB.symm
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv (coreQuotientEquivImage 2 B)
  let eK : K ≃* (L ⧸ pCore 2 L) := (coreQuotientEquivImage 2 B).symm.trans eqB
  have hsup : B ⊔ (S : Subgroup J) = ⊤ := by
    change L.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [←subgroupOf_sup (show L ≤ J from le_sup_left) le_sup_right,subgroupOf_self]
  have htwo : IsPGroup 2 (Q ⧸ K) :=
    isPGroup_quotient_of_sup_eq_top K ((S : Subgroup J).map q) (S.isPGroup'.map q) (by
      rw [←Subgroup.map_sup,hsup,map_top_of_surjective q hq])
  have hz : center K = ⊥ := by
    apply bot_unique
    intro x hx
    apply eK.map_eq_one_iff.mp
    exact h.quotient_center_eq_bot.le (MulEquivClass.apply_mem_center eK hx)
  have hcore : pCore 2 Q = ⊥ := pCore_quotient_pCore_eq_bot 2
  have hC : centralizer (K : Set Q) = ⊥ :=
    (centralizer_eq_twoCore_of_centerless_quasisimple_quotient K hz htwo).trans hcore
  have hne : q.ker ≠ ⊤ := by
    intro he
    have hK : K = ⊥ := by
      apply bot_unique
      rintro _ ⟨x, _, rfl⟩
      exact he.ge (mem_top x)
    exact hU (hK ▸ bot_le)
  have hP := (ChapterB.minimalParabolic_reduced_image S h.local_minimal_parabolic q hq hcore hne).2
  have hSQ : IsSQTK KnownSimple.IsKnownSimple J := by
    have hJL : J ≤ normalizer (L : Set G) := sup_le L.le_normalizer h.sylow_normalizes
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hJL)).mp
      ((h.qtke.twoLocal_sqtk h.maximal.1).subgroup (J.subgroupOf (normalizer (L : Set G))))
  let cover : SQTKQuotient KnownSimple.IsKnownSimple Q := {
    Cover := J
    kernel := pCore 2 J
    sqtk := hSQ
    equiv := MulEquiv.refl _ }
  exact RankOneRecognition.section_offenders_of_component_nontrivial
    ρ (S.mapSurjective hq) hP hcore ⟨cover⟩ K hC U hU hquot A hA hbudget

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
