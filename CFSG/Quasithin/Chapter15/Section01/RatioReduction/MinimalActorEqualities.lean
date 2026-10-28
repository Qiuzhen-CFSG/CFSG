module
public import CFSG.Quasithin.Chapter3.Section01.SourceSQTKEquality
public import CFSG.Quasithin.Chapter15.Section01.NormalizerSource

/-!
# The minimal actor and literal equalities in the full-module15.1.12 branch

The selected local normalizer supplies every qrc and uniqueness hypothesis.
Apply the general chosen-module theorem to V(M), obtaining one minimal
quadratic actor outside O₂(H), two noncentral chief factors, both rank
identities, equality of the fixed subgroups, and the equality on every
conjugate of V(M). The three earlier15.1.7--8/11 conclusions remain explicit.
For the proper moved-space branch, the general theorem retains the changed
module and its separately constructed qrc configuration.

Source: Aschbacher--Smith15.1.12(1--2), printed pp.1089--1090.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.GroupTheory Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_centralizing_minimal_actor_equalities
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hV : localModule T M ≤ twoCoreIn H)
    (hdual : ¬ DualFF (source_15_1_1_qrcConfiguration hG T hM hH))
    (hq : let d := source_15_1_1_qrcConfiguration hG T hM hH
      letI := d.module_elementary
      quadraticRatio (imageRepresentation (sourceNormalizer T M) (localModule T M)
        d.module_normalized) = 2) :
    let d := source_15_1_1_qrcConfiguration hG T hM hH
    let U := (conjugateSpan H (localModule T M)).subgroupOf H
    let S := T.subtype hH.1.1.2
    letI := d.module_elementary
    letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le H))
    ∃ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup H), ¬ A ≤ pCore 2 H ∧
      IsQuadratic (normalRepresentation U) A ∧
      (∀ B ∈ elementaryAbelianMaxSubgroups (S : Subgroup H),
        ¬ B ≤ pCore 2 H → (pCore 2 H).relIndex A ≤ (pCore 2 H).relIndex B) ∧
      ∀ s : SeriesOn U,
        s.noncentralCount = 2 ∧
        2 * Nat.log 2 ((pCore 2 H).relIndex A) = fixedCodim (normalRepresentation U) A ∧
        fixedCodim (normalRepresentation U) A =
          2 * Nat.log 2 ((centralizer (U : Set H)).relIndex (A ⊓ pCore 2 H)) ∧
        U ⊓ centralizer (A : Set H) = U ⊓ centralizer (A ⊓ pCore 2 H : Set H) ∧
        (∀ i, ¬ s.Central i →
          Nat.log 2 ((pCore 2 H).relIndex A) = fixedCodim (s.factorRepresentation i) A) ∧
        ∀ g : H,
          (fixedCodim (conjugateGenerator d (A ⊓ pCore 2 H) inf_le_right g).toRepresentation ⊤ : ℝ) =
            2 * (Nat.log 2 (subspaceKernel ((normalRepresentation U).comp (A ⊓ pCore 2 H).subtype)
              (conjugateGenerator d (A ⊓ pCore 2 H) inf_le_right g).toSubmodule ⊤).index : ℝ) := by
  let h := source_lemma_15_1_1_1 hG T hM hH
  have hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → sourceNormalizer T M ≤ N → N = M := by
    intro N hN hNL
    exact (lemma_A_5_7_1 hM h.sylow_le inf_le_left
      (sourceNormalizer_covers_action T hM.1.2) N hN).mp hNL
  have hne : localModule T M ≠ ⊥ := by
    intro he
    exact centralInvolutions_ne_bot_of_maximal_local T hM.1
      (bot_unique ((le_conjugateSpanBy _ _).trans he.le))
  exact h.sqtk_minimal_actor_equalities hG hM.1.1 hu hJ hne hV hdual hq
end CFSG.Quasithin.Chapter15.Section01
