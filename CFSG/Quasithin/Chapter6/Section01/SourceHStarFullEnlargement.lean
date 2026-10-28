module
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarConsumer
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterRestriction

/-!
# Preserving Hypothesis 6.1.1 under the source enlargement

A nonzero invariant subgroup of one or two A₅ modules is again one or two
copies with the same acting quotient. The original moved layer lies in the
enlarged moved layer, so the original A₅ exclusion rules out that model for
the enlargement. Together with reducedness and noncentrality this supplies
all of Hypothesis 6.1.1 for R₂(LT).

The literal overgroup consumer then needs no extra A₅-exclusion premise.
Source: Aschbacher--Smith 6.1.5, printed p.666, enlargement of V to R₂(LT).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H X : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- The A₅ exclusion is preserved by the actual source enlargement. -/
theorem reduced_enlargement_not_a5 :
    ¬ IsOneOrTwoA5Modules L
      (layer L (reducedSubgroup (L ⊔ (T : Subgroup G)))) := by
  intro hm
  let := h.V_mem.2.1
  let : IsElementaryAbelian 2 (layer L V) := IsElementaryAbelian.of_le h.layer_le_V
  exact h.not_a5 (hm.of_le (layer_le_reduced_layer h.V_mem)
    (normalizer_commutator_ge_right V L) h.nontrivial_action)

/-- All original hypotheses survive replacement of V by R₂(LT). -/
theorem reduced_enlargement :
    Hypothesis611 KnownSimple.IsKnownSimple T L M
      (reducedSubgroup (L ⊔ (T : Subgroup G))) n := by
  exact { h with
    V_mem := reducedSubgroup_mem (L ⊔ (T : Subgroup G))
    nontrivial_action := h.reduced_enlargement_nontrivial
    not_a5 := h.reduced_enlargement_not_a5 }

/-- The literal overgroup consumer with its extra A₅ premise discharged. -/
theorem checked_hstar_enlarged_overgroup_consumer
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hHX : H ≤ X) (hX : X ∈ Chapter1.HOver G (T : Set G)) :
    Hypothesis611 KnownSimple.IsKnownSimple T L M
      (reducedSubgroup (L ⊔ (T : Subgroup G))) n ∧
    (let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
     letI : U.Normal := (h.overgroup_omega_orbit_reduced hX).normal
     letI : IsElementaryAbelian 2 U := (h.overgroup_omega_orbit_reduced hX).elementary
     let C := centralizer (U : Set X)
     let q := QuotientGroup.mk' C
     let ρ : Representation (ZMod 2) (X ⧸ C) (Additive U) :=
       NormalElementaryQuotient.representation U q
         (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
     IsFFModule ρ ∧
       ChapterB.SourceInduction.NontrivialAdequateAlternative
         (ρ.comp (offenderSubgroup ρ).subtype) ∧
       (pResidual 2 H).map (q.comp (inclusion hHX)) ≤ offenderSubgroup ρ) := by
  exact ⟨h.reduced_enlargement,
    (h.checked_hstar_overgroup_consumer hout hH hZH hHX hX
      h.reduced_enlargement_not_a5).2⟩

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
