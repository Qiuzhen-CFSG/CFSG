module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.Ordering
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.NaturalModels.Intersections

/-!
# Noncentral action at the unique source ordering maximum

Source14.1.9 excludes Mc for the actual unique ordering maximum.
Applying the original14.1.7 producer then supplies both natural-action
alternatives, including their exact E and Z intersections, without an
additional M≠Mc or central-line premise. This is the noncentral branch
used at the start of15.1.9, printed p.1088.

The centralizing branch and selection of Mf still require their genuine
earlier source theorems. No characteristic-pair existence is assumed here.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
open ChapterA.Section05To06
universe u
theorem local_14_1_7_of_unique_ordering_maximal
    {G : Type u} [Group G] [Finite G]
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmax : ∀ L, IsOrderingMaximal T L → L = M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    let hH : M ∈ Chapter1.HOver G (T : Set G) :=
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1, hM.1.2⟩
    let U := (localModule T M).subgroupOf M
    letI := (localModule_reduced_from_source hG T hH).normal
    letI := (localModule_reduced_from_source hG T hH).elementary
    let q := QuotientGroup.mk' (centralizer (U : Set M))
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    (∃ (c : Additive U ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
      (e : (M ⧸ centralizer (U : Set M)) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      (∀ g v, c (ρ g v) = Representation.specialLinearNatural 2 (e g) (c v)) ∧
      Nat.card (localModule T M) = 4 ∧
      ChapterB.thompsonAlpha (T : Subgroup G) ⊓ localModule T M = centralInvolutions T ∧
      Nat.card (centralInvolutions T) = 2) ∨
    (Nonempty (NaturalOrthogonalAction M (localModule T M)) ∧
      Nat.card (localModule T M) = 16 ∧
      Nat.card ↥(ChapterB.thompsonAlpha (T : Subgroup G) ⊓ localModule T M) = 4 ∧
      Nat.card (centralInvolutions T) = 2 ∧
      centralInvolutions T ≤ (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ localModule T M)) := by
  exact local_14_1_7_from_source hA hC hG T hempty hM.1 hunique
    (Or.inl (unique_ordering_maximal_ne_partner_from_source hG T hM hmax hunique hmany)) hJ

end CFSG.Quasithin.Chapter15.Section03.InitialSource
