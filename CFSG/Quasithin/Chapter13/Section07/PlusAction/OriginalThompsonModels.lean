module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalCubicShape
public import CFSG.Quasithin.ChapterB.Section02.SolvableActionFactors.Subproduct
public import Stellmacher.ElementaryAbelianMaxJMap
/-!
# The original odd-chief Thompson section

The actual group K R₁ has a Sylow two-subgroup R₁ and its reduced
centralizer is its two-core. Noncentral Thompson action therefore supplies
nonempty solvable FF factors. The original three-rank bound leaves at most
two factors, yielding S₃ or S₃ × S₃ for the literal Thompson image.

Source: Aschbacher--Smith 13.7.4(1), printed p.937, applying B.2.16.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

theorem source_primitive_three_thompson_models
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (J : Subgroup H)
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (ho : Odd (Nat.card (J ⧸ pCore 2 J)))
    (hout : ¬ J.map H.subtype ≤ M)
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (hp : IsPGroup 3 (J ⧸ pCore 2 J)) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let R := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
    let X := J.map H.subtype ⊔ R
    let Y := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map (QuotientGroup.mk' (pCore 2 X))
    Nonempty (Y ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (Y ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let R := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
  let X := K ⊔ R
  let KX := K.subgroupOf X
  have hXH : X ≤ H := sup_le (hJC.trans (kernel_le_H (D := F)))
    ((pCoreIn_le 2 _).trans h.local_le)
  let : KX.Normal := normal_subgroupOf_of_le_normalizer (hXH.trans hJn)
  let e : KX ≃* J := (subgroupOfEquivOfLe (show K ≤ X from le_sup_left)).trans
    (J.equivMapOfInjective H.subtype H.subtype_injective).symm
  have hpX : IsPGroup 3 (KX ⧸ pCore 2 KX) := hp.of_equiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  obtain ⟨S,hS⟩ := source_primitive_odd_sylow h J hJC hJn ho
  have hgen : KX ⊔ (S : Subgroup X) = ⊤ := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show K ≤ X from le_sup_left), hS,
      ← MonoidHom.range_eq_map, range_subtype]
  have hc : centralizer (reducedTwoSubgroup X : Set X) = pCore 2 X := by
    apply map_injective X.subtype_injective
    rw [map_centralizer_subtype]
    exact source_primitive_odd_reduced_centralizer h hU J hJC hJn ho
  have hmove : ¬ elementaryAbelianMaxJ (S : Subgroup X) ≤
      centralizer (reducedTwoSubgroup X : Set X) := by
    intro hmove
    have hm := map_mono (f := X.subtype) hmove
    rw [← elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective, hS,
      map_centralizer_subtype] at hm
    exact source_primitive_odd_thompson_movement h hU J hJC hJn ho hout hB
      (hm.trans inf_le_right)
  let U := reducedTwoSubgroup X
  let : IsElementaryAbelian 2 U := isPReduced_reducedPSubgroup.elementary
  let : Group.IsNilpotent (pCore 2 KX) := pCore_isPGroup.isNilpotent
  let : Group.IsNilpotent (KX ⧸ pCore 2 KX) := hpX.isNilpotent
  let : Group.IsSolvable KX := (Group.isSolvable_iff_subgroup_quotient (pCore 2 KX)).mpr
    ⟨inferInstance,inferInstance⟩
  have hQ : IsPGroup 2 (X ⧸ KX) := isPGroup_quotient_of_sup_eq_top KX S S.isPGroup' hgen
  let : Group.IsNilpotent (X ⧸ KX) := hQ.isNilpotent
  let : Group.IsSolvable X := (Group.isSolvable_iff_subgroup_quotient KX).mpr
    ⟨inferInstance,inferInstance⟩
  let q := QuotientGroup.mk' (pCore 2 X)
  have hker : q.ker = centralizer (U : Set X) := (QuotientGroup.ker_mk' _).trans hc.symm
  obtain ⟨f, _, _, hnonempty, heq⟩ := ChapterB.thompson_factors_of_solvable_action U q
    (QuotientGroup.mk'_surjective _) hker S hmove inferInstance (pCore_quotient_pCore_eq_bot 2)
  have hrank : primeRank 3 X ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hXH) (inclusion_injective hXH)).trans
      (source_H_stronglyQuasithin d h 3 Nat.prime_three (by decide))
  have hcount := f.toSolvableFFFactors.count_eq_one_or_two_of_surjective_threeRank
    q (QuotientGroup.mk'_surjective _) hrank
  dsimp only
  change Nonempty (((elementaryAbelianMaxJ (⊤ : Subgroup X)).map q) ≃* _) ∨ _
  rw [heq]
  exact f.toSolvableFFFactors.nonempty_subproduct_models hcount _ hnonempty
end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
