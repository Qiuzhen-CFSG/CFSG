module

public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectLift
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Blocks in the ambient two-core quotient

Subnormal two-perfect subgroups are recovered from their images modulo O₂(G)
by taking the two-residual of the full preimage. Consequently equal images
imply equal blocks, and normalizers of the images lift. The intrinsic quotient
X/O₂(X) is isomorphic to the actual image of X in G/O₂(G).

If one block has quasisimple quotient, component calculus gives commutation
of the images of distinct blocks. This is only a quotient assertion; the
perfect-actor argument in `Commutation.PerfectAction` lifts it to the groups.
The cubic/cubic case is not covered by ordinary component calculus.

Source: Aschbacher--Smith C.1.9, printed p.123, and A.4.2(2), printed p.57.
Residual and image arguments are adapted from the checked private proofs in
Chapter15/.../FieldFourCentrality/SourceCubicActor/Commutation, preserving
that original module and avoiding its chapter dependencies.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BlockCommutation
variable {D : Type*} [Group D] [Finite D]

omit [Finite D] in
theorem eq_of_map_eq (A B : Subgroup D) (hA : A.IsSubnormal) (hB : B.IsSubnormal)
    (hpA : IsPPerfect 2 A) (hpB : IsPPerfect 2 B)
    (he : A.map (QuotientGroup.mk' (pCore 2 D)) =
      B.map (QuotientGroup.mk' (pCore 2 D))) : A = B := by
  have hnA : pCore 2 D ≤ normalizer A :=
    le_normalizer_of_isSubnormal_isPPerfect A _ hA hpA pCore_isPGroup
      le_normalizer_of_normal
  have hnB : pCore 2 D ≤ normalizer B :=
    le_normalizer_of_isSubnormal_isPPerfect B _ hB hpB pCore_isPGroup
      le_normalizer_of_normal
  have hs : A ⊔ pCore 2 D = B ⊔ pCore 2 D := by
    simpa only [comap_map_eq, QuotientGroup.ker_mk'] using
      congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 D))) he
  have ha := embedded_pResidual_join_pGroup A (pCore 2 D) hpA pCore_isPGroup hnA
  have hb := embedded_pResidual_join_pGroup B (pCore 2 D) hpB pCore_isPGroup hnB
  rw [hs] at ha
  exact ha.symm.trans hb

noncomputable def coreQuotientEquiv (A : Subgroup D) (hA : A.IsSubnormal) :
    (A ⧸ pCore 2 A) ≃* A.map (QuotientGroup.mk' (pCore 2 D)) := by
  let f := (QuotientGroup.mk' (pCore 2 D)).subgroupMap A
  have he : f.ker = pCore 2 A := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hA).symm
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((QuotientGroup.mk' (pCore 2 D)).subgroupMap_surjective A))

omit [Finite D] in
theorem normalizes_of_commutator_le_core (A B : Subgroup D)
    (hA : IsBlock A) (hc : ⁅A, B⁆ ≤ pCore 2 D) : B ≤ normalizer A := by
  have hnA : pCore 2 D ≤ normalizer A :=
    le_normalizer_of_isSubnormal_isPPerfect A _ hA.subnormal hA.short.twoPerfect
      pCore_isPGroup le_normalizer_of_normal
  have hres := embedded_pResidual_join_pGroup A (pCore 2 D)
    hA.short.twoPerfect pCore_isPGroup hnA
  have hn : B ≤ normalizer ((A ⊔ pCore 2 D : Subgroup D) : Set D) := by
    let q := QuotientGroup.mk' (pCore 2 D)
    have hqc : ⁅A.map q, B.map q⁆ = ⊥ := by
      rwa [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hbn : B.map q ≤ normalizer (A.map q : Set (D ⧸ pCore 2 D)) :=
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hqc)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hh := (map_le_iff_le_comap.mp hbn).trans ((A.map q).le_normalizer_comap q)
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk'] using hh
  rw [← hres]
  exact hn.trans (normalizer_le_normalizer_characteristic_image _ _)

/-- Distinct blocks commute modulo the ambient two-core if one quotient is quasisimple. -/
theorem quotient_commutation (A B : Subgroup D)
    (hA : IsBlock A) (hB : IsBlock B)
    (hqA : IsQuasisimple (A ⧸ pCore 2 A)) (hne : A ≠ B) :
    ⁅A, B⁆ ≤ pCore 2 D := by
  let q := QuotientGroup.mk' (pCore 2 D)
  let := hqA
  have hAc : IsComponent (D ⧸ pCore 2 D) (A.map q) :=
    ⟨hA.subnormal.map (QuotientGroup.mk'_surjective _),
      IsQuasisimple.of_mulEquiv (coreQuotientEquiv A hA.subnormal)⟩
  have hBsub := hB.subnormal.map (QuotientGroup.mk'_surjective (pCore 2 D))
  have hc : ⁅A.map q, B.map q⁆ = ⊥ := by
    rcases hAc.subnormal_dichotomy (B.map q) hBsub with hle | hc
    · rcases hB.short.quotient with hqB | hqB
      · let := hqB
        have hBc : IsComponent (D ⧸ pCore 2 D) (B.map q) :=
          ⟨hBsub, IsQuasisimple.of_mulEquiv (coreQuotientEquiv B hB.subnormal)⟩
        exact (hne (eq_of_map_eq A B hA.subnormal hB.subnormal
          hA.short.twoPerfect hB.short.twoPerfect (hAc.eq_of_le hBc hle))).elim
      · have hcard : Nat.card (B.map q) = 3 :=
          (Nat.card_congr (coreQuotientEquiv B hB.subnormal).toEquiv).symm.trans hqB
        let : IsCyclic (B.map q) := isCyclic_of_prime_card hcard
        let := hAc.2
        have hb : ⁅B.map q, B.map q⁆ = ⊥ :=
          commutator_eq_bot_iff_le_centralizer.mpr
            (le_centralizer_iff_isMulCommutative.mpr inferInstance)
        have ha : A.map q = ⊥ := by
          have hh := (commutator_mono hle hle).trans hb.le
          rwa [commutator_eq_self, le_bot_iff] at hh
        let : IsSimpleGroup (A.map q ⧸ center (A.map q)) := IsQuasisimple.simple
        let : Nontrivial (A.map q) :=
          (QuotientGroup.mk'_surjective (center (A.map q))).nontrivial
        exact ((nontrivial_iff_ne_bot _).mp inferInstance ha).elim
    · exact hc
  rwa [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hc

omit [Finite D] in
/-- The quotient commutator bound gives relative normality and bounds in both cores. -/
theorem pair_core_bound (A B : Subgroup D)
    (hA : IsBlock A) (hB : IsBlock B) (hc : ⁅A, B⁆ ≤ pCore 2 D) :
    B ≤ normalizer A ∧ A ≤ normalizer B ∧
      ⁅A, B⁆ ≤ A.pCoreIn 2 ⊓ B.pCoreIn 2 := by
  have hnA := normalizes_of_commutator_le_core A B hA hc
  have hnB := normalizes_of_commutator_le_core B A hB (by
    rwa [commutator_comm])
  have hp : IsPGroup 2 ↥(⁅A, B⁆ : Subgroup D) := pCore_isPGroup.to_le hc
  refine ⟨hnA, hnB, le_inf ?_ ?_⟩
  · exact le_pCoreIn_of_normalizes hp
      (le_normalizer_iff_commutator_le_left.mp hnA)
      (normalizer_commutator_ge_left A B)
  · exact le_pCoreIn_of_normalizes hp
      (le_normalizer_iff_commutator_le_right.mp hnB)
      (normalizer_commutator_ge_right A B)

/-- A short group with quasisimple two-core quotient is perfect. -/
theorem perfect_of_quasisimple_quotient {L : Type*} [Group L]
    (h : IsShort L) [IsQuasisimple (L ⧸ pCore 2 L)] : Group.IsPerfect L :=
  h.twoPerfect.isPerfect_of_surjective_pGroup_kernel
    (QuotientGroup.mk' (pCore 2 L)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)

end CFSG.Quasithin.ChapterC.BlockCommutation
