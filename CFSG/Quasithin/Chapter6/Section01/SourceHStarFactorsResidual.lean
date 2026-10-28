module
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarFactors

/-!
# The two-residual fixes the actual Thompson factors

Conjugation permutes a pair of literal factors, so its stabilizer has index
one or two. The two-residual therefore fixes both factors individually.
Apply this to the actual Thompson image in the H-star centralizer quotient,
and pull the containment back along its original quotient map. The same
conclusion holds for every odd-order subgroup, in particular the source
Hall subgroup `D_L` once it has been placed in `X`.

Source: Aschbacher--Smith, 6.1.5, printed pp.667--668.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.ThompsonImage

/-- An ambient two-residual fixes each subgroup in a conjugacy-invariant pair. -/
theorem residual_le_pair_normalizer {D : Type*} [Group D] [Finite D]
    (A B : Subgroup D)
    (hp : ∀ x : D,
      (A.map (MulAut.conj x).toMonoidHom = A ∧ B.map (MulAut.conj x).toMonoidHom = B) ∨
      (A.map (MulAut.conj x).toMonoidHom = B ∧ B.map (MulAut.conj x).toMonoidHom = A)) :
    pResidual 2 D ≤ normalizer (A : Set D) := by
  let N := normalizer (A : Set D)
  by_cases hn : N = ⊤
  · exact le_top.trans_eq hn.symm
  obtain ⟨a, ha⟩ := SetLike.exists_not_mem_of_ne_top N hn
  have hswap (x : D) (hx : x ∉ N) :
      A.map (MulAut.conj x).toMonoidHom = B ∧ B.map (MulAut.conj x).toMonoidHom = A := by
    rcases hp x with h | h
    · exact (hx (mem_normalizer_iff_map_conj_eq.mpr h.1)).elim
    · exact h
  have hi : N.index = 2 := by
    apply index_eq_two_iff_exists_notMem_and.mpr
    refine ⟨a, ha, fun b => ?_⟩
    by_cases hb : b ∈ N
    · exact Or.inr hb
    · left
      apply mem_normalizer_iff_map_conj_eq.mpr
      change A.map (MulAut.conj (b * a)).toMonoidHom = A
      calc
        A.map (MulAut.conj (b * a)).toMonoidHom =
            (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom :=
          (A.conjBy_conjBy a b).symm
        _ = A := by rw [(hswap a ha).1, (hswap b hb).2]
  let : N.Normal := normal_of_index_eq_two hi
  exact (pResidual_le_iff_isPGroup_quotient 2 N).mpr
    (IsPGroup.of_card (n := 1) (by simpa only [N.index_eq_card, pow_one] using hi))

private theorem map_conjNormal_subtype {D : Type*} [Group D]
    (J : Subgroup D) [J.Normal] (A : Subgroup J) (x : D) :
    (A.map (MulAut.conjNormal x).toMonoidHom).map J.subtype =
      (A.map J.subtype).map (MulAut.conj x).toMonoidHom := by
  rw [map_map, map_map]
  congr 1

/-- The two-residual of the actual ambient quotient fixes both literal factors. -/
theorem residual_normalizes_two_factors {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (J : Subgroup D) [J.Normal] (ρ : Representation (ZMod 2) J W)
    (d : ChapterB.SourceInduction.SourceTwoFactorCase ρ) (hcore : pCore 2 J = ⊥) :
    pResidual 2 D ≤ normalizer (d.first.map J.subtype : Set D) ∧
      pResidual 2 D ≤ normalizer (d.second.map J.subtype : Set D) := by
  have hp (x : D) := d.automorphism_permutation hcore (MulAut.conjNormal x)
  have hp' (x : D) :
      ((d.first.map J.subtype).map (MulAut.conj x).toMonoidHom = d.first.map J.subtype ∧
        (d.second.map J.subtype).map (MulAut.conj x).toMonoidHom = d.second.map J.subtype) ∨
      ((d.first.map J.subtype).map (MulAut.conj x).toMonoidHom = d.second.map J.subtype ∧
        (d.second.map J.subtype).map (MulAut.conj x).toMonoidHom = d.first.map J.subtype) := by
    rcases hp x with hh | hh
    · exact Or.inl ⟨(map_conjNormal_subtype J d.first x).symm.trans
        (congrArg (fun A : Subgroup J => A.map J.subtype) hh.1),
        (map_conjNormal_subtype J d.second x).symm.trans
        (congrArg (fun A : Subgroup J => A.map J.subtype) hh.2)⟩
    · exact Or.inr ⟨(map_conjNormal_subtype J d.first x).symm.trans
        (congrArg (fun A : Subgroup J => A.map J.subtype) hh.1),
        (map_conjNormal_subtype J d.second x).symm.trans
        (congrArg (fun A : Subgroup J => A.map J.subtype) hh.2)⟩
  exact ⟨residual_le_pair_normalizer _ _ hp',
    residual_le_pair_normalizer _ _ (fun x => (hp' x).imp And.symm And.symm)⟩

/-- Odd-order subgroups are contained in the two-residual. -/
theorem odd_le_residual {D : Type*} [Group D] [Finite D]
    (A : Subgroup D) (ho : Odd (Nat.card A)) : A ≤ pResidual 2 D := by
  apply le_pResidual_of_isPPerfect
  intro N hn htwo
  let := hn
  apply index_eq_one.mp
  change Nat.card (A ⧸ N) = 1
  apply htwo.card_eq_or_dvd.resolve_right
  intro hd
  exact (Nat.not_even_iff_odd.mpr ho)
    (even_iff_two_dvd.mpr (hd.trans N.card_quotient_dvd_card))

end CFSG.Quasithin.Chapter6.Source.ThompsonImage

namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V X : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- Source 6.1.5's `O²(X)` fixes both factors, on their actual quotient images. -/
theorem overgroup_thompson_residual_normalizes_two_factors
    (hX : X ∈ Chapter1.HOver G (T : Set G)) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
    letI := (h.overgroup_omega_orbit_reduced hX).normal
    letI := (h.overgroup_omega_orbit_reduced hX).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
    ∀ d : ChapterB.SourceInduction.SourceTwoFactorCase (ρ.comp J.subtype),
      (pResidual 2 X).map q ≤ normalizer (d.first.map J.subtype : Set (X ⧸ C)) ∧
      (pResidual 2 X).map q ≤ normalizer (d.second.map J.subtype : Set (X ⧸ C)) := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
  have hU := h.overgroup_omega_orbit_reduced hX
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
  let : J.Normal := ThompsonImage.normal U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  exact fun d =>
    let hn := ThompsonImage.residual_normalizes_two_factors J (ρ.comp J.subtype) d
      (h.overgroup_thompson_hypothesis hX).twoCore
    ⟨(map_pResidual_le 2 q).trans hn.1, (map_pResidual_le 2 q).trans hn.2⟩

/-- The original odd Hall actor, once included in `X`, fixes each factor. -/
theorem overgroup_thompson_odd_normalizes_two_factors
    (hX : X ∈ Chapter1.HOver G (T : Set G)) (A : Subgroup X) (ho : Odd (Nat.card A)) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
    letI := (h.overgroup_omega_orbit_reduced hX).normal
    letI := (h.overgroup_omega_orbit_reduced hX).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let J := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map q
    ∀ d : ChapterB.SourceInduction.SourceTwoFactorCase (ρ.comp J.subtype),
      A.map q ≤ normalizer (d.first.map J.subtype : Set (X ⧸ C)) ∧
      A.map q ≤ normalizer (d.second.map J.subtype : Set (X ⧸ C)) := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X).subgroupOf X
  have hU := h.overgroup_omega_orbit_reduced hX
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  exact fun d =>
    let hn := h.overgroup_thompson_residual_normalizes_two_factors hX d
    ⟨(map_mono (ThompsonImage.odd_le_residual A ho)).trans hn.1,
      (map_mono (ThompsonImage.odd_le_residual A ho)).trans hn.2⟩

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
