module

import Stellmacher.SectionOne.LemmaOneOne
import Stellmacher.SectionOne.LemmaOneTwo
import Theory.GroupAction.CommutatorSemidirect
import Theory.GroupAction.Quadratic
import Theory.ThreeSubgroups

open scoped BigOperators Pointwise commutatorElement

namespace Stellmacher.SectionOne

universe u v

example {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hquadratic : IsQuadraticAction S V) :
    let V₀ : Subgroup V :=
      ⨆ (S₀ : Subgroup S) (_ : Nat.card S = 2 * Nat.card S₀),
        FixedPoints.subgroup S₀ V
    ∀ (H : Subgroup S), Nat.card S = 2 * Nat.card H →
      let H' : Subgroup G := H.map (S : Subgroup G).subtype
      let N : Subgroup G := oddCore G ⊓ Subgroup.centralizer (H' : Set G)
      ⁅N, (S : Subgroup G)⁆ ≤ MulAction.stabilizer G (V₀ : Set V) := by
  let V₀ : Subgroup V :=
    ⨆ (S₀ : Subgroup S) (_ : Nat.card S = 2 * Nat.card S₀),
      FixedPoints.subgroup S₀ V
  intro H hHcard
  let H' : Subgroup G := H.map (S : Subgroup G).subtype
  let N : Subgroup G := oddCore G ⊓ Subgroup.centralizer (H' : Set G)
  letI : IsElementaryAbelian 2 S := (lemma_one_one h S).part_d hquadratic
  letI : CommGroup S := IsMulCommutative.instCommGroup
  letI : CommGroup V := IsMulCommutative.instCommGroup
  have hquadfix : commutatorAction S V ≤ FixedPoints.subgroup S V :=
    commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot hquadratic
  have hNfixed :
      commutatorSubgroup N V (FixedPoints.subgroup S V) ≤
        FixedPoints.subgroup H V := by
    rw [commutatorSubgroup]
    refine (Subgroup.closure_le (K := FixedPoints.subgroup H V)).2 ?_
    rintro x ⟨n, d, hd, rfl⟩
    rw [FixedPoints.mem_subgroup] at hd ⊢
    intro a
    have haH' : (a : G) ∈ H' := by
      exact Subgroup.mem_map.mpr ⟨(a : S), a.property, rfl⟩
    have han : (a : G) * (n : G) = (n : G) * (a : G) :=
      Subgroup.mem_centralizer_iff.mp n.property.2 (a : G) haH'
    have had : (a : H) • d = d := by
      simpa only [Subgroup.smul_def] using hd (a : S)
    have hand : (a : H) • (n • d) = n • d := by
      change (a : G) • ((n : G) • d) = (n : G) • d
      rw [← mul_smul, han, mul_smul]
      change (n : G) • ((a : H) • d) = (n : G) • d
      rw [had]
    simpa only [smul_mul', smul_inv', had, hand]
  let φ : G →* MulAut V := MulDistribMulAction.toMulAut G V
  let SD := V ⋊[φ] G
  letI : Group SD := by infer_instance
  let inl : V →* SD := SemidirectProduct.inl
  let inr : G →* SD := SemidirectProduct.inr
  let HV₀ : Subgroup SD := V₀.map inl
  let HH : Subgroup SD := (FixedPoints.subgroup H V).map inl
  let HN : Subgroup SD := N.map inr
  let HS : Subgroup SD := (S : Subgroup G).map inr
  have hnormN : HN ≤ Subgroup.normalizer HH := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    rw [Subgroup.commutator_comm]
    rw [← Theory.GroupAction.commutatorSubgroup_map_semidirect_inl_eq_commutator
      (B := N) (H := FixedPoints.subgroup H V)]
    apply Subgroup.map_mono
    rw [commutatorSubgroup]
    refine (Subgroup.closure_le (K := FixedPoints.subgroup H V)).2 ?_
    rintro x ⟨n, d, hd, rfl⟩
    rw [FixedPoints.mem_subgroup] at hd ⊢
    intro a
    have haH' : (a : G) ∈ H' :=
      Subgroup.mem_map.mpr ⟨(a : S), a.property, rfl⟩
    have han : (a : G) * (n : G) = (n : G) * (a : G) :=
      Subgroup.mem_centralizer_iff.mp n.property.2 (a : G) haH'
    have hand : (a : H) • (n • d) = n • d := by
      change (a : G) • ((n : G) • d) = (n : G) • d
      rw [← mul_smul, han, mul_smul]
      change (n : G) • ((a : H) • d) = (n : G) • d
      rw [hd a]
    simpa only [smul_mul', smul_inv', hd a, hand]
  have hnormS : HS ≤ Subgroup.normalizer HH := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    rw [Subgroup.commutator_comm]
    rw [← Theory.GroupAction.commutatorSubgroup_map_semidirect_inl_eq_commutator
      (B := (S : Subgroup G)) (H := FixedPoints.subgroup H V)]
    apply Subgroup.map_mono
    rw [commutatorSubgroup]
    refine (Subgroup.closure_le (K := FixedPoints.subgroup H V)).2 ?_
    rintro x ⟨s, d, hd, rfl⟩
    rw [FixedPoints.mem_subgroup] at hd ⊢
    intro a
    have hcomm : (a : S) * s = s * (a : S) := mul_comm _ _
    have hsd : (a : H) • (s • d) = s • d := by
      change (a : S) • (s • d) = s • d
      rw [← mul_smul, hcomm, mul_smul]
      change s • ((a : H) • d) = s • d
      rw [hd a]
    simpa only [smul_mul', smul_inv', hd a, hsd]
  have hnormV : HV₀ ≤ Subgroup.normalizer HH := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    rw [Subgroup.commutator_le]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hxy : Commute (inl x) (inl y) := by
      rw [SemidirectProduct.inl_apply, SemidirectProduct.inl_apply]
      exact SemidirectProduct.inl_commute_iff.mpr (Commute.all x y)
    rw [hxy.commutator_eq]
    exact HH.one_mem
  have hrot₁ : ⁅⁅HS, HV₀⁆, HN⁆ ≤ HH := by
    rw [Subgroup.commutator_comm HS HV₀]
    have hinner : ⁅HV₀, HS⁆ ≤ (commutatorAction S V).map inl := by
      rw [← Theory.GroupAction.commutatorSubgroup_map_semidirect_inl_eq_commutator
        (B := (S : Subgroup G)) (H := V₀)]
      apply Subgroup.map_mono
      exact Theory.GroupAction.commutatorSubgroup_mono le_top
    refine (Subgroup.commutator_mono hinner le_rfl).trans ?_
    rw [← Theory.GroupAction.commutatorSubgroup_map_semidirect_inl_eq_commutator
      (B := N) (H := commutatorAction S V)]
    apply Subgroup.map_mono
    exact (Theory.GroupAction.commutatorSubgroup_mono hquadfix).trans hNfixed
  have hrot₂ : ⁅⁅HV₀, HN⁆, HS⁆ ≤ HH := by
    have hinner : ⁅HV₀, HN⁆ ≤ (⊤ : Subgroup V).map inl := by
      rw [← Theory.GroupAction.commutatorSubgroup_map_semidirect_inl_eq_commutator
        (B := N) (H := V₀)]
      exact Subgroup.map_mono le_top
    refine (Subgroup.commutator_mono hinner le_rfl).trans ?_
    rw [← Theory.GroupAction.commutatorSubgroup_map_semidirect_inl_eq_commutator
      (B := (S : Subgroup G)) (H := (⊤ : Subgroup V))]
    apply Subgroup.map_mono
    exact hquadfix.trans (fixedPoints_subgroup_antitone S V H.le)
  have hthree : ⁅⁅HN, HS⁆, HV₀⁆ ≤ HH :=
    Subgroup.commutator_commutator_le_of_rotate_of_le_normalizer
      hnormN hnormS hnormV hrot₁ hrot₂
  sorry

end Stellmacher.SectionOne
