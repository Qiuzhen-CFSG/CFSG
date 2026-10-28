module
public import Theory.SpecificGroups.Rudvalis.Model.PointQuaternion.SquareCertificate
import all Theory.SpecificGroups.Rudvalis.Model.PointQuaternion.SquareCertificate
import all Theory.SpecificGroups.Rudvalis.Model.PointQuaternion.Embedding
import all Theory.SpecificGroups.Rudvalis.Model.PointCoreBound

/-!
# The quaternion centralizes the Rudvalis point-core commutator

The actual five-block quotient puts the full point two-core inside the
certified Sylow. The square certificate then proves that the native
quaternion centralizes every square in that core. The identity
`[x,y] = x² (x⁻¹y)² (y²)⁻¹` gives centralization of its derived subgroup.
This is the subgroup containing the original marked three-space in the
Chapter13 consumer; no assertion about all core involutions is used.

The import-all edges reuse the private native coordinates and decoder while
keeping the public result intrinsic. Source: Aschbacher--Smith J.2.2--3 and
4.2.13, printed pp.432--433,611--612. ATLAS conventions remain in Embedding.
-/

namespace Rudvalis.PointQuaternion
open scoped commutatorElement
open Subgroup SylowOvergroups PointCoreBound
open SylowOvergroups.RadicalCoverage.SylowCertificate
open SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder
open SylowOvergroups.RadicalCoverage.LocalCover
open SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate
set_option maxRecDepth 30000
set_option Elab.async false

private theorem square_check : ∀ n : Fin 16384, squareCommutes n := by
  have hc (k : Fin 16) : ∀ n : Fin 1024,
      squareCommutes ⟨1024 * k.val + n.val,by omega⟩ := by
    fin_cases k
    · exact square_check_0
    · exact square_check_1
    · exact square_check_2
    · exact square_check_3
    · exact square_check_4
    · exact square_check_5
    · exact square_check_6
    · exact square_check_7
    · exact square_check_8
    · exact square_check_9
    · exact square_check_10
    · exact square_check_11
    · exact square_check_12
    · exact square_check_13
    · exact square_check_14
    · exact square_check_15
  intro n
  have h := hc ⟨n.val / 1024,by omega⟩ ⟨n.val % 1024,by omega⟩
  have he : (⟨1024 * (n.val / 1024) + n.val % 1024,by omega⟩ : Fin 16384) = n := by
    apply Fin.ext
    change 1024 * (n.val / 1024) + n.val % 1024 = n.val
    omega
  exact he ▸ h

private theorem core_le_candidate :
    (centralizer ({elementaryGenerator 0} : Set Model)).pCoreIn 2 ≤ candidate := by
  have hi : ¬ 2 ∣ candidate.index := by
    intro hi
    apply not_two_pow_fifteen_dvd_card_model
    rw [←candidate.card_mul_index,candidate_card]
    exact Nat.mul_dvd_mul_left 16384 hi
  let S : Sylow 2 Model := candidate_isTwoGroup.toSylow hi
  have hh := pCoreIn_le_sylow _ (S.subtype candidate_le_point_centralizer)
  change (centralizer ({elementaryGenerator 0} : Set Model)).pCoreIn 2 ≤
    (candidate.subgroupOf (centralizer ({elementaryGenerator 0} : Set Model))).map
      (centralizer ({elementaryGenerator 0} : Set Model)).subtype at hh
  rwa [map_subgroupOf_eq_of_le candidate_le_point_centralizer] at hh

private theorem embedding_commutes_square (a : QuaternionGroup 2) (x : Model)
    (hx : x ∈ (centralizer ({elementaryGenerator 0} : Set Model)).pCoreIn 2) :
    Commute (embedding a) (x^2) := by
  obtain ⟨n,rfl⟩ := exists_candidateNormalForm (core_le_candidate hx)
  have h1 : normalMap n 460 ∈ blockOne := by
    rw [blockOne_eq,←normal_smul]
    exact core_preserves_blocks _ hx 1 460 (by decide +kernel)
  have h3 : normalMap n 128 ∈ blockThree := by
    rw [blockThree_eq,←normal_smul]
    exact core_preserves_blocks _ hx 3 128 (by decide +kernel)
  obtain ⟨ha,hb⟩ := square_check n h1 h3
  have hgen (u : QuaternionGroup 2)
      (h : normalMap (index u) (normalMap n (normalMap n 0)) =
          normalMap n (normalMap n (normalMap (index u) 0)) ∧
        normalMap (index u) (normalMap n (normalMap n 1)) =
          normalMap n (normalMap n (normalMap (index u) 1))) :
      Commute (embedding u) (candidateNormalForm n ^ 2) := by
    apply candidate_ext _ _
      (candidate.mul_mem (candidateNormalForm_mem _) (candidate.pow_mem (candidateNormalForm_mem _) 2))
      (candidate.mul_mem (candidate.pow_mem (candidateNormalForm_mem _) 2) (candidateNormalForm_mem _))
    · simpa only [pow_two,mul_smul,embedding_smul,normal_smul] using h.1
    · simpa only [pow_two,mul_smul,embedding_smul,normal_smul] using h.2
  have ha' := hgen (.a 1) ha
  have hb' := hgen (.xa 0) hb
  have hforms : ∀ u : QuaternionGroup 2, ∃ k : Fin 4,
      u = (QuaternionGroup.a 1)^k.val ∨
        u = QuaternionGroup.xa 0 * (QuaternionGroup.a 1)^k.val := by decide +kernel
  obtain ⟨k,hk | hk⟩ := hforms a
  · rw [hk,map_pow]
    exact ha'.pow_left _
  · rw [hk,map_mul,map_pow]
    exact hb'.mul_left (ha'.pow_left _)

/-- The native quaternion centralizes the derived subgroup of the actual
point two-core. The assertion concerns that subgroup, not all core involutions. -/
public theorem embedding_centralizes_core_commutator (a : QuaternionGroup 2) :
    embedding a ∈ centralizer
      ((⁅(centralizer ({elementaryGenerator 0} : Set Model)).pCoreIn 2,
        (centralizer ({elementaryGenerator 0} : Set Model)).pCoreIn 2⁆ : Subgroup Model) : Set Model) := by
  let R := (centralizer ({elementaryGenerator 0} : Set Model)).pCoreIn 2
  let C := centralizer ({embedding a} : Set Model)
  have hs (x : Model) (hx : x ∈ R) : x^2 ∈ C :=
    mem_centralizer_singleton_iff.mpr (embedding_commutes_square a x hx).symm.eq
  have hd : ⁅R,R⁆ ≤ C := by
    apply commutator_le.mpr
    intro x hx y hy
    have hid : ⁅x,y⁆ = x^2 * (x⁻¹*y)^2 * (y^2)⁻¹ := by
      simp [commutatorElement_def,pow_two,mul_assoc]
    rw [hid]
    exact C.mul_mem (C.mul_mem (hs x hx) (hs _ (R.mul_mem (R.inv_mem hx) hy)))
      (C.inv_mem (hs y hy))
  intro u hu
  exact mem_centralizer_singleton_iff.mp (hd hu)

end Rudvalis.PointQuaternion
