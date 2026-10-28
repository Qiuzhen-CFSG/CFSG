module
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalLevi
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Mixed point-parabolic sections in binary dimension five

A full-Sylow overgroup with a two-kernel quotient of order 1344 has Sylow
index 21, order 21504 and kernel order 16. The diagonal quotients of the
sixteen basis flags then identify its three possible flags: cuts {0,1},
{0,3}, or {2,3}. The middle alternative is the transvection-centralizer
flag; the adjacent-end alternatives remain distinct.

The original source application in NaturalSource/LocalControl/MixedBinary
constructs this section on the literal image of L₁T, with kernel the image
of O₂(LT). No transvection marking or normalizer comparison is assumed.
Source: Aschbacher--Smith,12.9.5(3) and12.9.6, printed pp.860--862.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear.FivePointSection
open FiveFlagGeometry
open OuterCyclic SmallParabolicLevi SmallParabolicLevi.TwoNodes
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private def linearOrder (n : ℕ) : ℕ := ∏ j : Fin n, (2^n - 2^j.val)

private theorem coordinate_card {α : Type*} [Fintype α] :
    Nat.card (BinaryLinear.GL (α → ZMod 2)) =
      linearOrder (Nat.card α) := by
  rw [Nat.card_eq_fintype_card (α := α)]
  let e : (α → ZMod 2) ≃ₗ[ZMod 2] Space (Fintype.card α) :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (Fintype.equivFin α).symm
  rw [Nat.card_congr (linearGroupCongr e).toEquiv,
    ← Nat.card_congr (matrixEquivLinear _).toEquiv, Matrix.card_GL_field]
  simp [linearOrder]

private def blockCount (s : Finset (Fin 4)) (k : Fin 5) : ℕ :=
  (Finset.univ.filter fun i : Fin 5 => (s.filter fun j => j.val < i.val).card = k.val).card

private theorem blockCount_eq (s : Finset (Fin 4)) (k : Fin 5) :
    blockCount s k = Nat.card (Block (cutLabel (s : Set (Fin 4))) k) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold blockCount cutLabel
  congr 1
  apply Finset.filter_congr
  intro i _
  simp only [Fin.ext_iff]
  have he : s.filter (fun j => j.val < i.val) =
      Finset.univ.filter (fun j : Fin 4 => j ∈ (s : Set (Fin 4)) ∧ j.val < i.val) := by
    ext j
    simp
  rw [he]
  apply Iff.of_eq
  congr 3

private def leviOrder (s : Finset (Fin 4)) : ℕ :=
  ∏ k : Fin 5, linearOrder (blockCount s k)

open scoped Classical in
private theorem quotient_card (b : FiveBasis) (cuts : Set (Fin 4)) :
    Nat.card (flagStabilizer b cuts ⧸ pCore 2 (flagStabilizer b cuts)) =
      leviOrder cuts.toFinset := by
  classical
  rw [Nat.card_congr (flagDiagonalQuotientEquiv b cuts).toEquiv, Nat.card_pi]
  simp_rw [coordinate_card]
  simp_rw [leviOrder, blockCount_eq, Set.coe_toFinset]

private theorem cut_certificate : ∀ s : Finset (Fin 4),
    leviOrder s = 21 * 2 ^ (leviOrder s).factorization 2 → s = {0,1} ∨ s = {0,3} ∨ s = {2,3} := by
  decide +kernel

/-- Sylow index 21 recognizes exactly the three flags with a three-dimensional Levi block. -/
theorem flag_of_sylow_index (S : Sylow 2 (LinearGroup 5))
    (H : Subgroup (LinearGroup 5)) (hSH : (S : Subgroup _) ≤ H)
    (hi : (S : Subgroup _).relIndex H = 21) :
    ∃ b : FiveBasis, H = flagStabilizer b {0,1} ∨ H = flagStabilizer b {0,3} ∨ H = flagStabilizer b {2,3} := by
  classical
  obtain ⟨b,cuts,rfl⟩ := isFlagParabolic_of_sylow_le S H hSH
  let P := flagStabilizer b cuts
  let R := S.subtype hSH
  let q := QuotientGroup.mk' (pCore 2 P)
  let U := R.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 P))
  have hui : U.index = 21 := by
    change ((R : Subgroup P).map q).index = _
    rw [index_map_eq _ (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal R)]
    exact hi
  have hc := (U : Subgroup (P ⧸ pCore 2 P)).index_mul_card
  rw [U.card_eq_multiplicity, hui] at hc
  change 21 * 2 ^ (Nat.card (P ⧸ pCore 2 P)).factorization 2 = Nat.card (P ⧸ pCore 2 P) at hc
  rw [quotient_card] at hc
  rcases cut_certificate cuts.toFinset hc.symm with he | he | he
  · refine ⟨b, Or.inl ?_⟩
    apply congrArg (flagStabilizer b)
    simpa only [Set.coe_toFinset, Finset.coe_insert, Finset.coe_singleton] using congrArg (fun t : Finset (Fin 4) => (t : Set (Fin 4))) he
  · refine ⟨b, Or.inr (Or.inl ?_)⟩
    apply congrArg (flagStabilizer b)
    simpa only [Set.coe_toFinset, Finset.coe_insert, Finset.coe_singleton] using congrArg (fun t : Finset (Fin 4) => (t : Set (Fin 4))) he

  · refine ⟨b, Or.inr (Or.inr ?_)⟩
    apply congrArg (flagStabilizer b)
    simpa only [Set.coe_toFinset, Finset.coe_insert, Finset.coe_singleton] using congrArg (fun t : Finset (Fin 4) => (t : Set (Fin 4))) he


/-- A two-kernel map onto a group of order 1344 has Sylow index 21,
and its kernel has order sixteen. -/
theorem section_orders (S : Sylow 2 (LinearGroup 5))
    (J : Subgroup (LinearGroup 5)) (hSJ : (S : Subgroup _) ≤ J)
    {P : Type*} [Group P] (f : J →* P) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hc : Nat.card P = 1344) :
    (S : Subgroup _).relIndex J = 21 ∧ Nat.card J = 21504 ∧ Nat.card f.ker = 16 := by
  let : Finite P := Finite.of_surjective f hf
  let U := S.subtype hSJ
  let R := U.mapSurjective hf
  have hR : Nat.card (R : Subgroup P) = 64 := by
    rw [R.card_eq_multiplicity,hc]
    decide +kernel
  have hRi : R.index = 21 := by
    have h := (R : Subgroup P).index_mul_card
    rw [hR,hc] at h
    omega
  have hi : (S : Subgroup _).relIndex J = 21 := by
    have hh : R.index = U.index := index_map_eq _ hf (hk.le_sylow_of_normal U)
    exact hh.symm.trans hRi
  have hS : Nat.card (S : Subgroup (LinearGroup 5)) = 1024 := by
    rw [S.card_eq_multiplicity]
    have hcard : Nat.card (LinearGroup 5) = 9999360 := by
      rw [← Nat.card_congr (matrixEquivLinear 5).toEquiv,Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ]
    rw [hcard]
    decide +kernel
  have hU : Nat.card (U : Subgroup J) = 1024 :=
    (Nat.card_congr (subgroupOfEquivOfLe hSJ).toEquiv).trans hS
  have hJ : Nat.card J = 21504 := by
    have h := (U : Subgroup J).index_mul_card
    rw [show U.index = 21 from hi,hU] at h
    omega
  refine ⟨hi,hJ,?_⟩
  have h := f.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top,hc,hJ] at h
  omega

/-- The actual image is one of the three flags with a three-dimensional Levi block.
The two adjacent-end flags are retained separately from the transvection flag. -/
theorem section_geometry (S : Sylow 2 (LinearGroup 5))
    (J : Subgroup (LinearGroup 5)) (hSJ : (S : Subgroup _) ≤ J)
    {P : Type*} [Group P] (f : J →* P) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hc : Nat.card P = 1344) :
    Nat.card J = 21504 ∧ Nat.card f.ker = 16 ∧
      ∃ b : FiveBasis, J = flagStabilizer b {0,1} ∨
        J = flagStabilizer b {0,3} ∨ J = flagStabilizer b {2,3} := by
  obtain ⟨hi,hJ,hk⟩ := section_orders S J hSJ f hf hk hc
  exact ⟨hJ,hk,flag_of_sylow_index S J hSJ hi⟩

end BinaryLinear.FivePointSection
