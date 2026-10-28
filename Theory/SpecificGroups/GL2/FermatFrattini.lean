module
public import Theory.SpecificGroups.GL2.DiagonalSwap
public import Theory.SpecificGroups.GL2.SemidihedralSylow
public import Theory.GroupTheory.SylowFrattiniBounds
public import Mathlib.GroupTheory.Schreier

/-!
# Two Frattini generators for GL₂ over Fermat fields

When the field has order 2^(2^k)+1, the actual Sylow two-subgroups of GL₂
need two generators. At k=0 the established semidihedral matrices supply
them. Otherwise the diagonal-and-swap subgroup has odd index, and one
diagonal generator together with the swap generates it.

Its Frattini quotient therefore has at most four elements. The immediate
consumer is the determinant-one two-block subgroup of SL₄, excluding the
Fermat linear-four outer section in Aschbacher--Smith 4.4.10--11 and 12.1.9,
printed pp.621 and 793. Matrix generators reuse the existing ABG II.2
construction recorded in `GL2.SemidihedralSylow` and `GL2.DiagonalSwap`.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative MatrixGroups
namespace Matrix.GeneralLinearGroup.FermatFrattini

private theorem pair_frattini_le_four {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (a b : P) (hg : closure ({a,b} : Set P) = ⊤) :
    Nat.card (P ⧸ frattini P) ≤ 4 := by
  classical
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  have hr : Group.rank P ≤ 2 := (Group.rank_le (S := {a,b}) (by simpa using hg)).trans
    (Finset.card_insert_le _ _ |>.trans (by simp))
  have hq := (Group.rank_le_of_surjective (QuotientGroup.mk' (frattini P))
    (QuotientGroup.mk'_surjective _)).trans hr
  have hd := card_dvd_exponent_pow_rank' (P ⧸ frattini P)
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (P ⧸ frattini P)))
  exact (Nat.le_of_dvd (by positivity) hd).trans
    (show 2 ^ Group.rank (P ⧸ frattini P) ≤ 4 by
      exact Nat.pow_le_pow_right (by decide) hq)

private theorem split_frattini_le_four {F : Type*} [Field F] [Finite F]
    (k : ℕ) (hk : 2 ≤ k) (hF : Nat.card F = 2 ^ k + 1)
    (P : Sylow 2 (GL (Fin 2) F)) : Nat.card (P ⧸ frattini P) ≤ 4 := by
  obtain ⟨z,hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  rw [Nat.card_units,hF,Nat.add_sub_cancel] at hz
  let H := diagonalSwapSubgroup F z
  have hp2 : 2 ^ (2*k+1) = 2*(2^k)^2 := by
    rw [show 2*k+1=k*2+1 by omega, pow_add, pow_mul, pow_one]
    ring
  have hc : Nat.card H = 2 ^ (2*k+1) := by
    rw [diagonalSwapSubgroup_card,hz,hp2]
  have htwo : IsPGroup 2 H := IsPGroup.of_card hc
  have hind : Odd H.index := by
    have hG : Nat.card (GL (Fin 2) F) = (2 ^ k + 1) * (2 ^ k)^2 * (2 ^ k + 2) := by
      let := Fintype.ofFinite F
      rw [Matrix.card_GL_field]
      simp only [Fin.prod_univ_two,Fin.val_zero,Fin.val_one,pow_zero,pow_one,
        ←Nat.card_eq_fintype_card,hF]
      have h₁ : (2^k+1)^2-1 = 2^k*(2^k+2) := by
        have : (2^k+1)^2=2^k*(2^k+2)+1 := by ring
        omega
      have h₂ : (2^k+1)^2-(2^k+1) = 2^k*(2^k+1) := by
        have : (2^k+1)^2=2^k*(2^k+1)+(2^k+1) := by ring
        omega
      rw [h₁,h₂]
      ring
    have he := H.card_mul_index
    rw [hc,hG] at he
    have hp : 2^k=2*(2^(k-1)) := by
      rw [←pow_succ', Nat.sub_add_cancel (by omega)]
    have hi : H.index = (2^k+1)*(2^(k-1)+1) := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 2^(2*k+1) by positivity)
      rw [he,hp2,hp]
      ring
    have heven (j : ℕ) (hj : 1 ≤ j) : Even (2^j) :=
      even_two.pow_of_ne_zero (by omega)
    rw [hi]
    exact (heven k (by omega)).add_one.mul ((heven (k-1) (by omega)).add_one)
  let S : Sylow 2 (GL (Fin 2) F) := htwo.toSylow hind.not_two_dvd_nat
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (P.equiv S)]
  let a : H := ⟨diagonalPair F (z,1),subset_closure (by simp)⟩
  let b : H := ⟨coordinateSwap F,subset_closure (by simp)⟩
  apply pair_frattini_le_four htwo a b
  apply Subgroup.map_injective H.subtype_injective
  rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,H.range_subtype,
    Set.image_insert_eq,Set.image_singleton]
  change closure {diagonalPair F (z,1),coordinateSwap F} = diagonalSwapSubgroup F z
  apply le_antisymm
  · exact closure_mono (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at *; tauto)
  · apply (closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact subset_closure (by simp)
    · rw [←coordinateSwap_conj_diagonalPair F z 1]
      exact mul_mem (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
        (inv_mem (subset_closure (by simp)))
    · exact subset_closure (by simp)

/-- A Fermat field has a two-generator Sylow subgroup in its actual GL₂. -/
theorem sylow_frattini_le_four {F : Type*} [Field F] [Finite F]
    (hF : ∃ k : ℕ, Nat.card F = 2 ^ (2 ^ k) + 1)
    (P : Sylow 2 (GL (Fin 2) F)) : Nat.card (P ⧸ frattini P) ≤ 4 := by
  obtain ⟨k,hk⟩ := hF
  by_cases hzero : k = 0
  · have hthree : Nat.card F % 4 = 3 := by simp [hk,hzero]
    obtain ⟨S,n,_,_,a,b,_,_,_,hg,_,_⟩ := exists_semidihedral_sylow F hthree
    rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (P.equiv S)]
    exact pair_frattini_le_four S.isPGroup' a b hg
  · exact split_frattini_le_four (2^k)
      (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ k)) hk P
end Matrix.GeneralLinearGroup.FermatFrattini
