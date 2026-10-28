module

public import Theory.SpecificGroups.BinaryLinear.CubicPairNormalizers.CoreAbsorption.Elementary
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Pairs

/-!
# Two-core absorption for nonadjacent binary five-space flags

The exact diagonal kernel is the two-core. Its matrices are unitriangular,
and the entries within each diagonal block are those of the identity.
Decreasing-row factorization expresses every such matrix as a product of
cross-block shears. In the block patterns 2+2+1, 2+1+2 and 1+2+2 every such
shear meets a two-dimensional block, so the cubic commutator identities
place it in O². The flag coordinate equivalence transports this intrinsic
containment to every supplied basis, retaining both orders of the nodes.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.25, printed p.960 (PDF p.977), the nonadjacent rank-two parabolic.
-/

public section

open Subgroup
namespace BinaryLinear.CubicPairNormalizers.CoreAbsorption
open OuterCyclic SmallParabolicLevi.TwoNodes FiveFlagGeometry FiveFlagGeometry.SylowOvergroups

private theorem entries_eq_matrix (g : LinearGroup 5) : entries g = matrix g := by
  ext r s
  rw [matrix_apply]
  simp [entries, standardBasis, Pi.basisFun_apply]

private theorem root_mem_triangular (c : Fin 5 → Fin 5) (r s : Fin 5)
    (hrs : r ≠ s) (hc : c r ≤ c s) : root r s hrs 1 ∈ triangularGroup c := by
  intro i j hij
  rw [matrix_apply]
  simp only [root_apply, standardBasis, Pi.basisFun_apply, Pi.single_apply, mul_one]
  have hji : j ≠ i := by intro he; subst j; exact (lt_irrefl _ hij)
  by_cases hir : i = r
  · subst i
    have hsj : s ≠ j := by
      intro he
      subst j
      exact (not_lt_of_ge hc) hij
    simp [hji.symm, hsj]
  · simp [hji.symm, hir]

/-- The diagonal kernel is absorbed whenever every cross-block pair has a partner. -/
theorem triangular_five_core_le_residual (c : Fin 5 → Fin 5) (hc : Monotone c)
    (hp : ∀ r s, c r < c s →
      (∃ k, k ≠ r ∧ c k = c r) ∨ (∃ k, k ≠ s ∧ c k = c s)) :
    pCore 2 (triangularGroup c) ≤ pResidual 2 (triangularGroup c) := by
  intro g hg
  have hgk : g ∈ (diagonalAction c).ker := by
    rwa [ker_diagonalAction_eq_twoCore c hc]
  have hgB : g.val ∈ standardBorel :=
    ker_le_standardBorel c hc (mem_map.mpr ⟨g, hgk, rfl⟩)
  have he (r s : Fin 5) (hrs : c r = c s) :
      entries g.val r s = if r = s then 1 else 0 := by
    have h := congrFun (congrFun (blockMatrix_eq_one_of_mem_ker c g hgk (c r))
      ⟨r, rfl⟩) ⟨s, hrs.symm⟩
    simpa [blockMatrix, Matrix.one_apply, Subtype.ext_iff, ← entries_eq_matrix] using h
  have hgR : g.val ∈ (pResidual 2 (triangularGroup c)).map (triangularGroup c).subtype := by
    apply upper_five_mem
    · intro r s hsr
      rw [entries_eq_matrix]
      exact (mem_standardBorel_iff _).mp hgB hsr
    · intro r
      rw [entries_eq_matrix]
      exact standardBorel_diagonal hgB r
    · intro r s hrs
      by_cases heq : c r = c s
      · rw [he r s heq, if_neg (ne_of_lt hrs), root_zero]
        exact one_mem _
      · have hlt : c r < c s := lt_of_le_of_ne (hc hrs.le) heq
        have hnz : entries g.val r s = 0 ∨ entries g.val r s = 1 :=
          (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) _
        rcases hnz with hz | ho
        · rw [hz, root_zero]; exact one_mem _
        · rw [ho]
          exact root_mem_residual (fun k => (c k).val) (triangularGroup c)
            (fun i j hij hijc => root_mem_triangular c i j hij hijc) r s (ne_of_lt hrs) hlt
            (by simpa only [Fin.val_inj] using hp r s hlt)
  obtain ⟨x, hx, hxe⟩ := mem_map.mp hgR
  have : x = g := Subtype.ext hxe
  exact this ▸ hx

private theorem pair_partners (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    ∀ r s, pairLabel i j r < pairLabel i j s →
      (∃ k, k ≠ r ∧ pairLabel i j k = pairLabel i j r) ∨
      (∃ k, k ≠ s ∧ pairLabel i j k = pairLabel i j s) := by
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  have h02 : pairLabel 0 2 = ![0,0,1,1,2] := by
    funext t; fin_cases t <;>
      simp [pairLabel, cutLabel, hu, Finset.filter_insert, Finset.filter_singleton]
  have h03 : pairLabel 0 3 = ![0,0,1,2,2] := by
    funext t; fin_cases t <;>
      simp [pairLabel, cutLabel, hu, Finset.filter_insert, Finset.filter_singleton]
  have h13 : pairLabel 1 3 = ![0,1,1,2,2] := by
    funext t; fin_cases t <;>
      simp [pairLabel, cutLabel, hu, Finset.filter_insert, Finset.filter_singleton]
  have h20 : pairLabel 2 0 = pairLabel 0 2 := pairLabel_comm 0 2
  have h30 : pairLabel 3 0 = pairLabel 0 3 := pairLabel_comm 0 3
  have h31 : pairLabel 3 1 = pairLabel 1 3 := pairLabel_comm 1 3
  have cases : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) ∨
      (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 0) ∨ (i = 3 ∧ j = 1) := by
    revert i j
    decide +kernel
  rcases cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [h02]; decide
  · rw [h03]; decide
  · rw [h13]; decide
  · rw [h20, h02]; decide
  · rw [h30, h03]; decide
  · rw [h31, h13]; decide

/-- The actual two-core of every nonadjacent binary five-space flag lies in its O². -/
theorem five_flag_core_le_residual (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    pCore 2 (flagStabilizer b ({i,j} : Set (Fin 4))ᶜ) ≤
      pResidual 2 (flagStabilizer b ({i,j} : Set (Fin 4))ᶜ) := by
  let e := flagCoordinates b ({i,j} : Set (Fin 4))ᶜ
  have ht := triangular_five_core_le_residual (pairLabel i j)
    (cutLabel_monotone _) (pair_partners i j h)
  simp only [pairLabel] at ht
  calc
    pCore 2 (flagStabilizer b ({i,j} : Set (Fin 4))ᶜ) =
        (pCore 2 (triangularGroup (cutLabel ({i,j} : Set (Fin 4))ᶜ))).map
          e.symm.toMonoidHom := (pCore_map_iso 2 e.symm).symm
    _ ≤ (pResidual 2 (triangularGroup (cutLabel ({i,j} : Set (Fin 4))ᶜ))).map
          e.symm.toMonoidHom := Subgroup.map_mono ht
    _ = pResidual 2 (flagStabilizer b ({i,j} : Set (Fin 4))ᶜ) := map_pResidual 2 e.symm


end BinaryLinear.CubicPairNormalizers.CoreAbsorption

end
