module

public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Intersections of local conjugates controlled by a maximal two-local

Let M be maximal two-local, let Q be a two-subgroup normalized by K, and
suppose Q contains a nontrivial M-invariant subgroup V. The intersection R
of the M-conjugates of Q contains V, is a two-group, and is normalized by M.
Maximality gives N(R) = M. Every element in all M-conjugates of K normalizes
each conjugate of Q, and hence belongs to M.

This is used for Q = O₂(Mc) in the chosen-module hyperplane argument of
Aschbacher--Smith 15.2.26, printed p.1118, after 15.2.27(2) is established.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

private theorem map_conj_map (Q : Subgroup G) (a b : G) :
    (Q.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      Q.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- A nontrivial invariant two-subgroup in Q makes the intersection of
the M-conjugates of its normalizing group K lie in the maximal two-local M. -/
theorem iInf_conjugates_le_of_invariant_two_subgroup
    (M K Q V : Subgroup G) (hM : IsMaximalTwoLocal M)
    (hQ : IsPGroup 2 Q) (hKQ : K ≤ normalizer (Q : Set G))
    (hVQ : V ≤ Q) (hne : V ≠ ⊥) (hMV : M ≤ normalizer (V : Set G)) :
    (⨅ m : M, K.map (MulAut.conj (m : G)).toMonoidHom) ≤ M := by
  let R : Subgroup G := ⨅ m : M, Q.map (MulAut.conj (m : G)).toMonoidHom
  have hRQ : R ≤ Q := by
    have hi := iInf_le (fun m : M => Q.map (MulAut.conj (m : G)).toMonoidHom) 1
    have hone : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    change R ≤ Q.map (MulAut.conj (1 : G)).toMonoidHom at hi
    simpa only [hone, map_id] using hi
  have hVR : V ≤ R := by
    apply le_iInf
    intro m
    have hi := map_mono (f := (MulAut.conj (m : G)).toMonoidHom) hVQ
    have hv : V.map (MulAut.conj (m : G)).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (hMV m.property)
    rwa [hv] at hi
  have hRn : R ≠ ⊥ := fun he => hne (bot_unique (hVR.trans he.le))
  have hMR : M ≤ normalizer (R : Set G) := by
    intro m hm
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⨅ n : M, Q.map (MulAut.conj (n : G)).toMonoidHom).map
      (MulAut.conj m).toMonoidHom = _
    rw [map_iInf _ (MulAut.conj m).injective]
    simp_rw [map_conj_map]
    apply le_antisymm
    · apply le_iInf
      intro n
      have hi := iInf_le
        (fun k : M => Q.map (MulAut.conj (m * (k : G))).toMonoidHom)
        ((⟨m, hm⟩ : M)⁻¹ * n)
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using hi
    · apply le_iInf
      intro n
      exact iInf_le (fun k : M => Q.map (MulAut.conj (k : G)).toMonoidHom)
        ((⟨m, hm⟩ : M) * n)
  have hNM : normalizer (R : Set G) ≤ M :=
    hM.2 ⟨R, hRn, hQ.to_le hRQ, rfl⟩ hMR
  apply le_trans _ hNM
  apply le_trans _ (iInf_normalizer_le_normalizer_iInf
    (fun m : M => Q.map (MulAut.conj (m : G)).toMonoidHom))
  apply le_iInf
  intro m
  have hi := map_mono (f := (MulAut.conj (m : G)).toMonoidHom) hKQ
  rw [map_equiv_normalizer_eq] at hi
  exact (iInf_le _ m).trans hi

end Subgroup
