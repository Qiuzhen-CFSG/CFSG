module

public import Theory.Order.UniqueMaximalOver
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.Commutator.NormalizesSupplement
public import Theory.PGroupCore

/-!
# The residual commutator in a unique-maximal Sylow overgroup

Suppose a Sylow two-subgroup T lies in a unique maximal subgroup M.
Frattini's argument shows that every normal subgroup N contained in M
has T ∩ N ≤ O₂(G): otherwise its Sylow normalizer would be a proper
overgroup of T outside M.

For J normal in T and outside O₂(G), put D = [O²(G),J]. Both D and JD
are normal in G. The preceding observation forces JD outside M, so
DT = G. The residual's defining minimality then gives D = O²(G).
No solvability, characteristic-two, or classification hypothesis is needed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
B.6.8(5),(6d), printed pp.114–115; used in C.5.3, printed p.154.
-/

public section
namespace Subgroup

/-- A normal subgroup inside the unique maximal overgroup has all its
Sylow two-elements in the ambient two-core. -/
theorem sylow_inf_normal_le_twoCore_of_uniqueMaximal {X : Type*} [Group X] [Finite X]
    (T : Sylow 2 X) (hu : Order.HasUniqueMaximalOver (T : Subgroup X) ⊤)
    (M N : Subgroup X) (hM : (T : Subgroup X) ≤ M ∧ IsCoatom M)
    [N.Normal] (hNM : N ≤ M) : (T : Subgroup X) ⊓ N ≤ pCore 2 X := by
  obtain ⟨P, hP⟩ := T.exists_subgroupOf_eq_of_normal N
  have hmap : (P : Subgroup N).map N.subtype = (T : Subgroup X) ⊓ N := by
    rw [hP, subgroupOf_map_subtype]
  have hTN : (T : Subgroup X) ≤ normalizer (((T : Subgroup X) ⊓ N : Subgroup X) : Set X) :=
    (le_inf (T : Subgroup X).le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have hfull : normalizer (((T : Subgroup X) ⊓ N : Subgroup X) : Set X) = ⊤ := by
    by_contra hne
    have hle := hu.le_maximal ⟨hM.1, hM.2.covBy_top⟩ hTN (lt_top_iff_ne_top.mpr hne)
    have hf := P.normalizer_sup_eq_top
    rw [hmap] at hf
    exact hM.2.ne_top (top_unique (hf ▸ sup_le hle hNM))
  let _ : ((T : Subgroup X) ⊓ N).Normal := normalizer_eq_top_iff.mp hfull
  exact le_sSup ⟨inferInstance, T.isPGroup'.to_le inf_le_left⟩

/-- A subgroup normal in the fixed Sylow subgroup and outside the two-core
generates the entire two-residual by commutators. -/
theorem commutator_twoResidual_eq_of_normal_sylow_subgroup
    {X : Type*} [Group X] [Finite X] (T : Sylow 2 X)
    (hu : Order.HasUniqueMaximalOver (T : Subgroup X) ⊤)
    (J : Subgroup X) (hJT : J ≤ T) (hTJ : (T : Subgroup X) ≤ normalizer (J : Set X))
    (hJ : ¬ J ≤ pCore 2 X) : ⁅pResidual 2 X, J⁆ = pResidual 2 X := by
  let D := ⁅pResidual 2 X, J⁆
  have hgen := pResidual_sup_sylow_eq_top T
  have hTD : (T : Subgroup X) ≤ normalizer (D : Set X) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    change D.map (MulAut.conj t).toMonoidHom = D
    dsimp only [D]
    have hr : (pResidual 2 X).map (MulAut.conj t).toMonoidHom = pResidual 2 X :=
      mem_normalizer_iff_map_conj_eq.mp (show t ∈ normalizer (pResidual 2 X : Set X) from
        le_normalizer_of_normal (mem_top t))
    have hj : J.map (MulAut.conj t).toMonoidHom = J :=
      mem_normalizer_iff_map_conj_eq.mp (hTJ ht)
    rw [map_commutator, hr, hj]
  have hDn : D.Normal := normalizer_eq_top_iff.mp (top_unique (hgen ▸
    sup_le (normalizer_commutator_ge_left _ _) hTD))
  let _ := hDn
  let E := J ⊔ D
  have hEn : E.Normal := normalizer_eq_top_iff.mp (top_unique (hgen ▸ sup_le
    (le_normalizer_sup_of_commutator_le J (pResidual 2 X) J D le_rfl
      (by rw [commutator_comm]))
    ((le_inf hTJ hTD).trans (normalizer_inf_normalizer_le_normalizer_sup J D))))
  let _ := hEn
  obtain ⟨M, hM, _⟩ := hu.2
  have hEM : ¬ E ≤ M := by
    intro hEM
    apply hJ
    exact (le_inf hJT (show J ≤ E from le_sup_left)).trans
      (sylow_inf_normal_le_twoCore_of_uniqueMaximal T hu M E ⟨hM.1, hM.2.isCoatom⟩ hEM)
  have hET : E ⊔ (T : Subgroup X) = ⊤ := by
    by_contra hne
    exact hEM (le_sup_left.trans (hu.le_maximal hM le_sup_right (lt_top_iff_ne_top.mpr hne)))
  have hDT : D ⊔ (T : Subgroup X) = ⊤ := by
    apply top_unique
    rw [← hET]
    exact sup_le (sup_le (hJT.trans le_sup_right) le_sup_left) le_sup_right
  exact le_antisymm (commutator_le_left _ _)
    (sInf_le ⟨hDn, isPGroup_quotient_of_sup_eq_top D T T.isPGroup' hDT⟩)

end Subgroup
end
