module

public import Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition.Placement
public import Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition.Cubic

/-!
# Literal residual recognition for index-three Sylow overgroups in S₇

An overgroup of the standard Sylow subgroup with relative index three has
order 48. The orbit argument places it in one of three subgroups of that
order, hence identifies the overgroup itself. Their residuals are the two
lifted tetrahedral actions and the three-point cyclic action. Sylow
conjugacy transports these equalities as actual permutation subgroups.

The result requires only one index-three overgroup. In particular, it
supplies the residual-recognition premise of
`BinaryPermutation.LocalResidualSeed.seven_of_residual_conjugacy` for either
member of a generating pair, with no representation-theoretic assumption.

Source: Aschbacher–Smith, I.5 and the final proof of 15.3.1, printed p.1155
(combined manuscript of 1 March 2004).
-/

public section

open Subgroup
open Theory.SpecificGroups.SymmetricSeven.LocalResidualModels
namespace Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition

/-- The three actual index-three overgroups of the standard Sylow subgroup. -/
theorem index_three_over_standardTwo (H : Subgroup S7) (hB : standardTwo ≤ H)
    (hi : standardTwo.relIndex H = 3) :
    H = duadOvergroup ∨ H = synthemeOvergroup ∨ H = cubicOvergroup := by
  rcases index_three_placement H hB hi with hd | hs | hc
  · exact Or.inl hd
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr (eq_of_le_of_card_ge hc (by
      rw [cubicOvergroup_card, index_three_card H hB hi])))

/-- The embedded two-residual of any index-three Sylow overgroup has one of
exactly the three concrete actions consumed by the natural-module bounds. -/
theorem residual_conjugacy (T : Sylow 2 S7) (P : Subgroup S7)
    (hT : (T : Subgroup S7) ≤ P) (hi : (T : Subgroup S7).relIndex P = 3) :
    ∃ g : S7,
      (pResidual 2 P).map P.subtype = duadResidual7.map (MulAut.conj g).toMonoidHom ∨
      (pResidual 2 P).map P.subtype = synthemeResidual7.map (MulAut.conj g).toMonoidHom ∨
      (pResidual 2 P).map P.subtype = cubicResidual7.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S7 standardSylow T
  let e := MulAut.conj g
  have he : e.mapSubgroup standardTwo = (T : Subgroup S7) := by
    change ((g • standardSylow : Sylow 2 S7) : Subgroup S7) = (T : Subgroup S7)
    rw [hg]
  let P₀ := e.mapSubgroup.symm P
  have hb : standardTwo ≤ P₀ := by
    have hh := e.mapSubgroup.symm.monotone hT
    rwa [← he, e.mapSubgroup.symm_apply_apply] at hh
  have hii : standardTwo.relIndex P₀ = 3 := by
    have hh := relIndex_map_map_of_injective (f := e.toMonoidHom) standardTwo P₀ e.injective
    change (e.mapSubgroup standardTwo).relIndex (e.mapSubgroup P₀) = _ at hh
    rw [he, e.mapSubgroup.apply_symm_apply] at hh
    exact hh.symm.trans hi
  have hP : P = P₀.map e.toMonoidHom := (e.mapSubgroup.apply_symm_apply P).symm
  have hr : (pResidual 2 P).map P.subtype =
      ((pResidual 2 P₀).map P₀.subtype).map e.toMonoidHom := by
    rw [map_embedded_pResidual, ← hP]
  rw [hr]
  rcases index_three_over_standardTwo P₀ hb hii with hd | hs | hc
  · refine ⟨g, Or.inl ?_⟩
    rw [hd, residual_duadOvergroup]
  · refine ⟨g, Or.inr (Or.inl ?_)⟩
    rw [hs, residual_synthemeOvergroup]
  · refine ⟨g * cubicConjugator, Or.inr (Or.inr ?_)⟩
    rw [hc, residual_cubicOvergroup, map_map]
    congr 1

end Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
