module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Definitions
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Properness of the two Rudvalis local candidates

Each pair of ATLAS subgroup generators preserves a small finite point set
which the ambient generator a does not preserve. This certifies that both
max4 and max6 are proper subgroups of the actual degree-4060 model, without
any subgroup or ambient cardinality calculation. All six finite checks are
kernel reductions of the original Lean group words.

Consequently a maximal subgroup contained in a conjugate of either candidate
equals that conjugate. The final lemma supplies the resulting multiplicative
equivalence, for use by the local normalizer calculation.

Source: the preserved ATLAS programs `RuG1-max4W1` and `RuG1-max6W1` in
`SylowOvergroups/source/`, translated in `SylowOvergroups.Definitions`.
The two point sets were found with GAP from those programs; their invariance
and noninvariance below are independently checked against the degree-4060
ATLAS permutation tables, with labels shifted to zero as in `PermutationData`.
No claim that these sets are full orbits is needed or made.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage

open scoped Pointwise

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

private def fixedSet4 : Finset (Fin 4060) :=
  {74, 78, 125, 404, 417, 727, 739, 745, 774, 1022, 1152, 1182, 1385, 1439,
    1680, 1751, 2049, 2145, 2319, 2419, 2774, 2803, 3146, 3326, 3396, 3418,
    3565, 3613}

private def fixedSet6 : Finset (Fin 4060) :=
  {556, 704, 811, 945, 1155, 1213, 1808, 2783, 3188, 3388, 3406, 3718}

private theorem pairClosure_ne_top (x y : Model) (s : Finset (Fin 4060))
    (hx : x • s = s) (hy : y • s = s) (ha : a • s ≠ s) :
    Subgroup.closure ({x, y} : Set Model) ≠ ⊤ := by
  have hle : Subgroup.closure ({x, y} : Set Model) ≤ MulAction.stabilizer Model s := by
    apply (Subgroup.closure_le _).mpr
    rintro z (rfl | hz)
    · exact MulAction.mem_stabilizer_iff.mpr hx
    · obtain rfl := Set.mem_singleton_iff.mp hz
      exact MulAction.mem_stabilizer_iff.mpr hy
  intro heq
  exact ha (MulAction.mem_stabilizer_iff.mp (hle (heq.symm ▸ Subgroup.mem_top a)))

/-- The fourth ATLAS candidate is proper, certified by an invariant point set. -/
public theorem max4_ne_top : max4 ≠ ⊤ := by
  exact pairClosure_ne_top max4Generators.1 max4Generators.2 fixedSet4
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The sixth ATLAS candidate is proper, certified by an invariant point set. -/
public theorem max6_ne_top : max6 ≠ ⊤ := by
  exact pairClosure_ne_top max6Generators.1 max6Generators.2 fixedSet6
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem equiv_of_le_map (M K : Subgroup Model) (hM : IsCoatom M)
    (hK : K ≠ ⊤) (e : MulAut Model) (hle : M ≤ K.map e.toMonoidHom) :
    Nonempty (M ≃* K) := by
  have hproper : K.map e.toMonoidHom ≠ ⊤ := by
    intro heq
    apply hK
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact heq.trans (Subgroup.map_equiv_top e).symm
  have heq : K.map e.toMonoidHom = M := (hM.le_iff.mp hle).resolve_left hproper
  exact ⟨(MulEquiv.subgroupCongr heq).symm.trans (e.subgroupMap K).symm⟩

/-- For a maximal subgroup, containment in an actual conjugate of either
proper candidate gives the required isomorphism type. -/
public theorem coatom_equiv_candidates_of_le_conjugate (M : Subgroup Model)
    (hM : IsCoatom M)
    (hcover : (∃ g : Model, M ≤ max4.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g : Model, M ≤ max6.map (MulAut.conj g).toMonoidHom)) :
    Nonempty (M ≃* max4) ∨ Nonempty (M ≃* max6) := by
  rcases hcover with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact Or.inl (equiv_of_le_map M max4 hM max4_ne_top (MulAut.conj g) hg)
  · exact Or.inr (equiv_of_le_map M max6 hM max6_ne_top (MulAut.conj g) hg)

end Rudvalis.SylowOvergroups.RadicalCoverage
