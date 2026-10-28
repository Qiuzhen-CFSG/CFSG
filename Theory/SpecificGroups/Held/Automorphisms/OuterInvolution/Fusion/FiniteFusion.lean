module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion.Reduction
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion.Table
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion.FiniteData

/-!
# Exhaustive fusion in the outer Held Sylow coset

A moved point of the square excludes every binary index outside the 64-entry
tree. Each tree edge is conjugation by an actual inner Sylow generator.
The four-point base for the full normalizer certifies all edge identities;
tree induction gives Held conjugacy to the published outer representative.
These checks concern the literal coset words, not an abstract two-group.

Source: GLS3 Table 5.3p and its pp.260–261 interpretation; the fixed ATLAS
HeG1-p2058B0 model. Discovery data are not used as proof.
-/

namespace Held.OuterInvolution.Fusion
open LocalPairs LocalPairs.SylowGeometry
open InvolutionFixedData.Coverage

private theorem checkedAll {m : ℕ} (P : Fin m → Prop) [DecidablePred P]
    (h : (List.finRange m).all (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp h i (by simp))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem index_cases : ∀ n : Fin 1024,
    (normalPerm n * outerPerm) ((normalPerm n * outerPerm) (squareWitness n)) ≠
        squareWitness n ∨
      forestIndex (forestRow n) = n := by
  apply checkedAll
  decide +kernel

private theorem involution_index (n : Fin 1024) (hn : orderOf (oddWord n) = 2) :
    ∃ i : Fin 64, forestIndex i = n := by
  rcases index_cases n with hmove | hrow
  · have hp : oddWord n ^ 2 = 1 := by
      rw [← hn]
      exact pow_orderOf_eq_one _
    have hperm : (oddWord n).val ^ 2 = 1 := congrArg Subtype.val hp
    rw [oddWord_val] at hperm
    apply False.elim
    apply hmove
    change ((normalPerm n * outerPerm) ^ 2) (squareWitness n) = _
    rw [hperm]
    rfl
  · exact ⟨forestRow n, hrow⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem edge_checks : ∀ i : Fin 64, i ≠ 0 → ∀ x : Fin 4,
    (generatorPerm (forestGenerator i) *
        (normalPerm (forestIndex (forestParent i)) * outerPerm) *
        (generatorPerm (forestGenerator i))⁻¹) ⟨x.val, by omega⟩ =
      (normalPerm (forestIndex i) * outerPerm) ⟨x.val, by omega⟩ := by
  decide +kernel

private theorem edge_identity (i : Fin 64) (hi : i ≠ 0) :
    MulAut.conj (innerEmbedding (Calculations.generator (forestGenerator i)))
        (oddWord (forestIndex (forestParent i))) = oddWord (forestIndex i) := by
  apply normalizer_ext_four
  intro x
  change (representation (Calculations.generator (forestGenerator i)) *
    (oddWord (forestIndex (forestParent i))).val *
    (representation (Calculations.generator (forestGenerator i)))⁻¹) ⟨x.val, by omega⟩ =
      (oddWord (forestIndex i)).val ⟨x.val, by omega⟩
  rw [oddWord_val, oddWord_val, ← generatorPerm_eq]
  exact edge_checks i hi x

/-- Every involution in the specified 1024-word outer coset is Held-conjugate
to the published representative. All exhaustion and tree identities are checked. -/
public theorem oddWord_isCovered (n : Fin 1024) (hn : orderOf (oddWord n) = 2) :
    IsCovered (oddWord n) := by
  have hroot : IsCovered (oddWord 0) := by
    rw [oddWord, normalForm_zero, map_one, one_mul]
    exact outer_isCovered
  have hforest (i : Fin 64) : IsCovered (oddWord (forestIndex i)) := by
    induction i using Fin.strong_induction_on with
    | h i ih =>
      by_cases hi : i = 0
      · subst i
        rw [forest_root]
        exact hroot
      · exact edge_identity i hi ▸ (ih (forestParent i) (forest_parent_lt i hi)).conj
          (innerEmbedding (Calculations.generator (forestGenerator i)))
  obtain ⟨i, rfl⟩ := involution_index n hn
  exact hforest i

end Held.OuterInvolution.Fusion
