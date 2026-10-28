module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit.MonomialWitness.Preparation
import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# A common ambient Sylow two-subgroup in the literal PSL₃(5):2

The determinant-one diagonal torus has order 16. Adjoining the signed swap
`[4,0,0;0,0,4;0,4,0]` doubles its order, and adjoining inverse transpose doubles
it again. The faithful matrix embedding and the fact that graph is outside the
marked inner subgroup justify both counts on the literal automorphism carrier.
The ambient group has order 744000, so this subgroup has odd index 11625 and
is an ambient Sylow two-subgroup.

Both the original actor and the conjugate specified in `Preparation` lie in
this subgroup, which lies in the actual split monomial overgroup. The final
application discharges the simultaneous-placement premise of the weak-closure
movement argument. Solvability and the final E-member assembly have separate
owners.

Source: `FiveSourceAudit/source/README.md`, the explicit diagnostic matrices;
Aschbacher--Smith E.1.1--5 and E.1.14(7), printed pp.209--214. The existing
matrix, projective-order and simplicity results retain the imported ATLAS
attribution and license at `LICENSES/ATLAS.txt`.
-/

public section
open Subgroup
open scoped MatrixGroups Matrix Pointwise
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : IsSimpleGroup PSL(3, ZMod 5) := Atlas.psl_simple_high_rank 3 (by decide)
private abbrev D := (torusSL (ZMod 5)).range
private def swap : SL(3, ZMod 5) :=
  ⟨!![4,0,0;0,0,4;0,4,0], by decide +kernel⟩
private theorem swap_sq : swap ^ 2 = 1 := by decide +kernel
private theorem swap_inv : swap⁻¹ = swap := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using swap_sq)
private theorem swap_out : swap ∉ D := by
  rintro ⟨d, hd⟩
  have := congrArg (fun g : SL(3, ZMod 5) => g.val 1 2) hd
  exact (by decide : (0 : ZMod 5) ≠ 4) this
private theorem swap_conj (d : (ZMod 5)ˣ × (ZMod 5)ˣ) :
    swap * torusSL (ZMod 5) d * swap⁻¹ = torusSL (ZMod 5) (d.1, (d.1 * d.2)⁻¹) := by
  revert d
  decide +kernel
private theorem normalizes_of_involution {G : Type*} [Group G]
    (H : Subgroup G) (w : G) (hw : w ^ 2 = 1)
    (h : ∀ x ∈ H, w * x * w⁻¹ ∈ H) : w ∈ normalizer (H : Set G) := by
  intro x
  constructor
  · exact h x
  · intro hx
    have hh := h _ hx
    have he : w * (w * x * w⁻¹) * w⁻¹ = x := by
      calc
        _ = w ^ 2 * x * (w ^ 2)⁻¹ := by simp only [pow_two, mul_inv_rev, mul_assoc]
        _ = x := by rw [hw]; simp
    exact he ▸ hh
private theorem swap_normalizes : swap ∈ normalizer (D : Set SL(3, ZMod 5)) := by
  apply normalizes_of_involution D swap swap_sq
  rintro _ ⟨d, rfl⟩
  exact ⟨_, (swap_conj d).symm⟩
private noncomputable def linearTwo : Subgroup SL(3, ZMod 5) := D ⊔ zpowers swap
private theorem card_linearTwo : Nat.card linearTwo = 32 := by
  rw [linearTwo, card_sup_zpowers_of_normalizing_involution D swap swap_sq swap_out swap_normalizes]
  rw [← Nat.card_congr (MonoidHom.ofInjective (torusSL_injective (ZMod 5))).toEquiv]
  simp only [Nat.card_prod, Nat.card_units, Nat.card_zmod]
private theorem graph_sq : graphElement ^ 2 = 1 :=
  Subtype.ext (Matrix.PSL3.OuterSolvable.graph_sq (ZMod 5))
private noncomputable def diagonalInner : Subgroup Model := D.map innerSL
private noncomputable def linearTwoInner : Subgroup Model := linearTwo.map innerSL
private noncomputable def commonTwo : Subgroup Model := linearTwoInner ⊔ zpowers graphElement
private theorem graph_normalizes_diagonal : graphElement ∈ normalizer (diagonalInner : Set Model) := by
  apply normalizes_of_involution _ _ graph_sq
  rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
  rw [graph_innerSL, mul_inv_cancel_right]
  exact ⟨torusSL (ZMod 5) d⁻¹, ⟨_, rfl⟩,
    congrArg innerSL (graphSL_torusSL (ZMod 5) d).symm⟩
private theorem graph_commutes_swap : Commute graphElement (innerSL swap) := by
  change graphElement * innerSL swap = innerSL swap * graphElement
  rw [graph_innerSL]
  congr 2
  have ht : Matrix.SpecialLinearGroup.transpose swap = swap := by decide +kernel
  rw [ht, swap_inv]
private theorem graph_normalizes_linearTwo :
    graphElement ∈ normalizer (linearTwoInner : Set Model) := by
  change graphElement ∈ normalizer ((D ⊔ zpowers swap).map innerSL : Set Model)
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  apply normalizer_inf_normalizer_le_normalizer_sup _ _
  refine ⟨graph_normalizes_diagonal, ?_⟩
  apply centralizer_le_normalizer
  rw [mem_centralizer_iff]
  rintro x ⟨n, rfl⟩
  exact (graph_commutes_swap.zpow_right n).symm.eq
private theorem linearTwoInner_le_inner : linearTwoInner ≤ inner := by
  rw [← innerSL_range]
  exact map_le_range _ _
private theorem card_commonTwo : Nat.card commonTwo = 64 := by
  rw [commonTwo, card_sup_zpowers_of_normalizing_involution _ _ graph_sq
    (fun h => graphElement_not_mem_inner (linearTwoInner_le_inner h)) graph_normalizes_linearTwo]
  rw [linearTwoInner, card_map_of_injective innerSL_injective, card_linearTwo]
private theorem torus_preserves (d : (ZMod 5)ˣ × (ZMod 5)ˣ) {v : Fin 3 → ZMod 5}
    (hv : v ∈ Matrix.SL3.SplitMonomial.coordinateVectors (ZMod 5)) :
    torusSL (ZMod 5) d • v ∈ Matrix.SL3.SplitMonomial.coordinateVectors (ZMod 5) := by
  obtain ⟨i, hi, hv⟩ := hv
  change ∃ i, (Matrix.diagonal ![(d.1 : ZMod 5), ((d.1 * d.2)⁻¹ : (ZMod 5)ˣ), (d.2 : ZMod 5)] *ᵥ v) i ≠ 0 ∧ _
  refine ⟨i, ?_, ?_⟩
  · rw [Matrix.mulVec_diagonal]
    apply mul_ne_zero _ hi
    fin_cases i <;> exact Units.ne_zero _
  · intro j hj
    change (Matrix.diagonal _ *ᵥ v) j = 0
    rw [Matrix.mulVec_diagonal]
    change _ * v j = 0
    rw [hv j hj, mul_zero]
private theorem torus_mem_linear (d : (ZMod 5)ˣ × (ZMod 5)ˣ) :
    torusSL (ZMod 5) d ∈ Matrix.SL3.SplitMonomial.linear (ZMod 5) := by
  change torusSL (ZMod 5) d ∈ MulAction.stabilizer _ (Matrix.SL3.SplitMonomial.coordinateVectors (ZMod 5))
  rw [MulAction.mem_stabilizer_iff]
  apply Set.Subset.antisymm
  · exact Set.smul_set_subset_iff.mpr (fun _ hv => torus_preserves d hv)
  · rw [Set.subset_smul_set_iff, ← map_inv]
    exact Set.smul_set_subset_iff.mpr (fun _ hv => torus_preserves d⁻¹ hv)
private theorem swap_mem_linear : swap ∈ Matrix.SL3.SplitMonomial.linear (ZMod 5) := by
  change swap ∈ MulAction.stabilizer _ (Matrix.SL3.SplitMonomial.coordinateVectors (ZMod 5))
  rw [MulAction.mem_stabilizer_iff]
  apply Set.Subset.antisymm
  · apply Set.smul_set_subset_iff.mpr
    dsimp [Matrix.SL3.SplitMonomial.coordinateVectors]
    decide +kernel
  · rw [Set.subset_smul_set_iff, swap_inv]
    apply Set.smul_set_subset_iff.mpr
    dsimp [Matrix.SL3.SplitMonomial.coordinateVectors]
    decide +kernel
private theorem commonTwo_le_monomial : commonTwo ≤ monomialOvergroup := by
  apply sup_le _ le_sup_right
  apply (map_mono (show linearTwo ≤ Matrix.SL3.SplitMonomial.linear (ZMod 5) from ?_)).trans le_sup_left
  apply sup_le _ (zpowers_le.mpr swap_mem_linear)
  rintro _ ⟨d, rfl⟩
  exact torus_mem_linear d
private def unitFour : (ZMod 5)ˣ := ⟨4,4,by decide,by decide⟩
private def unitTwo : (ZMod 5)ˣ := ⟨2,3,by decide,by decide⟩
private theorem diagonal_mem_common (d : (ZMod 5)ˣ × (ZMod 5)ˣ) :
    innerSL (torusSL (ZMod 5) d) ∈ commonTwo :=
  mem_sup_left ⟨_, mem_sup_left ⟨_, rfl⟩, rfl⟩
private theorem graph_mem_common : graphElement ∈ commonTwo := mem_sup_right (mem_zpowers _)
private theorem second_mem_common : innerSL secondDiagonal ∈ commonTwo := by
  have he : torusSL (ZMod 5) (1, unitFour) = secondDiagonal := by decide +kernel
  exact he ▸ diagonal_mem_common (1, unitFour)
private theorem actor_le_commonTwo : actor ≤ commonTwo := by
  rw [actor, closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · have he : torusSL (ZMod 5) (unitFour, 1) = Matrix.SL3.standardInvolution (ZMod 5) := by decide +kernel
    exact he ▸ diagonal_mem_common (unitFour, 1)
  · exact second_mem_common
  · exact graph_mem_common
private theorem movedActor_le_commonTwo : movedActor ≤ commonTwo := by
  refine movedActor_le_of_generators ?_ second_mem_common ?_
  · have he : torusSL (ZMod 5) (1, unitTwo) * swap = witnessSwap := by decide +kernel
    rw [← he, map_mul]
    exact commonTwo.mul_mem (diagonal_mem_common _) (mem_sup_left ⟨_, mem_sup_right (mem_zpowers _), rfl⟩)
  · have he : torusSL (ZMod 5) (1, unitTwo) = witnessDiagonal := by decide +kernel
    exact commonTwo.mul_mem (he ▸ diagonal_mem_common _) graph_mem_common
private theorem inner_sup_graph : inner ⊔ zpowers graphElement = ⊤ := by
  apply Subgroup.map_injective (Matrix.PSL3.OddPrimeGraphExtension.graphExtension (ZMod 5)).subtype_injective
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  change (innerPart (ZMod 5)).map _ ⊔ zpowers (Matrix.PSL3.OuterSolvable.graph (ZMod 5)) = _
  rw [innerPart, map_subgroupOf_eq_of_le (show MulAut.innerSubgroup PSL(3, ZMod 5) ≤
    Matrix.PSL3.OddPrimeGraphExtension.graphExtension (ZMod 5) from le_sup_left)]
  rw [← MonoidHom.range_eq_map, range_subtype]
  rfl
private theorem card_model : Nat.card Model = 744000 := by
  let : inner.Normal := inferInstanceAs (innerPart (ZMod 5)).Normal
  have hc : Nat.card inner = 372000 := by
    change Nat.card (innerPart (ZMod 5)) = _
    rw [← Nat.card_congr (innerPartEquiv (ZMod 5)).toEquiv,
      Matrix.PSL3.LinearThree.card_projective]
    norm_num
  have hn : graphElement ∈ normalizer (inner : Set Model) :=
    (show (⊤ : Subgroup Model) ≤ normalizer (inner : Set Model) from
      le_normalizer_of_normal) (mem_top _)
  have h := card_sup_zpowers_of_normalizing_involution inner graphElement graph_sq
    graphElement_not_mem_inner hn
  rw [inner_sup_graph, card_top, hc] at h
  exact h

private theorem commonTwo_odd_index : ¬ 2 ∣ commonTwo.index := by
  have h := commonTwo.card_mul_index
  rw [card_commonTwo, card_model] at h
  have hi : commonTwo.index = 11625 := by omega
  rw [hi]
  decide

/-- Both literal actors lie in one ambient Sylow two-subgroup contained in the
literal split monomial overgroup, with no additional model assumptions. -/
theorem simultaneous_sylow_placement : ∃ T : Sylow 2 Model,
    actor ≤ (T : Subgroup Model) ∧ (T : Subgroup Model) ≤ monomialOvergroup ∧
      movedActor ≤ (T : Subgroup Model) := by
  have hp : IsPGroup 2 commonTwo := IsPGroup.of_card (n := 6) card_commonTwo
  exact ⟨hp.toSylow commonTwo_odd_index, actor_le_commonTwo, commonTwo_le_monomial,
    movedActor_le_commonTwo⟩

/-- The simultaneous Sylow placement discharges the weak-closure movement input. -/
theorem exists_monomial_sylow_motion : ∃ T : Sylow 2 Model,
    actor ≤ (T : Subgroup Model) ∧ (T : Subgroup Model) ≤ monomialOvergroup ∧
      ¬ monomialOvergroup ≤ normalizer (weakClosure (T : Subgroup Model) family : Set Model) := by
  obtain ⟨T, hAT, hTK, hBT⟩ := simultaneous_sylow_placement
  exact ⟨T, hAT, hTK, monomial_motion_of_movedActor_le T hBT⟩
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit
