module

public import Theory.Representation.PSL3Two.SmallModules
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.Matrix.Dual
/-!
# Automorphisms on the natural and dual binary three-dimensional modules

Inverse transpose exchanges the natural and contragredient actions via the dot
product. An explicit matrix with different traces in the two representations
proves they are inequivalent, and hence that inverse transpose is noninner.
The checked index two of the inner subgroup then gives the action of every
automorphism and identifies both module stabilizers with the inner subgroup.

These are concrete model facts used in Aschbacher–Smith 13.8.21(1), printed
p.956, and H.6, in the combined manuscript of 1 March 2004.
-/

public section
open Matrix Representation
namespace BinaryLinearThree.AutomorphismAction
private lemma sl_transpose_mul (g h : Group) : (g * h).transpose = h.transpose * g.transpose := by
  apply Subtype.ext
  exact Matrix.transpose_mul _ _
private lemma sl_transpose_transpose (g : Group) : g.transpose.transpose = g := by
  apply Subtype.ext
  rfl
private lemma sl_transpose_one : (1 : Group).transpose = 1 := by
  apply Subtype.ext
  exact Matrix.transpose_one
private lemma sl_transpose_inv (g : Group) : g⁻¹.transpose = g.transpose⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← sl_transpose_mul, mul_inv_cancel, sl_transpose_one]
/-- The inverse-transpose automorphism of the actual matrix group. -/
@[expose] def graph : MulAut Group where
  toFun g := g⁻¹.transpose
  invFun g := g⁻¹.transpose
  left_inv g := by simp only [sl_transpose_inv, inv_inv, sl_transpose_transpose]
  right_inv g := by simp only [sl_transpose_inv, inv_inv, sl_transpose_transpose]
  map_mul' g h := by rw [_root_.mul_inv_rev, sl_transpose_mul]
/-- Matrix formula for inverse transpose. -/
lemma graph_apply (g : Group) : graph g = g⁻¹.transpose := rfl
/-- Inverse transpose is an involution. -/
lemma graph_graph (g : Group) : graph (graph g) = g := graph.left_inv g
/-- The graph automorphism squares to the identity. -/
lemma graph_sq : graph * graph = 1 := by ext g : 1; exact graph_graph g
/-- The dot product intertwines the graph twist of the natural module with its dual. -/
def graphNaturalDual : Representation.Equiv (W.comp graph.toMonoidHom) W.dual where
  toLinearEquiv := dotProductEquiv (ZMod 2) (Fin 3)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change ((g⁻¹.val)ᵀ *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (g⁻¹.val *ᵥ w)
    rw [← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.transpose_transpose]

private def traceWitness : Group := ⟨!![0,0,1;1,0,1;0,1,0], by decide⟩
private def traceWitnessInv : Group := ⟨!![1,1,0;0,0,1;1,0,0], by decide⟩
private lemma traceWitness_inv : traceWitness⁻¹ = traceWitnessInv := by
  apply inv_eq_of_mul_eq_one_right
  decide
/-- The natural and contragredient modules are not intertwining-equivalent. -/
lemma natural_not_equiv_dual : ¬ Nonempty (Representation.Equiv W W.dual) := by
  rintro ⟨e⟩
  have ht := LinearMap.trace_conj' (W traceWitness) e.toLinearEquiv
  rw [e.conj_apply_self, Representation.dual_apply, LinearMap.trace_transpose',
    traceWitness_inv] at ht
  change LinearMap.trace (ZMod 2) Vector traceWitnessInv.val.toLin' =
    LinearMap.trace (ZMod 2) Vector traceWitness.val.toLin' at ht
  rw [Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq] at ht
  exact (by decide : traceWitnessInv.val.trace ≠ traceWitness.val.trace) ht

private def innerTwist {G V : Type*} [_root_.Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (g : G) (a : MulAut G) :
    Representation.Equiv (ρ.comp (MulAut.conj g * a).toMonoidHom)
      (ρ.comp a.toMonoidHom) where
  toLinearEquiv := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g⁻¹)
  isIntertwining' h := by
    change ρ g⁻¹ ∘ₗ ρ (g * a h * g⁻¹) = ρ (a h) ∘ₗ ρ g⁻¹
    change ρ g⁻¹ * ρ (g * a h * g⁻¹) = ρ (a h) * ρ g⁻¹
    rw [← ρ.map_mul, ← ρ.map_mul]
    apply congrArg ρ
    simp only [mul_assoc, inv_mul_cancel_left]

private def innerEquiv {G V : Type*} [_root_.Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (g : G) :
    Representation.Equiv (ρ.comp (MulAut.conj g).toMonoidHom) ρ := by
  have hρ : ρ.comp (1 : MulAut G).toMonoidHom = ρ := by ext; rfl
  simpa only [mul_one, hρ] using innerTwist ρ g 1

/-- The graph automorphism is outside the actual inner automorphism subgroup. -/
lemma graph_not_inner : graph ∉ MulAut.innerSubgroup Group := by
  rintro ⟨g, hg⟩
  apply natural_not_equiv_dual
  have e : Representation.Equiv (W.comp graph.toMonoidHom) W := hg ▸ innerEquiv W g
  exact ⟨e.symm.trans graphNaturalDual⟩

/-- Every noninner automorphism is inner times inverse transpose. -/
lemma outer_eq_inner_graph (a : MulAut Group) (ha : a ∉ MulAut.innerSubgroup Group) :
    ∃ g : Group, a = MulAut.conj g * graph := by
  have hm : a * graph ∈ MulAut.innerSubgroup Group :=
    (Subgroup.mul_mem_iff_of_index_two
      Matrix.PSL3Two.Automorphisms.card_outer_sl).mpr (iff_of_false ha graph_not_inner)
  obtain ⟨g, hg⟩ := hm
  refine ⟨g, ?_⟩
  rw [hg, mul_assoc, graph_sq, mul_one]

/-- Every noninner automorphism carries the natural representation to its dual. -/
noncomputable def naturalOuterEquiv (a : MulAut Group)
    (ha : a ∉ MulAut.innerSubgroup Group) :
    Representation.Equiv (W.comp a.toMonoidHom) W.dual := by
  let g := Classical.choose (outer_eq_inner_graph a ha)
  rw [Classical.choose_spec (outer_eq_inner_graph a ha)]
  exact (innerTwist W g graph).trans graphNaturalDual

/-- The inverse dot-product identification intertwines the graph twist of the dual. -/
def graphDualNatural : Representation.Equiv (W.dual.comp graph.toMonoidHom) W where
  toLinearEquiv := graphNaturalDual.symm.toLinearEquiv
  isIntertwining' g := by
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, graph_graph]
      using graphNaturalDual.symm.isIntertwining' (graph g)

/-- Every noninner automorphism carries the dual representation to the natural one. -/
noncomputable def dualOuterEquiv (a : MulAut Group)
    (ha : a ∉ MulAut.innerSubgroup Group) :
    Representation.Equiv (W.dual.comp a.toMonoidHom) W := by
  let g := Classical.choose (outer_eq_inner_graph a ha)
  rw [Classical.choose_spec (outer_eq_inner_graph a ha)]
  exact (innerTwist W.dual g graph).trans graphDualNatural

/-- Precisely the inner automorphisms stabilize the natural representation. -/
lemma natural_stabilizer (a : MulAut Group) :
    Nonempty (Representation.Equiv (W.comp a.toMonoidHom) W) ↔
      a ∈ MulAut.innerSubgroup Group := by
  constructor
  · rintro ⟨e⟩
    by_contra ha
    exact natural_not_equiv_dual ⟨e.symm.trans (naturalOuterEquiv a ha)⟩
  · rintro ⟨g, rfl⟩
    exact ⟨innerEquiv W g⟩
/-- Precisely the inner automorphisms stabilize the contragredient representation. -/
lemma dual_stabilizer (a : MulAut Group) :
    Nonempty (Representation.Equiv (W.dual.comp a.toMonoidHom) W.dual) ↔
      a ∈ MulAut.innerSubgroup Group := by
  constructor
  · rintro ⟨e⟩
    by_contra ha
    exact natural_not_equiv_dual ⟨(dualOuterEquiv a ha).symm.trans e⟩
  · rintro ⟨g, rfl⟩
    exact ⟨innerEquiv W.dual g⟩

end BinaryLinearThree.AutomorphismAction
