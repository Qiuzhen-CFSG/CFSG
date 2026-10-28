module

public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.SpecificGroups.HigherLinear.SubspaceTransport

/-!
# Coordinates for arbitrary SL₃ subspace stabilizers

A proper nonzero subspace has dimension one or two. Extend a subspace
isomorphism to the ambient three-space, and conjugate its stabilizer to
the literal point or plane parabolic used by the scalar-quotient API.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
C.2.7(3)(g), p.145, and 14.7.68(2), pp.1071–1072.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
namespace Matrix.PSL3.LinearThree.SubspaceTransport
variable {F : Type*} [Field F]

private abbrev V3 (F : Type*) := Fin 3 → F
private def pointSpace (F : Type*) [Field F] : Submodule F (V3 F) :=
  Submodule.span F {![1, 0, 0]}
private def lineSpace (F : Type*) [Field F] : Submodule F (V3 F) :=
  Submodule.span F {![1, 0, 0], ![0, 1, 0]}

private lemma pointSpace_eq (F : Type*) [Field F] (v : V3 F) :
    v ∈ pointSpace F ↔ v 1 = 0 ∧ v 2 = 0 := by
  rw [pointSpace, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    simp
  · intro h
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [h.1, h.2]

private lemma lineSpace_eq (F : Type*) [Field F] (v : V3 F) :
    v ∈ lineSpace F ↔ v 2 = 0 := by
  rw [lineSpace]
  constructor
  · intro hv
    rw [Submodule.mem_span_set] at hv
    obtain ⟨c, hc, hs⟩ := hv
    have hz : ∀ x ∈ c.support, x 2 = 0 := by
      intro x hx
      have hx' := hc hx
      rcases hx' with rfl | rfl <;> simp
    have hs2 := congrFun hs 2
    have hsum : (∑ x ∈ c.support, c x • x) 2 = 0 := by
      rw [show (∑ x ∈ c.support, c x • x) 2 =
        ∑ x ∈ c.support, (c x • x) 2 by simp only [Finset.sum_apply]]
      apply Finset.sum_eq_zero
      intro x hx
      simp [hz x hx]
    exact hs2.symm.trans hsum
  · intro hv
    rw [show v = v 0 • (![1,0,0] : V3 F) + v 1 • (![0,1,0] : V3 F) by
      ext i; fin_cases i <;> simp [hv]]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private lemma point_dim : Module.finrank F (pointSpace F) = 1 :=
  finrank_span_singleton (by intro h; have := congrFun h 0; simp at this)

private def lineEquiv : lineSpace F ≃ₗ[F] (Fin 2 → F) where
  toFun x i := x.val i.castSucc
  invFun v := ⟨![v 0,v 1,0], (lineSpace_eq F _).mpr rfl⟩
  left_inv x := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact ((lineSpace_eq F x.val).mp x.property).symm
  right_inv x := by ext i; fin_cases i <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma line_dim : Module.finrank F (lineSpace F) = 2 := by
  rw [(lineEquiv (F := F)).finrank_eq, Module.finrank_fin_fun]

private lemma point_eq [Finite F] :
    Matrix.HigherLinear.parabolicSL (pointSpace F) = pointParabolicSL F := by
  ext g
  rw [Matrix.HigherLinear.SubspaceTransport.mem_parabolicSL_iff, pointParabolicSL,
    MulAction.mem_stabilizer_set]
  simp only [pointSpace_eq, Set.mem_ofPred_eq]
  rfl

private lemma line_eq [Finite F] :
    Matrix.HigherLinear.parabolicSL (lineSpace F) = lineParabolicSL F := by
  ext g
  rw [Matrix.HigherLinear.SubspaceTransport.mem_parabolicSL_iff, lineParabolicSL,
    MulAction.mem_stabilizer_set]
  simp only [lineSpace_eq, Set.mem_ofPred_eq]
  rfl

/-- Every nonzero proper three-space stabilizer has point or plane coordinates. -/
theorem exists_parabolic_equiv [Finite F] (W : Submodule F (Fin 3 → F))
    (hW : W ≠ ⊥) (hWt : W ≠ ⊤) :
    Nonempty (Matrix.HigherLinear.parabolicSL W ≃* pointParabolicSL F) ∨
      Nonempty (Matrix.HigherLinear.parabolicSL W ≃* lineParabolicSL F) := by
  have hpos : 0 < Module.finrank F W :=
    Nat.pos_of_ne_zero (fun h => hW (Submodule.finrank_eq_zero.mp h))
  have hlt := Submodule.finrank_lt hWt
  rw [Module.finrank_fin_fun] at hlt
  have hc : Module.finrank F W = 1 ∨ Module.finrank F W = 2 := by omega
  rcases hc with hd | hd
  · left
    rw [← point_eq]
    exact Matrix.HigherLinear.SubspaceTransport.exists_stabilizerEquiv W (pointSpace F)
      (hd.trans point_dim.symm)
  · right
    rw [← line_eq]
    exact Matrix.HigherLinear.SubspaceTransport.exists_stabilizerEquiv W (lineSpace F)
      (hd.trans line_dim.symm)

end Matrix.PSL3.LinearThree.SubspaceTransport

end
