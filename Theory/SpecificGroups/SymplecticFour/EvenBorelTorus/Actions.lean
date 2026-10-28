module

public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Construction
public import Theory.FieldTheory.BinaryTorusInvolution
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Field and exceptional graph actions on the symplectic Borel torus

The two determinant characters intertwine entrywise field automorphisms
with coordinatewise field action. Direct evaluation of the exterior-square
minors proves that the exceptional graph automorphism acts by (x,y) ↦ (y,x²)
on every Borel matrix. This action squares to Frobenius and stabilizes the
actual unipotent subgroup.

For a field involution over a field of order 2^(2m), the displacement image
on this rank-two torus has order (2^m+1)². It exceeds three even for m=1,
so the rank-one order-three exception does not extend to Sp₄(4). Fixing the
three-residual forces m=1 or m=3 by the binary torus arithmetic.
These are calculations for the indicated actors; arbitrary two-power actors
still require reduction to the graph-generated torus action.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954; GLS3, Theorem
2.5.1 for the exceptional graph map, constructed in the imported module.
-/

@[expose] public section
noncomputable section
open Subgroup Matrix
namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
open DiagramAutomorphisms DiagramAutomorphisms.ExceptionalGraph
variable {F : Type*} [Field F]

/-- Entrywise field action in the two determinant coordinates. -/
def fieldTorus (σ : F ≃+* F) : MulAut (Fˣ × Fˣ) :=
  (Units.mapEquiv σ.toMulEquiv).prodCongr (Units.mapEquiv σ.toMulEquiv)

@[simp] theorem fieldTorus_apply (σ : F ≃+* F) (x : Fˣ × Fˣ) :
    fieldTorus σ x = (Units.map σ.toMonoidHom x.1, Units.map σ.toMonoidHom x.2) := rfl

theorem field_mem_borel (σ : F ≃+* F) (g : Sp F) (hg : g ∈ borel) :
    fieldAutomorphism σ g ∈ borel := by
  rw [mem_borel_iff] at hg ⊢
  exact ⟨by change σ (g.val (.inl 1) (.inl 0)) = 0; rw [hg.1, map_zero],
    fun i j => by change σ (g.val (.inr i) (.inl j)) = 0; rw [hg.2 i j, map_zero]⟩

theorem characters_field (σ : F ≃+* F) (g : borel (F := F)) :
    borelCharacters ⟨fieldAutomorphism σ g, field_mem_borel σ g g.property⟩ =
      fieldTorus σ (borelCharacters g) := by
  apply Prod.ext <;> apply Units.ext
  · change (determinantCharacter (point F) _ : F) =
      σ (determinantCharacter (point F) _ : F)
    rw [point_determinant, point_determinant]
    rfl
  · change (determinantCharacter (plane F) _ : F) =
      σ (determinantCharacter (plane F) _ : F)
    rw [plane_determinant, plane_determinant, map_sub, map_mul, map_mul]
    rfl


/-- Displacement in the actual split torus; its image measures the odd commutator quotient. -/
def torusDisplacement (τ : MulAut (Fˣ × Fˣ)) : (Fˣ × Fˣ) →* (Fˣ × Fˣ) where
  toFun x := τ x * x⁻¹
  map_one' := by simp
  map_mul' x y := by simp [mul_comm, mul_left_comm, mul_assoc]

theorem field_displacement (σ : F ≃+* F) :
    torusDisplacement (fieldTorus σ) =
      (FiniteField.BinaryTorusInvolution.displacement σ).prodMap
        (FiniteField.BinaryTorusInvolution.displacement σ) := by
  ext x <;> rfl

variable [Finite F]

/-- A field involution has displacement of order (2^m+1)² on the rank-two torus. -/
theorem field_displacement_card (σ : F ≃+* F) {m : ℕ} (hm : 0 < m)
    (hF : Nat.card F = 2 ^ (2 * m))
    (hσ : ∀ x : F, σ x = x ^ (2 ^ m)) :
    Nat.card (torusDisplacement (fieldTorus σ)).range = (2 ^ m + 1) ^ 2 := by
  rw [field_displacement, MonoidHom.range_prodMap,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    FiniteField.BinaryTorusInvolution.card_displacement σ hm hF hσ, pow_two]

/-- Rank two excludes the small order-three bound even over F₄. -/
theorem field_displacement_gt_three (σ : F ≃+* F) {m : ℕ} (hm : 0 < m)
    (hF : Nat.card F = 2 ^ (2 * m))
    (hσ : ∀ x : F, σ x = x ^ (2 ^ m)) :
    3 < Nat.card (torusDisplacement (fieldTorus σ)).range := by
  rw [field_displacement_card σ hm hF hσ]
  have hp : 2 ≤ (2 : ℕ) ^ m := by
    simpa using Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ m by omega)
  nlinarith

/-- Fixing the three-residual on both coordinates forces the source degrees two or six. -/
theorem field_fixed_residual_degree (σ : F ≃+* F) {m : ℕ} (hm : 0 < m)
    (hF : Nat.card F = 2 ^ (2 * m))
    (hσ : ∀ x : F, σ x = x ^ (2 ^ m))
    (hfix : ∀ x ∈ pResidual 3 (Fˣ × Fˣ), fieldTorus σ x = x) :
    2 * m = 2 ∨ 2 * m = 6 := by
  have hf : ∀ u ∈ pResidual 3 Fˣ, Units.map σ.toMonoidHom u = u := by
    intro u hu
    have hm := map_pResidual_le 3 (MonoidHom.inl Fˣ Fˣ) ⟨u, hu, rfl⟩
    exact congrArg Prod.fst (hfix (u, 1) hm)
  rcases FiniteField.BinaryTorusInvolution.half_degree_of_fixed_residual σ hm hF hσ hf
      with h | h <;> omega

variable [CharP F 2]

/-- The exceptional graph action swaps the determinant coordinates and squares one. -/
def graphTorus : MulAut (Fˣ × Fˣ) :=
  (MulEquiv.prodComm : (Fˣ × Fˣ) ≃* (Fˣ × Fˣ)).trans
    ((MulEquiv.refl Fˣ).prodCongr (Units.mapEquiv (frobeniusEquiv F 2).toMulEquiv))

@[simp] theorem graphTorus_apply (x : Fˣ × Fˣ) : graphTorus x = (x.2, x.1 ^ 2) := by
  apply Prod.ext rfl
  apply Units.ext
  rfl

theorem graphTorus_square : graphTorus (F := F) ^ 2 = fieldTorus (frobeniusEquiv F 2) := by
  apply MulEquiv.ext
  intro x
  change graphTorus (graphTorus x) = _
  rw [graphTorus_apply, graphTorus_apply, fieldTorus_apply]
  apply Prod.ext <;> apply Units.ext <;> rfl

theorem graph_mem_borel (g : Sp F) (hg : g ∈ borel) : graphAut g ∈ borel := by
  rw [mem_borel_iff] at hg ⊢
  constructor
  · simp [graphAut_apply, graphEnd, graphMatrix, minor, first, second, hg.2]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [graphAut_apply, graphEnd, graphMatrix, minor, first, second, hg.1, hg.2]

omit [Finite F] [CharP F 2] in
private theorem borel_dual_second (g : borel (F := F)) :
    g.val.val (.inl 1) (.inl 1) * g.val.val (.inr 1) (.inr 1) = 1 := by
  have hz := (mem_borel_iff g.val).mp g.property
  have h (i j : Fin 2 ⊕ Fin 2) := congrArg (fun M => M i j)
    (SymplecticGroup.mem_iff'.mp g.val.property)
  have h00 := h (.inl 0) (.inr 0)
  have h01 := h (.inl 0) (.inr 1)
  have h11 := h (.inl 1) (.inr 1)
  simp [Matrix.mul_apply, Matrix.J, Matrix.fromBlocks, Fintype.sum_sum_type,
    Fin.sum_univ_two, hz.1, hz.2, Matrix.transpose_apply] at h00 h01 h11
  have ha := left_ne_zero_of_mul_eq_one h00
  have h21 := h01.resolve_left ha
  simpa only [h21, mul_zero, neg_zero, zero_add, neg_inj] using h11

/-- The graph formula holds on the entire Borel, not merely on diagonal representatives. -/
theorem characters_graph (g : borel (F := F)) :
    borelCharacters (F := F)
      ⟨graphAut (F := F) g.val, graph_mem_borel (F := F) g.val g.property⟩ =
      graphTorus (borelCharacters g) := by
  rw [graphTorus_apply]
  have hz := (mem_borel_iff g.val).mp g.property
  apply Prod.ext <;> apply Units.ext
  · change (determinantCharacter (point F) _ : F) =
      (determinantCharacter (plane F) _ : F)
    rw [point_determinant, plane_determinant]
    change graphMatrix g.val.val (.inl 0) (.inl 0) =
      g.val.val (.inl 0) (.inl 0) * g.val.val (.inl 1) (.inl 1) -
        g.val.val (.inl 0) (.inl 1) * g.val.val (.inl 1) (.inl 0)
    simp [graphMatrix, minor, first, second, hz.1]
  · change (determinantCharacter (plane F) _ : F) =
      (determinantCharacter (point F) _ : F) ^ 2
    rw [plane_determinant, point_determinant]
    change graphMatrix g.val.val (.inl 0) (.inl 0) *
        graphMatrix g.val.val (.inl 1) (.inl 1) -
      graphMatrix g.val.val (.inl 0) (.inl 1) *
        graphMatrix g.val.val (.inl 1) (.inl 0) = g.val.val (.inl 0) (.inl 0) ^ 2
    dsimp [graphMatrix, minor, first, second]
    simp only [hz.1, hz.2, mul_zero, add_zero, sub_zero]
    calc
      _ = (g.val.val (.inl 0) (.inl 0)) ^ 2 *
          (g.val.val (.inl 1) (.inl 1) * g.val.val (.inr 1) (.inr 1)) := by ring
      _ = _ := by rw [borel_dual_second, mul_one]

/-- The graph action stabilizes the unipotent subgroup as well as the Borel. -/
theorem graph_mem_unipotent (g : Sp F) (hg : g ∈ unipotent) : graphAut g ∈ unipotent := by
  have hb := (mem_unipotent_iff g).mp hg |>.1
  apply (borelCharacters_eq_one ⟨graphAut g, graph_mem_borel g hb⟩).mp
  rw [characters_graph ⟨g, hb⟩, (borelCharacters_eq_one ⟨g, hb⟩).mpr hg, map_one]

theorem graph_map_borel : borel.map (graphAut (F := F)).toMonoidHom = borel := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨g, hg, rfl⟩
    exact graph_mem_borel g hg
  · rw [card_map_of_injective (f := graphAut.toMonoidHom) graphAut.injective]

theorem graph_map_unipotent : unipotent.map (graphAut (F := F)).toMonoidHom = unipotent := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨g, hg, rfl⟩
    exact graph_mem_unipotent g hg
  · rw [card_map_of_injective (f := graphAut.toMonoidHom) graphAut.injective]

end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
