module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.OctonionLocals

/-!
# The additive centralizer of the long and graph actions

Products of three long-root displacements isolate coordinate 0, including
multiplication by an arbitrary field element. Commutation therefore forces
an additive endomorphism to be scalar on that coordinate. Two further root
displacements and the literal graph permutation give the same scalar on
all six coordinates. This argument does not assume field linearity.

`ScalarLinearity` applies the result to the actual Y operator transported
through an arbitrary additive long frame.
Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, p.283.
The displacement formulas use the existing octonion block convention, also
used in `Long.Module.Model`.
-/

open Matrix
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Factorization
open OctonionLocals PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
variable {K : Type*} [Field K] [CharP K 2]

private def root01 (a : K) : SL(3,K) :=
  ⟨!![1,a,0;0,1,0;0,0,1], by simp [Matrix.det_fin_three]⟩
private def root12 (a : K) : SL(3,K) :=
  ⟨!![1,0,0;0,1,a;0,0,1], by simp [Matrix.det_fin_three]⟩
private def root20 (a : K) : SL(3,K) :=
  ⟨!![1,0,0;0,1,0;a,0,1], by simp [Matrix.det_fin_three]⟩

private def displacement (A : SL(3,K)) (v : Fin 6 → K) : Fin 6 → K :=
  action (BlockRealization.blockHom A) v - v

private theorem displacement01 (a : K) (v : Fin 6 → K) :
    displacement (root01 a) v = ![a * v 3,0,a * v 5,0,0,0] := by
  rw [displacement, action_block]
  ext i
  fin_cases i <;> simp [root01, BlockRealization.cofactor, Matrix.adjugate_fin_three,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, CharTwo.neg_eq]

private theorem displacement12 (a : K) (v : Fin 6 → K) :
    displacement (root12 a) v = ![0,a * v 2,0,a * v 4,0,0] := by
  rw [displacement, action_block]
  ext i
  fin_cases i <;> simp [root12, BlockRealization.cofactor, Matrix.adjugate_fin_three,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, CharTwo.neg_eq]

private theorem displacement20 (a : K) (v : Fin 6 → K) :
    displacement (root20 a) v = ![0,0,0,0,a * v 0,a * v 1] := by
  rw [displacement, action_block]
  ext i
  fin_cases i <;> simp [root20, BlockRealization.cofactor, Matrix.adjugate_fin_three,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, CharTwo.neg_eq]

private theorem displacement_cycle (a : K) (v : Fin 6 → K) :
    displacement (root01 1) (displacement (root12 1) (displacement (root20 a) v)) =
      Pi.single 0 (a * v 0) := by
  rw [displacement20, displacement12, displacement01]
  funext i
  fin_cases i <;> simp

private theorem displacement20_single (a b : K) :
    displacement (root20 a) (Pi.single 0 b) = Pi.single 4 (a * b) := by
  rw [displacement20]
  funext i
  fin_cases i <;> simp

private theorem displacement12_single (a b : K) :
    displacement (root12 a) (Pi.single 4 b) = Pi.single 3 (a * b) := by
  rw [displacement12]
  funext i
  fin_cases i <;> simp

private def graphIndex : Fin 6 → Fin 6 := ![5,3,4,1,2,0]

private theorem graph_single (j : Fin 6) (a : K) :
    action graph (Pi.single j a) = Pi.single (graphIndex j) a := by
  rw [action_graph]
  funext i
  fin_cases j <;> fin_cases i <;> simp [graphIndex]

theorem commuting_long_graph_scalar (f : (Fin 6 → K) →+ (Fin 6 → K))
    (hlong : ∀ A v, f (action (BlockRealization.blockHom A) v) =
      action (BlockRealization.blockHom A) (f v))
    (hgraph : ∀ v, f (action graph v) = action graph (f v)) :
    ∃ c : K, ∀ v, f v = c • v := by
  have hd (A : SL(3,K)) (v : Fin 6 → K) :
      f (displacement A v) = displacement A (f v) := by
    rw [displacement, map_sub, hlong]
    rfl
  have h0 (a : K) (v : Fin 6 → K) :
      f (Pi.single 0 (a * v 0)) = Pi.single 0 (a * f v 0) := by
    rw [← displacement_cycle, hd, hd, hd, displacement_cycle]
  let c := f (Pi.single 0 1) 0
  have hs0 (a : K) : f (Pi.single 0 a) = Pi.single 0 (c * a) := by
    simpa [c, mul_comm] using h0 a (Pi.single 0 1)
  have hs4 (a : K) : f (Pi.single 4 a) = Pi.single 4 (c * a) := by
    have h := hd (root20 1) (Pi.single 0 a)
    rw [displacement20_single, hs0, displacement20_single, one_mul, one_mul] at h
    exact h
  have hs3 (a : K) : f (Pi.single 3 a) = Pi.single 3 (c * a) := by
    have h := hd (root12 1) (Pi.single 4 a)
    rw [displacement12_single, hs4, displacement12_single, one_mul, one_mul] at h
    exact h
  have hs5 (a : K) : f (Pi.single 5 a) = Pi.single 5 (c * a) := by
    have h := hgraph (Pi.single 0 a)
    rw [graph_single, hs0, graph_single] at h
    exact h
  have hs1 (a : K) : f (Pi.single 1 a) = Pi.single 1 (c * a) := by
    have h := hgraph (Pi.single 3 a)
    rw [graph_single, hs3, graph_single] at h
    exact h
  have hs2 (a : K) : f (Pi.single (2 : Fin 6) a) = Pi.single (2 : Fin 6) (c * a) := by
    have h := hgraph (Pi.single 4 a)
    rw [graph_single, hs4, graph_single] at h
    exact h
  have hs (j : Fin 6) (a : K) : f (Pi.single j a) = Pi.single j (c * a) := by
    fin_cases j
    · exact hs0 a
    · exact hs1 a
    · exact hs2 a
    · exact hs3 a
    · exact hs4 a
    · exact hs5 a
  have he : f = (c • (LinearMap.id : (Fin 6 → K) →ₗ[K] (Fin 6 → K))).toAddMonoidHom := by
    apply AddMonoidHom.functions_ext
    intro j a
    simpa only [LinearMap.toAddMonoidHom_coe, LinearMap.smul_apply, LinearMap.id_apply, ← Pi.single_smul, smul_eq_mul] using hs j a
  exact ⟨c, fun v => DFunLike.congr_fun he v⟩

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Factorization
