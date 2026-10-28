module

public import Theory.Representation.G2.RestrictedModules
import Mathlib.Tactic.Module

/-!
# Normalized unipotent embeddings of the restricted G₂ factors

Each of the four actual restricted factors embeds in the level-two Steinberg
orbit carrier after restriction to the positive unipotent subgroup. The maps
send the specified highest vectors to the Steinberg highest vector, with scalar
one. This supplies the embedding input of the tensor fixed-line reduction.

For the natural and adjoint factors, the maps are explicit linear combinations
of the sparse orbit tensors. Selected ambient tensor coordinates give left
inverses. The six arbitrary-parameter root identities follow from the published
sparse root formulas, by normalizing field coefficients in characteristic two;
the actual unipotent product then gives intertwining on the whole subgroup.
The adjoint map is transported through the equivalence with actual octonion
derivations. The trivial map is the highest line, and the Steinberg map is the
identity. All proofs work over arbitrary characteristic-two fields.

These are concrete supporting calculations for GLS3, 2.8.6–9 and 2.8.10(g),
and Aschbacher–Smith, G.9.3(10), printed pp.354,356–357. They do not assume
simplicity, cyclicity or tensor fixed-line uniqueness. The underlying octonion
coordinates use the existing ATLAS port; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`.
-/

public noncomputable section
open scoped BigOperators
namespace Atlas.G2.TensorClassification.FixedLine.RestrictedEmbeddings
open Restricted Restricted.Steinberg Restricted.Steinberg.OrbitClosure
open Restricted.Adjoint Restricted.Adjoint.Coordinates

set_option linter.unusedSimpArgs false
variable (F : Type*) [Field F] [CharP F 2]

private def inOrbit (v : Steinberg.Ambient F) (hv : v ∈ Steinberg.binarySpan F) : Steinberg.Space F :=
  ⟨v, by
    change v ∈ (Steinberg.orbitSpan F).toSubmodule
    rw [← Steinberg.binarySpan_eq_orbitSpan]
    exact hv⟩

private def linearCombination {n : ℕ} (f : Fin n → Steinberg.Space F) :
    (Fin n → F) →ₗ[F] Steinberg.Space F where
  toFun v := ∑ i, v i • f i
  map_add' v w := by
    simp only [Pi.add_apply, add_smul]
    rw [Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_smul]
    change (a • v i) • f i = (a * v i) • f i
    rfl

/-- Images of the six natural coordinate vectors, in their given order. -/
private def naturalMap : NaturalCoordinates.Space F →ₗ[F] Steinberg.Space F :=
  linearCombination F ![inOrbit F (b0 F) (b0_mem_binarySpan F), inOrbit F (b4 F) (b4_mem_binarySpan F),
    inOrbit F (b5 F) (b5_mem_binarySpan F), inOrbit F (b7 F) (b7_mem_binarySpan F),
    inOrbit F (b15 F + b24 F + b36 F) (by
      exact (binarySpan F).add_mem ((binarySpan F).add_mem (b15_mem_binarySpan F) (b24_mem_binarySpan F))
        (b36_mem_binarySpan F)),
    inOrbit F (b10 F + b16 F + b25 F + b50 F) (by
      exact (binarySpan F).add_mem ((binarySpan F).add_mem ((binarySpan F).add_mem
        (b10_mem_binarySpan F) (b16_mem_binarySpan F)) (b25_mem_binarySpan F)) (b50_mem_binarySpan F))]

/-- Images of the fourteen adjoint parameter vectors, before transport to derivations. -/
private def adjointMap : Coordinates.Space F →ₗ[F] Steinberg.Space F :=
  linearCombination F ![inOrbit F (b0 F) (b0_mem_binarySpan F),
    inOrbit F (b1 F) (b1_mem_binarySpan F),
    inOrbit F (b5 F + b12 F) ((binarySpan F).add_mem (b5_mem_binarySpan F) (b12_mem_binarySpan F)),
    inOrbit F (b7 F + b23 F) ((binarySpan F).add_mem (b7_mem_binarySpan F) (b23_mem_binarySpan F)),
    inOrbit F (b2 F) (b2_mem_binarySpan F),
    inOrbit F (b17 F + b37 F) ((binarySpan F).add_mem (b17_mem_binarySpan F) (b37_mem_binarySpan F)),
    inOrbit F (b9 F + b15 F + b24 F + b36 F) ((binarySpan F).add_mem ((binarySpan F).add_mem ((binarySpan F).add_mem (b9_mem_binarySpan F) (b15_mem_binarySpan F)) (b24_mem_binarySpan F)) (b36_mem_binarySpan F)),
    inOrbit F (b3 F) (b3_mem_binarySpan F),
    inOrbit F (b30 F + b42 F + b45 F) ((binarySpan F).add_mem ((binarySpan F).add_mem (b30_mem_binarySpan F) (b42_mem_binarySpan F)) (b45_mem_binarySpan F)),
    inOrbit F (b32 F + b40 F) ((binarySpan F).add_mem (b32_mem_binarySpan F) (b40_mem_binarySpan F)),
    inOrbit F (b28 F + b39 F) ((binarySpan F).add_mem (b28_mem_binarySpan F) (b39_mem_binarySpan F)),
    inOrbit F (b20 F + b38 F) ((binarySpan F).add_mem (b20_mem_binarySpan F) (b38_mem_binarySpan F)),
    inOrbit F (b10 F + b16 F + b25 F) ((binarySpan F).add_mem ((binarySpan F).add_mem (b10_mem_binarySpan F) (b16_mem_binarySpan F)) (b25_mem_binarySpan F)),
    inOrbit F (b9 F + b36 F) ((binarySpan F).add_mem (b9_mem_binarySpan F) (b36_mem_binarySpan F))]

/-- Six tensor entries recover the natural input. -/
private def naturalMap_read (x : Steinberg.Space F) : Fin 6 → F :=
  ![Steinberg.coordinates F x.val (0, 0, 1),
    Steinberg.coordinates F x.val (1, 0, 1),
    Steinberg.coordinates F x.val (0, 1, 2),
    Steinberg.coordinates F x.val (0, 1, 3),
    Steinberg.coordinates F x.val (0, 0, 5),
    Steinberg.coordinates F x.val (1, 0, 5)]

private theorem naturalMap_val (v : Fin 6 → F) : (naturalMap F v).val =
    v 0 • (b0 F) +
    v 1 • (b4 F) +
    v 2 • (b5 F) +
    v 3 • (b7 F) +
    v 4 • (b15 F + b24 F + b36 F) +
    v 5 • (b10 F + b16 F + b25 F + b50 F) := by
  simp [naturalMap, linearCombination, inOrbit, Fin.sum_univ_succ, add_assoc]

private theorem naturalMap_read_0 (v : Fin 6 → F) : naturalMap_read F (naturalMap F v) 0 = v 0 := by
  simp only [naturalMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, naturalMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b4, b5, b7, b10, b15, b16, b24, b25, b36, b50, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem naturalMap_read_1 (v : Fin 6 → F) : naturalMap_read F (naturalMap F v) 1 = v 1 := by
  simp only [naturalMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, naturalMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b4, b5, b7, b10, b15, b16, b24, b25, b36, b50, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem naturalMap_read_2 (v : Fin 6 → F) : naturalMap_read F (naturalMap F v) 2 = v 2 := by
  simp only [naturalMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, naturalMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b4, b5, b7, b10, b15, b16, b24, b25, b36, b50, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem naturalMap_read_3 (v : Fin 6 → F) : naturalMap_read F (naturalMap F v) 3 = v 3 := by
  simp only [naturalMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, naturalMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b4, b5, b7, b10, b15, b16, b24, b25, b36, b50, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem naturalMap_read_4 (v : Fin 6 → F) : naturalMap_read F (naturalMap F v) 4 = v 4 := by
  simp only [naturalMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, naturalMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b4, b5, b7, b10, b15, b16, b24, b25, b36, b50, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem naturalMap_read_5 (v : Fin 6 → F) : naturalMap_read F (naturalMap F v) 5 = v 5 := by
  simp only [naturalMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, naturalMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b4, b5, b7, b10, b15, b16, b24, b25, b36, b50, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem naturalMap_read_apply (v : Fin 6 → F) : naturalMap_read F (naturalMap F v) = v := by
  funext i
  fin_cases i
  · exact naturalMap_read_0 F v
  · exact naturalMap_read_1 F v
  · exact naturalMap_read_2 F v
  · exact naturalMap_read_3 F v
  · exact naturalMap_read_4 F v
  · exact naturalMap_read_5 F v

private theorem naturalMap_injective : Function.Injective (naturalMap F) := by
  intro v w h
  have hc := congrArg (naturalMap_read F) h
  simpa only [naturalMap_read_apply] using hc

private theorem naturalMap_highest : naturalMap F (Pi.single 0 1) = Steinberg.highestVector F := by
  apply Subtype.ext
  simp [naturalMap, linearCombination, inOrbit, Fin.sum_univ_succ, Steinberg.highestVector, Steinberg.seed, b0]

/-- Thirteen entries and the sum of two entries recover the adjoint parameters. -/
private def adjointMap_read (x : Steinberg.Space F) : Fin 14 → F :=
  ![Steinberg.coordinates F x.val (0, 0, 1),
    Steinberg.coordinates F x.val (0, 0, 2),
    Steinberg.coordinates F x.val (1, 0, 2),
    Steinberg.coordinates F x.val (1, 0, 3),
    Steinberg.coordinates F x.val (0, 0, 3),
    Steinberg.coordinates F x.val (2, 0, 4),
    Steinberg.coordinates F x.val (2, 0, 3),
    Steinberg.coordinates F x.val (0, 0, 4),
    Steinberg.coordinates F x.val (2, 3, 4),
    Steinberg.coordinates F x.val (0, 3, 5),
    Steinberg.coordinates F x.val (3, 0, 4),
    Steinberg.coordinates F x.val (0, 2, 5),
    Steinberg.coordinates F x.val (0, 1, 5),
    Steinberg.coordinates F x.val (1, 0, 4) + Steinberg.coordinates F x.val (2, 0, 3)]

private theorem adjointMap_val (v : Fin 14 → F) : (adjointMap F v).val =
    v 0 • (b0 F) +
    v 1 • (b1 F) +
    v 2 • (b5 F + b12 F) +
    v 3 • (b7 F + b23 F) +
    v 4 • (b2 F) +
    v 5 • (b17 F + b37 F) +
    v 6 • (b9 F + b15 F + b24 F + b36 F) +
    v 7 • (b3 F) +
    v 8 • (b30 F + b42 F + b45 F) +
    v 9 • (b32 F + b40 F) +
    v 10 • (b28 F + b39 F) +
    v 11 • (b20 F + b38 F) +
    v 12 • (b10 F + b16 F + b25 F) +
    v 13 • (b9 F + b36 F) := by
  simp [adjointMap, linearCombination, inOrbit, Fin.sum_univ_succ, add_assoc]

private theorem adjointMap_read_0 (v : Fin 14 → F) : adjointMap_read F (adjointMap F v) 0 = v 0 := by
  simp only [adjointMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, adjointMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b1, b2, b3, b5, b7, b9, b10, b12, b15, b16, b17, b20, b23, b24, b25, b28, b30, b32, b36, b37,
      b38, b39, b40, b42, b45, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem adjointMap_read_1 (v : Fin 14 → F) : adjointMap_read F (adjointMap F v) 1 = v 1 := by
  simp only [adjointMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, adjointMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b1, b2, b3, b5, b7, b9, b10, b12, b15, b16, b17, b20, b23, b24, b25, b28, b30, b32, b36, b37,
      b38, b39, b40, b42, b45, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem adjointMap_read_2 (v : Fin 14 → F) : adjointMap_read F (adjointMap F v) 2 = v 2 := by
  simp only [adjointMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, adjointMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b1, b2, b3, b5, b7, b9, b10, b12, b15, b16, b17, b20, b23, b24, b25, b28, b30, b32, b36, b37,
      b38, b39, b40, b42, b45, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem adjointMap_read_3 (v : Fin 14 → F) : adjointMap_read F (adjointMap F v) 3 = v 3 := by
  simp only [adjointMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, adjointMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b1, b2, b3, b5, b7, b9, b10, b12, b15, b16, b17, b20, b23, b24, b25, b28, b30, b32, b36, b37,
      b38, b39, b40, b42, b45, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem adjointMap_read_4 (v : Fin 14 → F) : adjointMap_read F (adjointMap F v) 4 = v 4 := by
  simp only [adjointMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, adjointMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b1, b2, b3, b5, b7, b9, b10, b12, b15, b16, b17, b20, b23, b24, b25, b28, b30, b32, b36, b37,
      b38, b39, b40, b42, b45, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem adjointMap_read_5 (v : Fin 14 → F) : adjointMap_read F (adjointMap F v) 5 = v 5 := by
  simp only [adjointMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, adjointMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b1, b2, b3, b5, b7, b9, b10, b12, b15, b16, b17, b20, b23, b24, b25, b28, b30, b32, b36, b37,
      b38, b39, b40, b42, b45, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem adjointMap_read_6 (v : Fin 14 → F) : adjointMap_read F (adjointMap F v) 6 = v 6 := by
  simp only [adjointMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, adjointMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b1, b2, b3, b5, b7, b9, b10, b12, b15, b16, b17, b20, b23, b24, b25, b28, b30, b32, b36, b37,
      b38, b39, b40, b42, b45, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem adjointMap_read_7 (v : Fin 14 → F) : adjointMap_read F (adjointMap F v) 7 = v 7 := by
  simp only [adjointMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, adjointMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b1, b2, b3, b5, b7, b9, b10, b12, b15, b16, b17, b20, b23, b24, b25, b28, b30, b32, b36, b37,
      b38, b39, b40, b42, b45, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem adjointMap_read_8 (v : Fin 14 → F) : adjointMap_read F (adjointMap F v) 8 = v 8 := by
  simp only [adjointMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, adjointMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b1, b2, b3, b5, b7, b9, b10, b12, b15, b16, b17, b20, b23, b24, b25, b28, b30, b32, b36, b37,
      b38, b39, b40, b42, b45, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem adjointMap_read_9 (v : Fin 14 → F) : adjointMap_read F (adjointMap F v) 9 = v 9 := by
  simp only [adjointMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, adjointMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b1, b2, b3, b5, b7, b9, b10, b12, b15, b16, b17, b20, b23, b24, b25, b28, b30, b32, b36, b37,
      b38, b39, b40, b42, b45, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem adjointMap_read_10 (v : Fin 14 → F) : adjointMap_read F (adjointMap F v) 10 = v 10 := by
  simp only [adjointMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, adjointMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b1, b2, b3, b5, b7, b9, b10, b12, b15, b16, b17, b20, b23, b24, b25, b28, b30, b32, b36, b37,
      b38, b39, b40, b42, b45, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem adjointMap_read_11 (v : Fin 14 → F) : adjointMap_read F (adjointMap F v) 11 = v 11 := by
  simp only [adjointMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, adjointMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b1, b2, b3, b5, b7, b9, b10, b12, b15, b16, b17, b20, b23, b24, b25, b28, b30, b32, b36, b37,
      b38, b39, b40, b42, b45, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem adjointMap_read_12 (v : Fin 14 → F) : adjointMap_read F (adjointMap F v) 12 = v 12 := by
  simp only [adjointMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, adjointMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b1, b2, b3, b5, b7, b9, b10, b12, b15, b16, b17, b20, b23, b24, b25, b28, b30, b32, b36, b37,
      b38, b39, b40, b42, b45, Steinberg.e, CharTwo.add_self_eq_zero]

private theorem adjointMap_read_13 (v : Fin 14 → F) : adjointMap_read F (adjointMap F v) 13 = v 13 := by
  simp only [adjointMap_read, Matrix.cons_val_zero, Matrix.cons_val_succ, adjointMap_val,
    map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simp [b0, b1, b2, b3, b5, b7, b9, b10, b12, b15, b16, b17, b20, b23, b24, b25, b28, b30, b32, b36, b37,
      b38, b39, b40, b42, b45, Steinberg.e, CharTwo.add_self_eq_zero]
  rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]

private theorem adjointMap_read_apply (v : Fin 14 → F) : adjointMap_read F (adjointMap F v) = v := by
  funext i
  fin_cases i
  · exact adjointMap_read_0 F v
  · exact adjointMap_read_1 F v
  · exact adjointMap_read_2 F v
  · exact adjointMap_read_3 F v
  · exact adjointMap_read_4 F v
  · exact adjointMap_read_5 F v
  · exact adjointMap_read_6 F v
  · exact adjointMap_read_7 F v
  · exact adjointMap_read_8 F v
  · exact adjointMap_read_9 F v
  · exact adjointMap_read_10 F v
  · exact adjointMap_read_11 F v
  · exact adjointMap_read_12 F v
  · exact adjointMap_read_13 F v

private theorem adjointMap_injective : Function.Injective (adjointMap F) := by
  intro v w h
  have hc := congrArg (adjointMap_read F) h
  simpa only [adjointMap_read_apply] using hc

private theorem adjointMap_highest : adjointMap F (Pi.single 0 1) = Steinberg.highestVector F := by
  apply Subtype.ext
  simp [adjointMap, linearCombination, inOrbit, Fin.sum_univ_succ, Steinberg.highestVector, Steinberg.seed, b0]
private theorem natural_roots (r : Fin 6) (a : F) (v : NaturalCoordinates.Space F) :
    naturalMap F (NaturalCoordinates.action F (![rootA a, rootB a, rootC a, rootD a, rootE a, rootF a] r) v) =
      Steinberg.action F (![rootA a, rootB a, rootC a, rootD a, rootE a, rootF a] r) (naturalMap F v) := by
  apply Subtype.ext
  fin_cases r <;>
    simp [naturalMap, linearCombination, NaturalCoordinates.action_rootA, NaturalCoordinates.action_rootB,
      NaturalCoordinates.action_rootC, NaturalCoordinates.action_rootD,
      NaturalCoordinates.action_rootE, NaturalCoordinates.action_rootF, inOrbit,
      Steinberg.action_val, rootA_b0, rootA_b4, rootA_b5, rootA_b7, rootA_b15,
      rootA_b24, rootA_b36, rootA_b10, rootA_b16, rootA_b25, rootA_b50,
      rootB_b0, rootB_b4, rootB_b5, rootB_b7, rootB_b15, rootB_b24, rootB_b36,
      rootB_b10, rootB_b16, rootB_b25, rootB_b50,
      rootC_b0, rootC_b4, rootC_b5, rootC_b7, rootC_b15, rootC_b24, rootC_b36,
      rootC_b10, rootC_b16, rootC_b25, rootC_b50,
      rootD_b0, rootD_b4, rootD_b5, rootD_b7, rootD_b15, rootD_b24, rootD_b36,
      rootD_b10, rootD_b16, rootD_b25, rootD_b50,
      rootE_b0, rootE_b4, rootE_b5, rootE_b7, rootE_b15, rootE_b24, rootE_b36,
      rootE_b10, rootE_b16, rootE_b25, rootE_b50,
      rootF_b0, rootF_b4, rootF_b5, rootF_b7, rootF_b15, rootF_b24, rootF_b36,
      rootF_b10, rootF_b16, rootF_b25, rootF_b50, Fin.sum_univ_succ,
      smul_add, add_smul, smul_smul]
  all_goals
    have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have hthree : (3 : F) = 1 := by
      calc (3 : F) = 2 + 1 := by norm_num
           _ = 0 + 1 := by rw [htwo]
           _ = 1 := by simp
    have hfour : (4 : F) = 0 := by
      calc (4 : F) = 2 + 2 := by norm_num
           _ = 0 := by rw [htwo]; simp
    match_scalars <;> ring_nf <;> simp only [htwo, hthree, hfour, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add]

private theorem adjoint_roots (r : Fin 6) (a : F) (v : Coordinates.Space F) :
    adjointMap F (Coordinates.action F (![rootA a, rootB a, rootC a, rootD a, rootE a, rootF a] r) v) =
      Steinberg.action F (![rootA a, rootB a, rootC a, rootD a, rootE a, rootF a] r) (adjointMap F v) := by
  apply Subtype.ext
  fin_cases r <;>
    simp [adjointMap, linearCombination, Coordinates.action_rootA, Coordinates.action_rootB,
      Coordinates.action_rootC, Coordinates.action_rootD,
      Coordinates.action_rootE, Coordinates.action_rootF, inOrbit,
      Steinberg.action_val,
      rootA_b0, rootA_b1, rootA_b2, rootA_b3, rootA_b5, rootA_b7, rootA_b9, rootA_b10, rootA_b12,
      rootA_b15, rootA_b16, rootA_b17, rootA_b20, rootA_b23, rootA_b24, rootA_b25, rootA_b28, rootA_b30,
      rootA_b32, rootA_b36, rootA_b37, rootA_b38, rootA_b39, rootA_b40, rootA_b42, rootA_b45,
      rootB_b0, rootB_b1, rootB_b2, rootB_b3, rootB_b5, rootB_b7, rootB_b9, rootB_b10, rootB_b12,
      rootB_b15, rootB_b16, rootB_b17, rootB_b20, rootB_b23, rootB_b24, rootB_b25, rootB_b28, rootB_b30,
      rootB_b32, rootB_b36, rootB_b37, rootB_b38, rootB_b39, rootB_b40, rootB_b42, rootB_b45,
      rootC_b0, rootC_b1, rootC_b2, rootC_b3, rootC_b5, rootC_b7, rootC_b9, rootC_b10, rootC_b12,
      rootC_b15, rootC_b16, rootC_b17, rootC_b20, rootC_b23, rootC_b24, rootC_b25, rootC_b28, rootC_b30,
      rootC_b32, rootC_b36, rootC_b37, rootC_b38, rootC_b39, rootC_b40, rootC_b42, rootC_b45,
      rootD_b0, rootD_b1, rootD_b2, rootD_b3, rootD_b5, rootD_b7, rootD_b9, rootD_b10, rootD_b12,
      rootD_b15, rootD_b16, rootD_b17, rootD_b20, rootD_b23, rootD_b24, rootD_b25, rootD_b28, rootD_b30,
      rootD_b32, rootD_b36, rootD_b37, rootD_b38, rootD_b39, rootD_b40, rootD_b42, rootD_b45,
      rootE_b0, rootE_b1, rootE_b2, rootE_b3, rootE_b5, rootE_b7, rootE_b9, rootE_b10, rootE_b12,
      rootE_b15, rootE_b16, rootE_b17, rootE_b20, rootE_b23, rootE_b24, rootE_b25, rootE_b28, rootE_b30,
      rootE_b32, rootE_b36, rootE_b37, rootE_b38, rootE_b39, rootE_b40, rootE_b42, rootE_b45,
      rootF_b0, rootF_b1, rootF_b2, rootF_b3, rootF_b5, rootF_b7, rootF_b9, rootF_b10, rootF_b12,
      rootF_b15, rootF_b16, rootF_b17, rootF_b20, rootF_b23, rootF_b24, rootF_b25, rootF_b28, rootF_b30,
      rootF_b32, rootF_b36, rootF_b37, rootF_b38, rootF_b39, rootF_b40, rootF_b42, rootF_b45,
      Fin.sum_univ_succ,
      smul_add, add_smul, smul_smul]
  all_goals match_scalars <;> ring_nf <;>
    simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

/-- The normalized embeddings of the four actual restricted factors in the
level-two Steinberg carrier, as modules for the positive unipotent subgroup. -/
def embedding : (a : Factor) → Restricted.Space F a →ₗ[F] Restricted.Space F .steinberg
  | .trivial => LinearMap.toSpanSingleton F _ (Steinberg.highestVector F)
  | .natural => naturalMap F
  | .adjoint => (adjointMap F).comp (Coordinates.equiv F).toLinearMap
  | .steinberg => LinearMap.id

/-- Each of the four displayed maps has zero kernel. -/
theorem embedding_injective (a : Factor) : Function.Injective (embedding F a) := by
  cases a with
  | trivial =>
    exact LinearMap.ker_eq_bot.mp
      (LinearMap.ker_toSpanSingleton F (Steinberg.highestVector_ne_zero F))
  | natural => exact naturalMap_injective F
  | adjoint => exact (adjointMap_injective F).comp (Coordinates.equiv F).injective
  | steinberg => exact Function.injective_id

/-- Normalization is at the actual highest vectors, with scalar exactly one. -/
theorem embedding_highestVector (a : Factor) :
    embedding F a (Restricted.highestVector F a) =
      Restricted.highestVector F .steinberg := by
  cases a with
  | trivial => exact one_smul F _
  | natural => exact naturalMap_highest F
  | adjoint =>
    change adjointMap F (Coordinates.equiv F (Adjoint.highestVector F)) = _
    rw [Adjoint.equiv_highestVector]
    exact adjointMap_highest F
  | steinberg => rfl

private theorem embedding_roots (a : Factor) (r : Fin 6) (t : F)
    (v : Restricted.Space F a) :
    embedding F a (Restricted.action F a
      (![rootA t, rootB t, rootC t, rootD t, rootE t, rootF t] r) v) =
    Restricted.action F .steinberg
      (![rootA t, rootB t, rootC t, rootD t, rootE t, rootF t] r) (embedding F a v) := by
  cases a with
  | trivial =>
    change F at v
    change v • Steinberg.highestVector F =
      Steinberg.action F _ (v • Steinberg.highestVector F)
    rw [map_smul]
    congr 1
    obtain ⟨hA, hB, hC, hD, hE, hF⟩ := Steinberg.highestVector_fixed_roots F t
    fin_cases r <;> simp_all
  | natural => exact natural_roots F r t v
  | adjoint =>
    change Adjoint.Space F at v
    change adjointMap F (Coordinates.equiv F (Adjoint.action F _ v)) =
      Steinberg.action F _ (adjointMap F (Coordinates.equiv F v))
    rw [Adjoint.equiv_action]
    exact adjoint_roots F r t _
  | steinberg => rfl

/-- Intertwining holds on the full positive unipotent group at arbitrary field
parameters, by its actual six-root product decomposition. -/
theorem embedding_intertwines (a : Factor) (g : Model F)
    (hg : g ∈ (unipotent : Subgroup (Model F))) (v : Restricted.Space F a) :
    embedding F a (Restricted.action F a g v) =
      Restricted.action F .steinberg g (embedding F a v) := by
  have hA := embedding_roots F a 0
  have hB := embedding_roots F a 1
  have hC := embedding_roots F a 2
  have hD := embedding_roots F a 3
  have hE := embedding_roots F a 4
  have hF := embedding_roots F a 5
  simp at hA hB hC hD hE hF
  rw [unipotent_eq_range] at hg
  obtain ⟨t, rfl⟩ := hg
  simp only [unipotentProduct, map_mul, Module.End.mul_apply]
  rw [hA, hB, hC, hD, hE, hF]

/-- The complete embedding input of `tensor_fixed_unipotent_of_steinberg_data`.
It is uniform over all characteristic-two fields and has no simplicity,
cyclicity, fixed-line or classification premise. -/
theorem exists_normalized_unipotent_embeddings :
    ∃ j : (a : Factor) → Restricted.Space F a →ₗ[F] Restricted.Space F .steinberg,
      (∀ a, Function.Injective (j a)) ∧
      (∀ a, j a (Restricted.highestVector F a) = Restricted.highestVector F .steinberg) ∧
      (∀ a g, g ∈ (unipotent : Subgroup (Model F)) → ∀ v,
        j a (Restricted.action F a g v) = Restricted.action F .steinberg g (j a v)) :=
  ⟨embedding F, embedding_injective F, embedding_highestVector F, embedding_intertwines F⟩

end Atlas.G2.TensorClassification.FixedLine.RestrictedEmbeddings
end
