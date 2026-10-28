module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceLocalGeneration
public import Mathlib.GroupTheory.Commutator.Basic
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCoordinates
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceTensorProduct

/-!
# Faithfulness from the linear local geometry

The row is self-centralizing and its normalizer is transitive on its
nonidentity elements. Hence every nontrivial normal subgroup of that
normalizer contains the row. A marked row shear acts as a transposition on
the other two points of a source line. Conjugating it by the line reversal
moves the base point, which rules out a nontrivial normal core.

Thus the actual source coset action is faithful even before global generation
or ambient simplicity is known. This supplies the faithfulness needed for
the normalizer-generated subgroup in Aschbacher, *Sporadic Groups* (1994),
41.1, pp.219–220, without assuming that subgroup simple. The internal imports
reuse the previously checked marked shear and six-bit tensor coordinates.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
open PlaneTensor PlaneCensus GraphUniquenessSystem.Cosets
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

private def rowShearPoint : Subgroup.centralizer ({z} : Set G) :=
  F.equiv.symm ⟨PlaneTensor.generator 0, PlaneTensor.generator_centralizer 0⟩

private theorem rowShearPoint_mem : (rowShearPoint F : G) ∈ F.row := by
  apply (F.mem_pullback_iff Model.row (rowShearPoint F)).mpr
  change (F.equiv (F.equiv.symm _) : SL) ∈ Model.row
  rw [F.equiv.apply_symm_apply]
  change root (by decide : (0 : Fin 5) < 1) ∈ Model.row
  exact subset_closure ⟨1, by decide, rfl⟩

private theorem rowShearPoint_conj (x : Code) :
    (rowShearPoint F : G) * element F x * (rowShearPoint F : G)⁻¹ =
      element F (PlaneCensus.shear 0 x) := by
  have he : rowShearPoint F * (⟨element F x, F.pullback_le _ (element_mem F x)⟩ :
      Subgroup.centralizer ({z} : Set G)) * (rowShearPoint F)⁻¹ =
      ⟨element F (PlaneCensus.shear 0 x), F.pullback_le _ (element_mem F _)⟩ := by
    apply F.equiv.injective
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      rowShearPoint, F.equiv.apply_symm_apply, element_model]
    change PlaneTensor.generator 0 * modelElement (decode x) * (PlaneTensor.generator 0)⁻¹ =
      modelElement (decode (PlaneCensus.shear 0 x))
    rw [PlaneTensor.decode_shear, PlaneTensor.model_shear]
  exact congrArg Subtype.val he

variable [Finite G]
private def rowShear : sourcePlaneNormalizer F := ⟨rowShearPoint F, by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨x, hx⟩ := (sourceEquiv F).surjective ⟨a, ha⟩
    have hxa : element F x = a := congrArg Subtype.val hx
    change (rowShearPoint F : G) * a * (rowShearPoint F : G)⁻¹ ∈ F.plane
    rw [← hxa, rowShearPoint_conj]
    exact element_mem F _
  · rw [card_map_of_injective (MulAut.conj _).injective]⟩

private theorem tensor_label_unique : ∀ (i j : Fin 3) (v w : Fin 3 → ZMod 2),
    v ≠ 0 → w ≠ 0 → tensorCode i v = tensorCode j w → i = j := by decide
private theorem tensor_shear_label : ∀ (i : Fin 3) (v : Fin 3 → ZMod 2),
    PlaneCensus.shear 0 (tensorCode i v) = tensorCode (Equiv.swap 1 2 i) v := by decide

variable (hlinear : F.LinearFusion)
private theorem rowShear_action : lineAction F hlinear (rowShear F) = Equiv.swap 1 2 := by
  apply Equiv.ext
  intro i
  let v : Fin 3 → ZMod 2 := fun _ => 1
  have hv : v ≠ 0 := by intro h; have := congrFun h 0; exact zero_ne_one this.symm
  have h := lineAction_tensor F hlinear (rowShear F) i v
  change element F (tensorCode _ _) =
    (rowShearPoint F : G) * element F (tensorCode i v) * (rowShearPoint F : G)⁻¹ at h
  rw [rowShearPoint_conj, tensor_shear_label] at h
  exact tensor_label_unique _ _ _ _
    (fun hz => hv ((linearPlaneQuotientEquiv F hlinear
      (QuotientGroup.mk (rowShear F))).1.map_eq_zero_iff.mp hz)) hv (element_injective F h)

include hlinear in
/-- Every nontrivial normal subgroup of the row normalizer contains the row. -/
theorem row_le_normal_of_ne_bot (N : Subgroup (rowNormalizer F)) [N.Normal] (hN : N ≠ ⊥) :
    F.row.subgroupOf (rowNormalizer F) ≤ N := by
  let A := F.row.subgroupOf (rowNormalizer F)
  have hi : ¬ Disjoint N A := by
    intro hd
    have hc : N ≤ Subgroup.centralizer (A : Set (rowNormalizer F)) :=
      commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd)
    have hnA : N ≤ A := by
      intro n hn
      change (n : G) ∈ F.row
      rw [← row_centralizer_eq F]
      apply mem_centralizer_iff.mpr
      intro a ha
      exact congrArg Subtype.val (mem_centralizer_iff.mp (hc hn)
        ⟨a, F.row.le_normalizer ha⟩ ha)
    exact hN (bot_unique fun n hn => disjoint_def.mp hd hn (hnA hn))
  rw [disjoint_def] at hi
  push Not at hi
  obtain ⟨a, haN, haA, ha1⟩ := hi
  intro b hb
  by_cases hb1 : b = 1
  · simpa only [hb1] using N.one_mem
  obtain ⟨n, hn, _, he⟩ := row_subgroup_nonidentity_transitive F hlinear F.row le_rfl
    ⟨a, haA⟩ ⟨b, hb⟩ (by
      intro h
      have hv : (a : G) = 1 := congrArg (fun x : F.row => (x : G)) h
      exact ha1 (Subtype.ext hv)) (by
      intro h
      have hv : (b : G) = 1 := congrArg (fun x : F.row => (x : G)) h
      exact hb1 (Subtype.ext hv))
  have hnN := (inferInstance : N.Normal).conj_mem a haN ⟨n, hn⟩
  have he' : (⟨n, hn⟩ : rowNormalizer F) * a * (⟨n, hn⟩ : rowNormalizer F)⁻¹ = b :=
    Subtype.ext he
  exact he' ▸ hnN

include hlinear in
/-- Faithfulness of the literal source point action follows from local linear
geometry alone; no simplicity of the ambient group is required. -/
theorem linear_row_normalizer_core : (rowNormalizer F).normalCore = ⊥ := by
  let K := (rowNormalizer F).normalCore
  by_contra hK
  have hK' : K.subgroupOf (rowNormalizer F) ≠ ⊥ := by
    intro he
    apply hK
    apply bot_unique
    intro k hk
    have hk' : (⟨k, (rowNormalizer F).normalCore_le hk⟩ : rowNormalizer F) ∈ K.subgroupOf (rowNormalizer F) := hk
    rw [he] at hk'
    exact congrArg Subtype.val hk'
  have hA := row_le_normal_of_ne_bot F hlinear (K.subgroupOf (rowNormalizer F)) hK'
  have hnK : (rowShear F : G) ∈ K :=
    hA (x := ⟨rowShear F, F.row.le_normalizer (rowShearPoint_mem F)⟩) (rowShearPoint_mem F)
  let t := lineSwap F hlinear
  have hconj : (t : G) * (rowShear F : G) * (t : G)⁻¹ ∈ K :=
    (inferInstance : K.Normal).conj_mem _ hnK t
  have hfix := (lineAction_fix_iff F hlinear (t * rowShear F * t⁻¹)).mpr
    ((rowNormalizer F).normalCore_le hconj)
  rw [map_mul, map_mul, map_inv, rowShear_action, lineSwap_action] at hfix
  exact (by decide :
    (((Equiv.swap (0 : Fin 3) 1) * (Equiv.swap 1 2) * (Equiv.swap 0 1)⁻¹ : Equiv.Perm (Fin 3)) 0) ≠ 0) hfix

include hlinear in
/-- The linear fusion counts give a faithful action on the original point cosets. -/
theorem linear_point_action_faithful (g : G)
    (hg : ∀ a : Vertex (rowNormalizer F), g • a = a) : g = 1 :=
  GraphUniquenessSystem.Cosets.faithful _ (linear_row_normalizer_core F hlinear) g hg

include hlinear in
/-- The same faithful action is available for the induction overgroup of 41.1. -/
theorem normalizerSpan_row_core :
    (rowNormalizer (normalizerSpanMarking F)).normalCore = ⊥ :=
  linear_row_normalizer_core (normalizerSpanMarking F) (normalizerSpan_linearFusion F hlinear)

end Theory.GroupTheory.TransvectionFive.UniquenessLinear.SourceGeometry
