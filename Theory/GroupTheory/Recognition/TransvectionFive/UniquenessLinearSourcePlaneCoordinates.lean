module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Rectangles
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCensus
import Mathlib.Tactic.FinCases
/-!
# Marked matrix coordinates and elementary rectangle conjugations

Six bits parametrize the original plane subgroup through the full centralizer
marking. XOR is exactly its group law, zero is the identity, and code 4 is the
distinguished involution. The same coordinates describe its two-by-three
matrix block under the original model embedding.

The five shears used by the point-stabilizer orbit census are conjugations
by the actual elementary matrices at (0,1), (2,3), (3,2), (2,4), and (3,4).
Each centralizes the distinguished involution. Transporting those identities
through the marking supplies actual conjugating elements of C_G(z), rather
than an abstract permutation action on an unrelated six-space.

These are the local action inputs to the source 40.3 fusion proof in
Aschbacher, *Sporadic Groups* (1994), pp.217–218. The plane coordinate
isomorphism is reused from the shared rectangle calculation; no normalizer
identification or ambient recognition is assumed.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear.PlaneTensor
open UniquenessMathieu.SourceNormalizer
abbrev Six := Fin 2 → Fin 3 → ZMod 2

private def modelElement (v : Six) : SL :=
  (modelPlaneCoordinates.symm (Multiplicative.ofAdd v) : SL)
private theorem modelElement_matrix (v : Six) : (modelElement v).val =
    1 + Matrix.single 0 2 (v 0 0) + Matrix.single 0 3 (v 0 1) + Matrix.single 0 4 (v 0 2) +
    Matrix.single 1 2 (v 1 0) + Matrix.single 1 3 (v 1 1) + Matrix.single 1 4 (v 1 2) := by
  simpa only [modelElement, modelPlaneCoordinates.apply_symm_apply, toAdd_ofAdd] using
    modelPlaneCoordinates_matrix (modelPlaneCoordinates.symm (Multiplicative.ofAdd v))

private def shear (k : Fin 5) (v : Six) : Six :=
  match k.val with
  | 0 => ![v 0 + v 1, v 1]
  | 1 => fun i => ![v i 0, v i 1 + v i 0, v i 2]
  | 2 => fun i => ![v i 0 + v i 1, v i 1, v i 2]
  | 3 => fun i => ![v i 0, v i 1, v i 2 + v i 0]
  | _ => fun i => ![v i 0, v i 1, v i 2 + v i 1]

private def generator : Fin 5 → SL :=
  ![Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 5) ≠ 1) 1,
    Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 5) ≠ 3) 1,
    Matrix.SpecialLinearGroup.transvection (by decide : (3 : Fin 5) ≠ 2) 1,
    Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 5) ≠ 4) 1,
    Matrix.SpecialLinearGroup.transvection (by decide : (3 : Fin 5) ≠ 4) 1]

private theorem generator_inv (k : Fin 5) : (generator k)⁻¹ = generator k := by
  fin_cases k <;> simp [generator, Matrix.SpecialLinearGroup.transvection_inv,
    show (-1 : ZMod 2) = 1 from rfl]

private theorem generator_centralizer (k : Fin 5) : generator k ∈ centralizer := by
  apply mem_centralizer_singleton_iff.mpr
  fin_cases k <;> apply Subtype.ext <;>
    simp [generator, transvection, root, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_add, Matrix.add_mul, Matrix.single_mul_single_of_ne, add_comm, add_left_comm]

private def generatorRoot : Fin 5 → Fin 5 × Fin 5 := ![(0,1),(2,3),(3,2),(2,4),(3,4)]
private theorem generator_matrix (k : Fin 5) : (generator k).val =
    1 + Matrix.single (generatorRoot k).1 (generatorRoot k).2 1 := by
  fin_cases k <;> rfl

private theorem model_shear_0 (v : Six) :
    modelElement (shear 0 v) = generator 0 * modelElement v * (generator 0)⁻¹ := by
  apply Subtype.ext
  change (modelElement (shear 0 v)).val =
    (generator 0).val * (modelElement v).val * ((generator 0)⁻¹).val
  rw [generator_inv, modelElement_matrix, modelElement_matrix, generator_matrix]
  simp [generatorRoot, Matrix.mul_add, Matrix.add_mul, Matrix.single_mul_single_of_ne,
    Matrix.single_mul_single_same]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shear, Matrix.single]
  all_goals ring_nf
  all_goals simp [show (2 : ZMod 2) = 0 from rfl]

private theorem model_shear_1 (v : Six) :
    modelElement (shear 1 v) = generator 1 * modelElement v * (generator 1)⁻¹ := by
  apply Subtype.ext
  change (modelElement (shear 1 v)).val =
    (generator 1).val * (modelElement v).val * ((generator 1)⁻¹).val
  rw [generator_inv, modelElement_matrix, modelElement_matrix, generator_matrix]
  simp [generatorRoot, Matrix.mul_add, Matrix.add_mul, Matrix.single_mul_single_of_ne,
    Matrix.single_mul_single_same]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shear, Matrix.single]
  all_goals ring_nf
  all_goals simp [show (2 : ZMod 2) = 0 from rfl]

private theorem model_shear_2 (v : Six) :
    modelElement (shear 2 v) = generator 2 * modelElement v * (generator 2)⁻¹ := by
  apply Subtype.ext
  change (modelElement (shear 2 v)).val =
    (generator 2).val * (modelElement v).val * ((generator 2)⁻¹).val
  rw [generator_inv, modelElement_matrix, modelElement_matrix, generator_matrix]
  simp [generatorRoot, Matrix.mul_add, Matrix.add_mul, Matrix.single_mul_single_of_ne,
    Matrix.single_mul_single_same]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shear, Matrix.single]
  all_goals ring_nf
  all_goals simp [show (2 : ZMod 2) = 0 from rfl]

private theorem model_shear_3 (v : Six) :
    modelElement (shear 3 v) = generator 3 * modelElement v * (generator 3)⁻¹ := by
  apply Subtype.ext
  change (modelElement (shear 3 v)).val =
    (generator 3).val * (modelElement v).val * ((generator 3)⁻¹).val
  rw [generator_inv, modelElement_matrix, modelElement_matrix, generator_matrix]
  simp [generatorRoot, Matrix.mul_add, Matrix.add_mul, Matrix.single_mul_single_of_ne,
    Matrix.single_mul_single_same]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shear, Matrix.single]
  all_goals ring_nf
  all_goals simp [show (2 : ZMod 2) = 0 from rfl]

private theorem model_shear_4 (v : Six) :
    modelElement (shear 4 v) = generator 4 * modelElement v * (generator 4)⁻¹ := by
  apply Subtype.ext
  change (modelElement (shear 4 v)).val =
    (generator 4).val * (modelElement v).val * ((generator 4)⁻¹).val
  rw [generator_inv, modelElement_matrix, modelElement_matrix, generator_matrix]
  simp [generatorRoot, Matrix.mul_add, Matrix.add_mul, Matrix.single_mul_single_of_ne,
    Matrix.single_mul_single_same]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shear, Matrix.single]
  all_goals ring_nf
  all_goals simp [show (2 : ZMod 2) = 0 from rfl]

private theorem model_shear (k : Fin 5) (v : Six) :
    modelElement (shear k v) = generator k * modelElement v * (generator k)⁻¹ := by
  fin_cases k
  · exact model_shear_0 v
  · exact model_shear_1 v
  · exact model_shear_2 v
  · exact model_shear_3 v
  · exact model_shear_4 v
open PlaneCensus (Code)
private def bit (a : ZMod 2) : Bool := decide (a = 1)
private def val (b : Bool) : ZMod 2 := if b then 1 else 0

private def encode (v : Six) : Code :=
  BitVec.cons (bit (v 1 2)) (BitVec.cons (bit (v 1 1)) (BitVec.cons (bit (v 1 0))
    (BitVec.cons (bit (v 0 2)) (BitVec.cons (bit (v 0 1)) (BitVec.cons (bit (v 0 0)) 0)))))
def decode (x : Code) : Six := fun i j => val (x.getLsbD (i.val * 3 + j.val))
private theorem val_bit (a : ZMod 2) : val (bit a) = a := by fin_cases a <;> rfl
private theorem decode_encode (v : Six) : decode (encode v) = v := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [decode, encode, BitVec.getElem_cons, val_bit]
private theorem encode_decode : ∀ x : Code, encode (decode x) = x := by decide

def codeEquiv : Code ≃ Six where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode

private theorem val_xor (a b : Bool) : val (a ^^ b) = val a + val b := by
  cases a <;> cases b <;> decide

theorem decode_xor (x y : Code) : decode (x ^^^ y) = decode x + decode y := by
  funext i j
  simp [decode, val_xor]

def sourceEquiv {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z) :
    Code ≃ F.plane :=
  codeEquiv.trans (Multiplicative.ofAdd.trans
    (modelPlaneCoordinates.symm.toEquiv.trans
      (F.pullbackEquiv Model.plane Model.plane_le_centralizer).symm.toEquiv))

@[expose] def element {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z) (x : Code) : G :=
  (sourceEquiv F x : G)

variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

theorem element_injective : Function.Injective (element F) :=
  F.plane.subtype_injective.comp (sourceEquiv F).injective

theorem element_mem (x : Code) : element F x ∈ F.plane := (sourceEquiv F x).property

theorem element_model (x : Code) :
    (F.equiv ⟨element F x, F.pullback_le _ (element_mem F x)⟩ : SL) =
      (modelPlaneCoordinates.symm (Multiplicative.ofAdd (decode x)) : SL) := by
  exact congrArg Subtype.val
    ((F.pullbackEquiv Model.plane Model.plane_le_centralizer).apply_symm_apply _)

theorem element_xor (x y : Code) : element F (x ^^^ y) = element F x * element F y := by
  let e := (F.pullbackEquiv Model.plane Model.plane_le_centralizer).symm
  change ((e (modelPlaneCoordinates.symm (Multiplicative.ofAdd (decode (x ^^^ y))))) : G) = _
  rw [decode_xor, ofAdd_add, map_mul, map_mul]
  rfl

theorem element_zero : element F 0 = 1 := by
  have hd : decode 0 = 0 := by decide
  change (((F.pullbackEquiv Model.plane Model.plane_le_centralizer).symm
    (modelPlaneCoordinates.symm (Multiplicative.ofAdd (decode 0)))) : G) = 1
  rw [hd, ofAdd_zero, map_one, map_one]
  rfl

theorem element_point : element F 4 = z := by
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hm : (modelPlaneCoordinates.symm (Multiplicative.ofAdd (decode 4)) : SL) = transvection := by
    apply Subtype.ext
    rw [modelPlaneCoordinates_matrix, modelPlaneCoordinates.apply_symm_apply]
    simp [decode, val, transvection, root, Matrix.SpecialLinearGroup.transvection_coe]
  have he : (⟨element F 4, F.pullback_le _ (element_mem F 4)⟩ :
      Subgroup.centralizer ({z} : Set G)) = ⟨z, hzC⟩ := by
    apply F.equiv.injective
    apply Subtype.ext
    rw [element_model, F.on_point, hm]
  exact congrArg Subtype.val he

private theorem decode_shear : ∀ (k : Fin 5) (x : Code),
    decode (PlaneCensus.shear k x) = shear k (decode x) := by decide

/-- Each binary shear is induced on the whole rectangle by one element of
the marked point centralizer. The conjugating element is independent of the
coordinate being acted on. -/
theorem exists_shear_conjugator_uniform (k : Fin 5) :
    ∃ n ∈ Subgroup.centralizer ({z} : Set G),
      ∀ x : Code, n * element F x * n⁻¹ = element F (PlaneCensus.shear k x) := by
  let n := F.equiv.symm ⟨generator k, generator_centralizer k⟩
  refine ⟨n, n.property, fun x => ?_⟩
  have he : n * (⟨element F x, F.pullback_le _ (element_mem F x)⟩ :
      Subgroup.centralizer ({z} : Set G)) * n⁻¹ =
        ⟨element F (PlaneCensus.shear k x), F.pullback_le _ (element_mem F _)⟩ := by
    apply F.equiv.injective
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      n, F.equiv.apply_symm_apply, element_model]
    change generator k * modelElement (decode x) * (generator k)⁻¹ =
      modelElement (decode (PlaneCensus.shear k x))
    rw [decode_shear, model_shear]
  exact congrArg Subtype.val he

/-- The five binary shears are conjugations by actual elements of the full
marked point centralizer. -/
theorem exists_shear_conjugator (k : Fin 5) (x : Code) :
    ∃ n ∈ Subgroup.centralizer ({z} : Set G),
      n * element F x * n⁻¹ = element F (PlaneCensus.shear k x) := by
  obtain ⟨n, hn, hnx⟩ := exists_shear_conjugator_uniform F k
  exact ⟨n, hn, hnx x⟩

/-- The census predicate is the nonzero rank-one condition on the actual
binary two-by-three coordinate matrix. -/
theorem pure_iff_rank_one : ∀ x : Code, PlaneCensus.pure x = true ↔
    decode x ≠ 0 ∧ (decode x 0 = 0 ∨ decode x 1 = 0 ∨ decode x 0 = decode x 1) := by decide

/-- Code 1 is a row root different from the distinguished code 4. This
retains the actual row marking needed for nonweak closure in the two-core. -/
theorem element_one_mem_row : element F 1 ∈ F.row := by
  apply (F.mem_pullback_iff Model.row
    ⟨element F 1, F.pullback_le _ (element_mem F 1)⟩).mpr
  rw [element_model]
  have hm : modelElement (decode 1) = root (show (0 : Fin 5) < 2 by decide) := by
    apply Subtype.ext
    rw [modelElement_matrix]
    simp [decode, val, root, Matrix.SpecialLinearGroup.transvection_coe]
  change modelElement (decode 1) ∈ Model.row
  rw [hm]
  exact subset_closure ⟨2, by decide, rfl⟩

/-- The two named root codes are distinct in the actual source group. -/
theorem element_one_ne_point : element F 1 ≠ z := by
  intro he
  have hh := element_injective F (he.trans (element_point F).symm)
  exact (by decide : (1 : Code) ≠ 4) hh

/-- The second matrix row vanishes exactly on the first eight coordinate codes. -/
theorem decode_secondRow_zero_iff : ∀ x : Code, decode x 1 = 0 ↔ x >>> 3 = 0 := by decide

end Theory.GroupTheory.TransvectionFive.UniquenessLinear.PlaneTensor
