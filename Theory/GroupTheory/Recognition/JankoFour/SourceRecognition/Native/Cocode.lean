module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Transport.Coordinates
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal
public import Theory.Representation.ElementaryAbelianAction
import all Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Transport.Coordinates

/-!
# The literal native J4 kernel as the Mathieu cocode

The certified 24-star labels define an eleven-coordinate syndrome on the
native even permutation space. Each of the twelve native Golay rows has
zero syndrome, and the eleven marked pairs map to a basis. This gives a
linear equivalence from the actual cocode to the literal max1 kernel.
The existing pair-label compatibility then proves equivariance for actual
left conjugation, retaining the original star relabeling and M24 quotient.

The internal import of Transport.Coordinates reuses its proved pair-label
compatibility; no private data appears in the exported statements. Native
normalizer applications use this bridge to supply the module input to
AS91 (4.8)--(4.9), rather than inferring an action from the extension order.

Source: Aschbacher--Segev, The uniqueness of groups of type J4, Invent.
Math. 105 (1991), (4.8), pp.598--599, DOI 10.1007/BF01232280.
The literal ATLAS J4G1-max1W1 words, masks and star relabeling retain the
attribution documented in the imported native certificate modules.
-/

public section
open scoped BigOperators IsMulCommutative
open Janko4.Cardinality.QuotientCount.Image
open Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate
open MathieuCode
set_option backward.isDefEq.respectTransparency true
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeCocode
private abbrev V := Fin 11 → ZMod 2
private theorem binary_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
private theorem binary_bool (b : Bool) : decide ((if b then (1 : ZMod 2) else 0) = 1) = b := by cases b <;> decide

private def label (i j : Fin 24) : V := fun k => if (pairLabel i j).testBit k.val then 1 else 0

private def syndrome : Full →ₗ[ZMod 2] V where
  toFun v := ∑ i : Fin 24, v (relabel i) • label i 0
  map_add' v w := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, mul_smul]

set_option maxRecDepth 4096 in
private theorem syndrome_row : ∀ i : Fin 12, syndrome (row i) = 0 := by
  intro i
  fin_cases i <;> (ext k; revert k; decide +kernel)

set_option maxRecDepth 4096 in
private theorem label_sum : ∀ i j : Fin 24, label i 0 + label j 0 = label i j := by
  intro i
  fin_cases i <;> (intro j; ext k; revert j k; decide +kernel)

set_option maxRecDepth 4096 in
private theorem label_basis : ∀ i : Fin 11,
    label (basisPair i).1 (basisPair i).2 = Pi.single i 1 := by
  decide +kernel

private def pairWord (i j : Fin 24) : Core :=
  ⟨Pi.single (relabel i) 1 + Pi.single (relabel j) 1, by
    simp [BinaryPermutation.mem_core, Finset.sum_add_distrib]⟩

private theorem syndrome_single (i : Fin 24) :
    syndrome (Pi.single (relabel i) 1) = label i 0 := by
  simp [syndrome, Pi.single_apply, relabel.injective.eq_iff]

private theorem syndrome_pair (i j : Fin 24) :
    syndrome (pairWord i j).val = label i j := by
  change syndrome (Pi.single (relabel i) 1 + Pi.single (relabel j) 1) = _
  rw [map_add, syndrome_single, syndrome_single, label_sum]

private theorem golay_le_ker : golay ≤ syndrome.ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact syndrome_row i

private noncomputable def cocodeSyndrome : Cocode →ₗ[ZMod 2] V :=
  codeInCore.liftQ (syndrome.comp Core.subtype) (fun _ hv => golay_le_ker hv)

private theorem cocodeSyndrome_pair (i j : Fin 24) :
    cocodeSyndrome (codeInCore.mkQ (pairWord i j)) = label i j := syndrome_pair i j

private theorem cocodeSyndrome_surjective : Function.Surjective cocodeSyndrome := by
  intro v
  refine ⟨∑ i, v i • codeInCore.mkQ (pairWord (basisPair i).1 (basisPair i).2), ?_⟩
  simp only [map_sum, map_smul, cocodeSyndrome_pair, label_basis]
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

private noncomputable def cocodeCoordinates : Cocode ≃ₗ[ZMod 2] V :=
  LinearEquiv.ofBijective cocodeSyndrome
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [finrank_cocode]; simp [V])).mpr cocodeSyndrome_surjective,
      cocodeSyndrome_surjective⟩

open Janko4 Janko4.Cardinality Janko4.Cardinality.QuotientCount
open Janko4.LocalStructure.SylowCore.Transport
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
local instance : IsElementaryAbelian 2 (localKernel hA hB) :=
  Janko4.LocalStructure.localKernel_elementary hA hB

private def evaluate : V →ₗ[ZMod 2] Additive (localKernel hA hB) :=
  ({ toFun v := Additive.ofMul (coordinates hA hB (fun i => decide (v i = 1)))
     map_zero' := by
       apply Additive.toMul.injective
       apply Subtype.ext
       simp [coordinates_val, KernelCount.binaryProduct_zero]
     map_add' v w := by
       apply Additive.toMul.injective
       rw [show (Additive.ofMul (coordinates hA hB (fun i => decide (v i = 1))) +
         Additive.ofMul (coordinates hA hB (fun i => decide (w i = 1)))).toMul =
         coordinates hA hB (fun i => decide (v i = 1)) *
         coordinates hA hB (fun i => decide (w i = 1)) from rfl, coordinates_mul]
       change coordinates hA hB _ = coordinates hA hB _
       congr 1
       funext i
       have hv : v i = 0 ∨ v i = 1 := by simpa using binary_cases (v i)
       have hw : w i = 0 ∨ w i = 1 := by simpa using binary_cases (w i)
       rcases hv with hv | hv <;> rcases hw with hw | hw <;> simp [Pi.add_apply,hv,hw]
    } : V →+ Additive (localKernel hA hB)).toZModLinearMap 2

private theorem evaluate_bijective : Function.Bijective (evaluate hA hB) := by
  constructor
  · intro v w he
    have hh := coordinates_injective hA hB (congrArg Additive.toMul he)
    funext i
    have hi := congrFun hh i
    have hv : v i = 0 ∨ v i = 1 := binary_cases (v i)
    have hw : w i = 0 ∨ w i = 1 := binary_cases (w i)
    rcases hv with hv | hv <;> rcases hw with hw | hw <;> simp_all
  · intro w
    obtain ⟨v,hv⟩ := coordinates_surjective hA hB w.toMul
    refine ⟨fun i => if v i then 1 else 0, ?_⟩
    apply Additive.toMul.injective
    change coordinates hA hB _ = w.toMul
    rw [←hv]
    congr 1
    funext i
    exact binary_bool (v i)

noncomputable def cocodeEquiv : Cocode ≃ₗ[ZMod 2] Additive (localKernel hA hB) :=
  cocodeCoordinates.trans (LinearEquiv.ofBijective (evaluate hA hB) (evaluate_bijective hA hB))

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeCocode

namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeCocode
open Janko4 Janko4.Cardinality Janko4.Cardinality.QuotientCount
open Janko4.LocalStructure.SylowCore.Transport
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
local instance : IsElementaryAbelian 2 (localKernel hA hB) :=
  Janko4.LocalStructure.localKernel_elementary hA hB

private theorem evaluate_label (i j : Fin 24) :
    (evaluate hA hB (label i j)).toMul =
      coordinates hA hB (fun k => (pairLabel i j).testBit k.val) := by
  change coordinates hA hB _ = _
  congr 1
  funext k
  exact binary_bool ((pairLabel i j).testBit k.val)

private theorem cocodeEquiv_pair (i j : Fin 24) :
    (cocodeEquiv hA hB (codeInCore.mkQ (pairWord i j))).toMul =
      coordinates hA hB (fun k => (pairLabel i j).testBit k.val) := by
  change (evaluate hA hB (cocodeSyndrome (codeInCore.mkQ (pairWord i j)))).toMul = _
  rw [cocodeSyndrome_pair, evaluate_label]

private theorem pairWord_expansion (v : Core) :
    v = ∑ i : Fin 24, v.val (relabel i) • pairWord i 0 := by
  have hv : (∑ i : Fin 24, v.val (relabel i)) = 0 :=
    (Equiv.sum_comp relabel v.val).trans v.property
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pairWord, Pi.add_apply, mul_add, Finset.sum_add_distrib, ←Finset.sum_mul,hv,zero_mul,add_zero]
  simp [Pi.single_apply, ←relabel.symm_apply_eq, eq_comm]

private theorem permute_single (g : Equiv.Perm (Fin 24)) (i : Fin 24) :
    BinaryPermutation.representation (Fin 24) g (Pi.single i 1) = Pi.single (g i) 1 := by
  ext j
  simp [Pi.single_apply, Equiv.symm_apply_eq]

private theorem native_pairWord (s : StarGroup) (i j : Fin 24) :
    coreRepresentation (starGroupEquivM24 s) (pairWord i j) =
      pairWord (s.val i) (s.val j) := by
  apply Subtype.ext
  change BinaryPermutation.representation (Fin 24) (starGroupEquivM24 s).val
    (Pi.single (relabel i) 1 + Pi.single (relabel j) 1) = _
  rw [map_add,permute_single,permute_single,starGroupEquivM24_apply]
  change Pi.single (relabel (s.val (relabel.symm (relabel i)))) 1 +
    Pi.single (relabel (s.val (relabel.symm (relabel j)))) 1 = _
  rw [relabel.symm_apply_apply, relabel.symm_apply_apply]
  rfl

/-- The quotient uses the original local-kernel quotient and the certified star relabeling. -/
@[expose] noncomputable def projection : max1Subgroup hA hB →* Sporadic.Mathieu.M24 :=
  starGroupEquivM24.toMonoidHom.comp (starProjection hA hB)

private theorem linear_ext_pairs {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    (f g : Cocode →ₗ[ZMod 2] A)
    (he : ∀ i j, f (codeInCore.mkQ (pairWord i j)) = g (codeInCore.mkQ (pairWord i j))) : f = g := by
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := codeInCore.mkQ_surjective v
  rw [pairWord_expansion w]
  simp only [map_sum,map_smul,he]

/-- The native cocode coordinates intertwine actual left conjugation with the
same marked M24 quotient. -/
theorem cocodeEquiv_equivariant (g : max1Subgroup hA hB) (v : Cocode) :
    cocodeEquiv hA hB (cocodeRepresentation (projection hA hB g) v) =
      Additive.ofMul (MulAut.conjNormal g (cocodeEquiv hA hB v).toMul) := by
  let act : Additive (localKernel hA hB) →ₗ[ZMod 2] Additive (localKernel hA hB) :=
    ((MulAut.conjNormal g : MulAut (localKernel hA hB)).toMonoidHom.toAdditive).toZModLinearMap 2
  have he := linear_ext_pairs
    ((cocodeEquiv hA hB).toLinearMap.comp (cocodeRepresentation (projection hA hB g)))
    (act.comp (cocodeEquiv hA hB).toLinearMap) (fun i j => by
      change cocodeEquiv hA hB (cocodeRepresentation (projection hA hB g)
        (codeInCore.mkQ (pairWord i j))) = act (cocodeEquiv hA hB (codeInCore.mkQ (pairWord i j)))
      rw [cocodeRepresentation_mk]
      change cocodeEquiv hA hB (codeInCore.mkQ
        (coreRepresentation (starGroupEquivM24 (starProjection hA hB g)) (pairWord i j))) = _
      rw [native_pairWord]
      apply Additive.toMul.injective
      rw [cocodeEquiv_pair]
      change _ = MulAut.conjNormal g _
      rw [cocodeEquiv_pair]
      exact (Janko4.LocalStructure.SylowCore.Transport.compatible hA hB g i j).symm)
  exact LinearMap.congr_fun he v

/-- The original first kernel basis element is the native pair class {1,14}. -/
theorem cocodeEquiv_seed :
    ((cocodeEquiv hA hB (pairVector ⟨{1,14},by decide⟩)).toMul : max1Subgroup hA hB) =
      localKernelSeed hA hB := by
  have hp : pairVector ⟨{1,14},by decide⟩ = codeInCore.mkQ (pairWord 0 1) := by
    unfold pairVector
    apply congrArg codeInCore.mkQ
    apply Subtype.ext
    funext i
    revert i
    decide +kernel
  rw [hp,cocodeEquiv_pair,coordinates_val]
  have hb : (fun k : Fin 11 => (pairLabel 0 1).testBit k.val) = (fun k => k == 0) := by
    decide +kernel
  rw [hb]
  change KernelCount.binaryProduct (KernelCount.basis hA hB)
    (fun k => decide (k = 0)) = _
  rw [KernelCount.binaryProduct_single]
  rfl

/-- Surjectivity retains the previously certified full M24 quotient. -/
theorem projection_surjective : Function.Surjective (projection hA hB) :=
  starGroupEquivM24.surjective.comp (starProjection_surjective hA hB)

/-- Its kernel is exactly the literal order-2048 native subgroup. -/
theorem projection_ker : (projection hA hB).ker = localKernel hA hB := by
  rw [projection,MonoidHom.ker_comp_of_injective _ _ starGroupEquivM24.injective,
    starProjection_ker]

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeCocode
