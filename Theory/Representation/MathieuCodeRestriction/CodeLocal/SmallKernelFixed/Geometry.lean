module

public import Theory.Representation.MathieuCodeRestriction.CodeLocal.FixedLift
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.BinaryOffender.CommutatorRank
import all Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.BinaryKernel.Translations
import all Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.BinaryKernel
/-!
# Binary coordinates for the native octad kernel

The existing heptad translations, extended along the actual M23 embedding,
exhaust the pointwise stabilizer of the seed octad. Their complementary
coordinates identify the permutation action with addition on four binary
digits. The native 4096 messages enumerate the Golay subspace bijectively.
These comparisons support finite fixed-word counts without changing models.
The internal translation imports are intentional: only this comparison proof
inspects the existing coordinate table and the binary-equivalence implementation.

Source: Aschbacher--Smith, H.16.2 and H.16.8, printed pp.402--405;
native translations from `HeptadStructure.BinaryKernel`.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M23Geometry
open Sporadic.Mathieu.M24LocalGeometry Sporadic.Mathieu.M24LocalGeometry.LinearFourCore
open Representation.BinaryOffender
namespace MathieuCode.SmallKernelFixed
noncomputable section

def decode (n : Fin 16) : Fin 4 → ZMod 2 := fun i => if n.val.testBit i.val then 1 else 0
def xorIndex (n j : Fin 16) : Fin 16 :=
  (BitVec.ofFin (w := 4) n ^^^ BitVec.ofFin (w := 4) j).toFin

theorem decode_bijective : Function.Bijective decode := by decide +kernel

theorem decode_xor (n j : Fin 16) : decode (xorIndex n j) = decode n + decode j := by
  revert n j
  decide +kernel

def coordinate : Fin 16 → Fin 24 := ![23,6,7,8,9,10,18,12,13,15,19,22,20,21,16,14]

theorem coordinate_eq (j : Fin 16) :
    coordinate j = m23PointEmbedding (heptadBinaryPoint (decode j)) := by
  revert j
  decide +kernel

theorem coordinate_cover (i : Fin 24) : i ∈ seedOctad.val ∨ ∃ j, coordinate j = i := by
  simp only [mem_seedOctad]
  revert i
  decide +kernel

def translation (n : Fin 16) : M24 :=
  (kernelLift (heptadBinaryEquiv (Multiplicative.ofAdd (decode n)))).val.val

theorem translation_mem (n : Fin 16) : translation n ∈ octadPointwiseKernel seedOctad :=
  Subgroup.mem_map_of_mem _ (kernelLift _).property

theorem translation_zero : translation 0 = 1 := by
  have h : decode 0 = 0 := by decide +kernel
  simp [translation, h]

theorem translation_injective : Function.Injective translation := by
  intro n m h
  apply decode_bijective.1
  apply Multiplicative.ofAdd.injective
  apply heptadBinaryEquiv.injective
  apply kernelLift_bijective.1
  exact Subtype.ext (Subtype.ext h)

theorem translation_surjective (g : M24) (hg : g ∈ octadPointwiseKernel seedOctad) :
    ∃ n, translation n = g := by
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨b, hb⟩ := kernelLift_bijective.2 ⟨a, ha⟩
  obtain ⟨v, rfl⟩ := heptadBinaryEquiv.surjective b
  obtain ⟨n, hn⟩ := decode_bijective.2 v.toAdd
  refine ⟨n, ?_⟩
  unfold translation
  rw [hn]
  exact congrArg (fun k : (action seedOctad).ker => k.val.val) hb

theorem translation_coordinate (n j : Fin 16) :
    translation n • coordinate j = coordinate (xorIndex n j) := by
  change (kernelLift _).val.val.val (coordinate j) = _
  rw [kernelLift_coe, heptadLift_coe, coordinate_eq, m23ExtendHom_apply_embedded]
  change m23PointEmbedding (heptadBinaryPermutation (decode n) (heptadBinaryPoint (decode j))) = _
  rw [heptadBinaryPermutation_translate, ← decode_xor, ← coordinate_eq]

def golayWord (u : Fin 4096) : golay := ⟨wordOfMask (m24GolayCode u), wordOfMask_code_mem u⟩

theorem golayWord_bijective : Function.Bijective golayWord := by
  constructor
  · intro u t h
    apply m24GolayWord_injective
    apply Finset.ext
    intro i
    have he := congrArg (fun v : golay => v.val i) h
    change wordOfMask (m24GolayCode u) i = wordOfMask (m24GolayCode t) i at he
    rw [← wordOfSet_golayWord, ← wordOfSet_golayWord] at he
    by_cases hu : i ∈ m24GolayWord u <;> by_cases ht : i ∈ m24GolayWord t <;>
      simp_all [wordOfSet]
  · intro v
    obtain ⟨u, hu⟩ := golay_exists_word v.property
    exact ⟨u, Subtype.ext hu.symm⟩

def golayWordEquiv : Fin 4096 ≃ golay := Equiv.ofBijective golayWord golayWord_bijective

theorem golay_fixed_iff_forward (g : M24) (v : golay) :
    golayRepresentation g v = v ↔ ∀ i, v.val (g • i) = v.val i := by
  constructor
  · intro h i
    have he := congrArg (fun w : golay => w.val (g • i)) h
    change v.val (g⁻¹ • (g • i)) = v.val (g • i) at he
    simpa only [inv_smul_smul] using he.symm
  · intro h
    apply Subtype.ext
    funext i
    change v.val (g⁻¹ • i) = v.val i
    simpa only [smul_inv_smul] using (h (g⁻¹ • i)).symm

theorem translation_fixed_iff (n : Fin 16) (v : golay) :
    golayRepresentation (translation n) v = v ↔
      ∀ j, v.val (coordinate (xorIndex n j)) = v.val (coordinate j) := by
  rw [golay_fixed_iff_forward]
  constructor
  · intro h j
    simpa only [translation_coordinate] using h (coordinate j)
  · intro h i
    rcases coordinate_cover i with hi | ⟨j, rfl⟩
    · rw [(mem_octadPointwiseKernel _ _).mp (translation_mem n) i hi]
    · simpa only [translation_coordinate] using h j
end
end MathieuCode.SmallKernelFixed
