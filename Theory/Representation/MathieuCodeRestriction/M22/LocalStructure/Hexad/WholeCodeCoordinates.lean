module
public import Theory.Representation.MathieuCodeRestriction.M22
public import Theory.Mathieu.M22.Properties.HexadSplitCoordinates.Coordinates

/-!
# Whole-code coordinates for an arbitrary native M22 hexad

The stabilizer equivalence uses a fixed inverse native conjugator. Apply the
same representation operator to the entire ten-dimensional code: this
intertwines the literal actions and carries the actual hexad vector to the
source vector. Composition retains the full kernel of any original actor
map, so it can feed point-residual and commutator calculations unchanged.

Source: Aschbacher--Smith H.16.4 and 8.2.11, printed pp.403,722.
-/

@[expose] public noncomputable section
open Sporadic.Mathieu
open scoped Pointwise
namespace MathieuCode.Hexad.WholeCodeCoordinates
open M22HexadCoordinates

/-- The whole-code marking uses the same inverse conjugator as the stabilizer marking. -/
def codeEquiv {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    M22Code ≃ₗ[ZMod 2] M22Code :=
  m22CodeConjugationEquiv (Classical.choose (exists_base_conjugator hB))⁻¹

theorem codeEquiv_equivariant {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : MulAction.stabilizer M22 B) (v : M22Code) :
    codeEquiv hB (m22CodeRepresentation g.val v) =
      m22CodeRepresentation (stabilizerEquiv hB g).val (codeEquiv hB v) := by
  rw [stabilizerEquiv_coe]
  exact m22CodeConjugationEquiv_intertwines _ _ _

private theorem hexadVector_smul {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : M22) :
    m22CodeRepresentation g (m22HexadVector hB) =
      m22HexadVector (m22_smul_block_mem g B hB) := by
  apply Subtype.ext
  change codeRepresentation (m22Embedding g) (octadVector (m22Octad hB)) = _
  rw [octadVector, codeRepresentation_mk]
  apply congrArg codeLine.mkQ
  apply Subtype.ext
  change BinaryPermutation.representation (Fin 24) (m22Embedding g).val
    (wordOfSet (m22AugmentedOctad B)) = wordOfSet (m22AugmentedOctad (g • B))
  rw [permute_wordOfSet, m22AugmentedOctad_smul]
  rfl

/-- The literal chosen point is carried to the native source hexad vector. -/
theorem codeEquiv_point {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    codeEquiv hB (m22HexadVector hB) = m22HexadVector m22Hexad24Ten_mem := by
  let g := Classical.choose (exists_base_conjugator hB)
  have hg : g⁻¹ • B = base := by
    rw [← Classical.choose_spec (exists_base_conjugator hB), inv_smul_smul]
  change m22CodeRepresentation g⁻¹ (m22HexadVector hB) = _
  rw [hexadVector_smul]
  generalize_proofs h
  congr 1

variable {R V : Type*} [Group R] [AddCommGroup V] [Module (ZMod 2) V]

/-- Preserve the complete original homomorphism while changing hexad coordinates. -/
def actorMap {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (f : R →* MulAction.stabilizer M22 B) : R →* M22ChapterH.Hexad.Action.Inner :=
  (stabilizerEquiv hB).toMonoidHom.comp f

theorem actorMap_surjective {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (f : R →* MulAction.stabilizer M22 B) (hf : Function.Surjective f) :
    Function.Surjective (actorMap hB f) := (stabilizerEquiv hB).surjective.comp hf

theorem actorMap_ker {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (f : R →* MulAction.stabilizer M22 B) : (actorMap hB f).ker = f.ker :=
  MonoidHom.ker_comp_of_injective _ _ (stabilizerEquiv hB).injective

/-- Whole original module coordinates and the full actor map change together. -/
theorem original_equivariant {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (ρ : Representation (ZMod 2) R V) (f : R →* MulAction.stabilizer M22 B)
    (e : V ≃ₗ[ZMod 2] M22Code)
    (he : ∀ r v, e (ρ r v) = m22CodeRepresentation (f r).val (e v)) (r : R) (v : V) :
    (e.trans (codeEquiv hB)) (ρ r v) =
      m22CodeRepresentation (actorMap hB f r).val ((e.trans (codeEquiv hB)) v) :=
  (congrArg (codeEquiv hB) (he r v)).trans (codeEquiv_equivariant hB (f r) (e v))

end MathieuCode.Hexad.WholeCodeCoordinates
