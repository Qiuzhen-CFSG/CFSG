module

public import Theory.Representation.MathieuCodeRestriction.M22.Construction
public import Theory.Representation.MathieuCodeRestriction.Orthogonality


/-!
# The literal ten-dimensional M22 cocode and pair-stabilizer actions

The distinguished native coordinates are 0 and 9. Their binary pair word has
nonzero class in the eleven-dimensional cocode: its dot product with a certified
Golay row is 1, whereas the Golay space is self-orthogonal. Quotienting by this
line therefore gives dimension ten. The setwise stabilizer preserves both the
pair line and the existing code hyperplane, so acts on these exact carriers.
Its pointwise pair subgroup is precisely the image of the existing native M22
embedding. These are actual permutation actions; identification of the full
setwise stabilizer with `MulAut M22` is a further theorem obligation.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), H.13.1,
printed p.395 (PDF p.406). Both pair fixation conventions are kept explicit.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu
open scoped BigOperators Pointwise
namespace MathieuCode

/-- The distinguished pair in the native coordinate system. -/
def m22Pair : Finset (Fin 24) := {0, 9}

/-- The binary vector supported on the distinguished pair. -/
def m22PairWord : Full := Pi.single 0 1 + Pi.single 9 1

theorem m22PairWord_eq_wordOfSet : m22PairWord = wordOfSet m22Pair := by
  ext i
  fin_cases i <;> decide +kernel

theorem dotForm_m22PairWord (v : Full) : dotForm v m22PairWord = v 0 + v 9 := by
  simp [m22PairWord, dotForm, dotProductBilin, dotProduct_single]

theorem m22PairWord_mem_core : m22PairWord ∈ Core := by
  change (∑ i, m22PairWord i) = 0
  decide +kernel

/-- The actual class of the pair in the eleven-dimensional cocode. -/
def m22PairClass : Cocode := codeInCore.mkQ ⟨m22PairWord, m22PairWord_mem_core⟩

theorem m22PairClass_ne_zero : m22PairClass ≠ 0 := by
  intro hz
  have hc : m22PairWord ∈ golay := (Submodule.Quotient.mk_eq_zero codeInCore).mp hz
  have h := golay_le_orthogonal hc (row 0) (row_mem 0)
  rw [dotForm_m22PairWord] at h
  have hr : row 0 0 + row 0 9 = 1 := by decide +kernel
  rw [hr] at h
  exact one_ne_zero h

/-- The line removed in H.13.1, inside the actual eleven-dimensional cocode. -/
def m22PairLine : Submodule (ZMod 2) Cocode := Submodule.span (ZMod 2) {m22PairClass}

abbrev M22Cocode := Cocode ⧸ m22PairLine

theorem finrank_m22PairLine : Module.finrank (ZMod 2) m22PairLine = 1 := by
  exact finrank_span_singleton m22PairClass_ne_zero

theorem finrank_m22Cocode : Module.finrank (ZMod 2) M22Cocode = 10 := by
  have h := m22PairLine.finrank_quotient_add_finrank
  rw [finrank_m22PairLine, finrank_cocode] at h
  change Module.finrank (ZMod 2) M22Cocode + 1 = 11 at h
  omega

/-- This fixes the pair setwise, allowing its two coordinates to be exchanged. -/
def m22PairStabilizer : Subgroup M24 := MulAction.stabilizer M24 m22Pair

/-- The pointwise pair stabilizer, which is the image of the native M22. -/
def m22PointwisePairStabilizer : Subgroup M24 :=
  MulAction.stabilizer M24 (0 : Fin 24) ⊓ MulAction.stabilizer M24 (9 : Fin 24)

theorem m22Embedding_range : m22Embedding.range = m22PointwisePairStabilizer := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨m22Embedding_fixed_zero u, m22Embedding_fixed_nine u⟩
  · rintro ⟨h0, h9⟩
    rw [← pointEmbedding_range] at h0
    obtain ⟨u, rfl⟩ := h0
    have hu : u ∈ MulAction.stabilizer M23 (9 : Fin 23) := by
      apply m23PointEmbedding.injective
      change m23PointEmbedding (u.val 9) = m23PointEmbedding 9
      rw [← pointEmbedding_apply]
      have he : m23PointEmbedding 9 = (9 : Fin 24) := by decide +kernel
      rw [he]
      exact h9
    refine ⟨m23EquivM22PointStabilizer.symm ⟨u, hu⟩, ?_⟩
    have hv : m22InM23 (m23EquivM22PointStabilizer.symm ⟨u, hu⟩) = u :=
      congrArg (fun k : MulAction.stabilizer M23 (9 : Fin 23) => (k : M23))
        (m23EquivM22PointStabilizer.apply_symm_apply ⟨u, hu⟩)
    exact congrArg pointEmbedding hv

theorem m22PointwisePairStabilizer_le : m22PointwisePairStabilizer ≤ m22PairStabilizer := by
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro i hi
  have hi' : i = 0 ∨ i = 9 := by simpa [m22Pair] using hi
  rcases hi' with rfl | rfl
  · rwa [show g • (0 : Fin 24) = 0 from hg.1]
  · rwa [show g • (9 : Fin 24) = 9 from hg.2]

/-- The marked inclusion of the native M22 in the setwise stabilizer. -/
def m22ToPairStabilizer : M22 →* m22PairStabilizer :=
  m22Embedding.codRestrict m22PairStabilizer (fun g =>
    m22PointwisePairStabilizer_le ⟨m22Embedding_fixed_zero g, m22Embedding_fixed_nine g⟩)

@[simp] theorem m22ToPairStabilizer_coe (g : M22) :
    (m22ToPairStabilizer g).val = m22Embedding g := rfl

theorem m22PairWord_invariant (g : m22PairStabilizer) :
    fullRepresentation g.val m22PairWord = m22PairWord := by
  rw [m22PairWord_eq_wordOfSet]
  change BinaryPermutation.representation (Fin 24) g.val.val _ = _
  rw [permute_wordOfSet]
  exact congrArg wordOfSet (MulAction.mem_stabilizer_iff.mp g.property)

theorem m22PairClass_invariant (g : m22PairStabilizer) :
    cocodeRepresentation g.val m22PairClass = m22PairClass := by
  unfold m22PairClass
  rw [cocodeRepresentation_mk]
  congr 1
  exact Subtype.ext (m22PairWord_invariant g)

theorem pairFunctional_invariant_setwise (g : m22PairStabilizer) (v : Code) :
    pairFunctional (codeRepresentation g.val v) = pairFunctional v := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change pairFunctional (codeRepresentation g.val (codeLine.mkQ v)) =
      pairFunctional (codeLine.mkQ v)
    rw [codeRepresentation_mk, pairFunctional_mk, pairFunctional_mk]
    change (fullRepresentation g.val v.val) 0 + (fullRepresentation g.val v.val) 9 = _
    rw [← dotForm_m22PairWord, ← dotForm_m22PairWord]
    calc
      dotForm (fullRepresentation g.val v.val) m22PairWord =
          dotForm (fullRepresentation g.val v.val) (fullRepresentation g.val m22PairWord) :=
        congrArg (dotForm (fullRepresentation g.val v.val)) (m22PairWord_invariant g).symm
      _ = dotForm v.val m22PairWord := dotForm_invariant g.val v.val m22PairWord

/-- The code hyperplane is invariant under the actual setwise pair stabilizer. -/
def m22OuterCodeSubrepresentation :
    Subrepresentation (codeRepresentation.comp m22PairStabilizer.subtype) where
  toSubmodule := m22Hyperplane
  apply_mem_toSubmodule g v hv := by
    change pairFunctional (codeRepresentation g.val v) = 0
    rw [pairFunctional_invariant_setwise]
    exact hv

def m22OuterCodeRepresentation : Representation (ZMod 2) m22PairStabilizer M22Code :=
  m22OuterCodeSubrepresentation.toRepresentation

/-- The fixed pair line is an invariant subrepresentation, not an abstract copy. -/
def m22PairLineSubrepresentation :
    Subrepresentation (cocodeRepresentation.comp m22PairStabilizer.subtype) where
  toSubmodule := m22PairLine
  apply_mem_toSubmodule g v hv := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    change cocodeRepresentation g.val (c • m22PairClass) ∈ m22PairLine
    rw [map_smul, m22PairClass_invariant]
    exact m22PairLine.smul_mem c (Submodule.subset_span (Set.mem_singleton _))

/-- The literal quotient action of the setwise pair stabilizer. -/
def m22OuterCocodeRepresentation : Representation (ZMod 2) m22PairStabilizer M22Cocode :=
  m22PairLineSubrepresentation.quotientRepresentation

def m22CocodeRepresentation : Representation (ZMod 2) M22 M22Cocode :=
  m22OuterCocodeRepresentation.comp m22ToPairStabilizer

@[simp] theorem m22OuterCodeRepresentation_restrict (g : M22) (v : M22Code) :
    m22OuterCodeRepresentation (m22ToPairStabilizer g) v = m22CodeRepresentation g v := rfl

@[simp] theorem m22OuterCocodeRepresentation_mk (g : m22PairStabilizer) (v : Cocode) :
    m22OuterCocodeRepresentation g (m22PairLine.mkQ v) =
      m22PairLine.mkQ (cocodeRepresentation g.val v) := rfl

@[simp] theorem m22CocodeRepresentation_mk (g : M22) (v : Cocode) :
    m22CocodeRepresentation g (m22PairLine.mkQ v) =
      m22PairLine.mkQ (cocodeRepresentation (m22Embedding g) v) := rfl

end MathieuCode
