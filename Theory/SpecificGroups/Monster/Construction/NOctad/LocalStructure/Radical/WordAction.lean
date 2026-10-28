module
public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Radical.Actors

/-!
# Signed action of collected even cocode words

The only hypotheses are the three signed-vector generator laws of 29.12.
Multiplication in the existing representation gives the action of the literal
`normalForm` word, in left-composition order. Equality of signed vectors
then detects both the scalar sign and the subset modulo complement. The
same computation proves block stability and is applied to the published
`blockRepresentation`.

Source: Aschbacher, *Sporadic Groups*, 29.12 and the first part of 29.13(4),
printed pp. 160–161. No kernel, fixed-space or irreducibility conclusion is
included among the hypotheses.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
open TrialitySpin LocalC.ShortFamilies Atlas.Codes Atlas.Fischer

/-- The three hypotheses are exactly the three signed-vector laws in 29.12. -/
structure GeneratorLaws : Prop where
  standard : ∀ (a : ParkerStandardGroup), a.val parkerOmega = parkerOmega →
    ∀ p : OctadParameters,
      representation ⟨psiAut1N a, psiAut1N_mem_N1 a⟩ (vector p) =
        vector (standardParameters a p)
  first : ∀ (d : ParkerLoop) (p : OctadParameters),
    representation ⟨psi1N d, psi1N_mem_N1 d⟩ (vector p) = vector (psi1Parameters d p)
  second : ∀ (e : ParkerLoop) (p : OctadParameters),
    representation ⟨psi2N e, psi2N_mem_N1 e⟩ (vector p) = vector (psi2Parameters e p)

theorem standardParameters_cocode (a : Cocode) (p : OctadParameters) :
    standardParameters (parkerCocodeStandard a) p = p.sign (cocodePairing p.c.1 a) := by
  apply parameters_ext
  · rfl
  · change coordinatePermutation (parkerStandardProjection (parkerCocodeStandard a)).val p.J = p.J
    rw [parkerCocodeStandard_projection]
    rfl

/-- The sign of a collected radical word on a source vector. -/
def wordSign (d e : ParkerLoop) (a : Cocode) (p : OctadParameters) : ParkerBit :=
  binaryDot p.J d.1.val + golayHalfOverlap p.c.1 d.1 +
    golayHalfOverlap e.1 p.c.1 + cocodePairing p.c.1 a

def wordParameters (d e : ParkerLoop) (a : Cocode) (p : OctadParameters) : OctadParameters :=
  standardParameters (parkerCocodeStandard a) (psi2Parameters e (psi1Parameters d p))

theorem wordParameters_code (d e : ParkerLoop) (a : Cocode) (p : OctadParameters) :
    (wordParameters d e a p).c = parkerSign (wordSign d e a p) p.c := by
  rw [wordParameters, standardParameters_cocode]
  change parkerSign _ (parkerSign _ (parkerSign _ p.c)) = _
  rw [parkerSign_add, parkerSign_add]
  apply congrArg (fun t => parkerSign t p.c)
  change cocodePairing p.c.1 a + golayHalfOverlap e.1 p.c.1 +
    (binaryDot p.J d.1.val + golayHalfOverlap p.c.1 d.1) = _
  unfold wordSign
  abel

theorem wordParameters_subset (d e : ParkerLoop) (a : Cocode) (p : OctadParameters) :
    (wordParameters d e a p).J = p.J + p.c.1.val * e.1.val := by
  rw [wordParameters, standardParameters_cocode]
  rfl

theorem normalForm_vector (h : GeneratorLaws) (d e : ParkerLoop) (a : Cocode)
    (ha : EvenCocode a) (p : OctadParameters) :
    representation (normalForm d e (parkerCocodeStandard a)) (vector p) =
      vector (wordParameters d e a p) := by
  have hn : normalForm d e (parkerCocodeStandard a) =
      (⟨psiAut1N (parkerCocodeStandard a), psiAut1N_mem_N1 _⟩ : N1) *
      ⟨psi2N e, psi2N_mem_N1 e⟩ * ⟨psi1N d, psi1N_mem_N1 d⟩ := rfl
  rw [hn, map_mul, map_mul]
  change representation ⟨psiAut1N (parkerCocodeStandard a), psiAut1N_mem_N1 _⟩
    (representation ⟨psi2N e, psi2N_mem_N1 e⟩
      (representation ⟨psi1N d, psi1N_mem_N1 d⟩ (vector p))) = _
  rw [h.first, h.second, h.standard _ ((evenCocode_iff a).mp ha)]
  rfl

/-- The complement relation and the central sign are both necessary. -/
theorem normalForm_vector_fixed_iff (h : GeneratorLaws) (d e : ParkerLoop) (a : Cocode)
    (ha : EvenCocode a) (p : OctadParameters) :
    representation (normalForm d e (parkerCocodeStandard a)) (vector p) = vector p ↔
      wordSign d e a p = 0 ∧
        (p.c.1.val * e.1.val = 0 ∨ p.c.1.val * e.1.val = p.c.1.val) := by
  rw [normalForm_vector h d e a ha, vector_eq_iff, wordParameters_code, wordParameters_subset]
  have hs (t : ParkerBit) : parkerSign t p.c = p.c ↔ t = 0 := by
    constructor
    · intro hh
      exact add_eq_left.mp (congrArg Prod.snd hh)
    · intro ht
      rw [ht, parkerSign_zero]
  rw [hs]
  simp only [add_eq_left, add_right_inj]

/-- A collected even cocode word preserves each actual octad block. -/
theorem normalForm_mem_blockStabilizer (h : GeneratorLaws) (d e : ParkerLoop)
    (a : Cocode) (ha : EvenCocode a) (c : Octad) :
    normalForm d e (parkerCocodeStandard a) ∈ blockStabilizer c := by
  let g := normalForm d e (parkerCocodeStandard a)
  let p := parameters c 0 0
  obtain ⟨q, hq, hqc⟩ := representation_vector_transport g p
  have he : vector q = vector (wordParameters d e a p) :=
    hq.symm.trans (normalForm_vector h d e a ha p)
  have hc : parameterOctad q = c := by
    apply Subtype.ext
    have hh := congrArg Prod.fst ((vector_eq_iff q _).mp he).1
    rw [wordParameters_code] at hh
    exact hh
  change octadTransport g c = c
  exact hqc.symm.trans hc

/-- The published block action on the same literal collected word. -/
theorem blockRepresentation_normalForm_vector (h : GeneratorLaws) (d e : ParkerLoop)
    (a : Cocode) (ha : EvenCocode a) (c : Octad) (p : OctadParameters)
    (hp : p.c.1 = c.val) :
    (blockRepresentation c
      ⟨normalForm d e (parkerCocodeStandard a), normalForm_mem_blockStabilizer h d e a ha c⟩
      ⟨vector p, Submodule.subset_span ⟨p, hp, rfl⟩⟩).val =
        vector (wordParameters d e a p) := normalForm_vector h d e a ha p

end Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
