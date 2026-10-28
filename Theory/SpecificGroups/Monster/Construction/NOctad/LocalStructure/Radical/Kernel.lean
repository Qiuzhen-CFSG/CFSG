module

public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Radical.WordAction
public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Radical.Characters

/-!
# The exact block kernel on literal radical words

For a collected word with even cocode, the action on the block is trivial
exactly when both Golay words intersect the octad in the empty or full
subset and the cocode annihilates it. The proof uses the zero-subset vector
to separate the constant sign and all even subsets to detect the first
loop word. It applies directly to the published block action and its
restriction to actual radical elements.

The subgroup `blockActor` is explicitly the radical intersected with the
block stabilizer. Collection of all radical elements and identification
with the source setwise product remain separate group-theoretic obligations.

Source: Aschbacher, *Sporadic Groups*, 29.13(4), printed pp. 160–161.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
open TrialitySpin LocalC.ShortFamilies Atlas.Codes Atlas.Fischer

/-- The exact source intersection and cocode conditions on a collected word. -/
def KernelParameters (c : Octad) (d e : ParkerLoop) (a : Cocode) : Prop :=
  (c.val.val * d.1.val = 0 ∨ c.val.val * d.1.val = c.val.val) ∧
  (c.val.val * e.1.val = 0 ∨ c.val.val * e.1.val = c.val.val) ∧
  cocodePairing c.val a = 0

/-- The relative kernel of the published block representation, evaluated on
actual radical words. Both intersections are modulo the complement class. -/
theorem normalForm_block_kernel_iff (h : GeneratorLaws) (d e : ParkerLoop)
    (a : Cocode) (ha : EvenCocode a) (c : Octad) :
    (⟨normalForm d e (parkerCocodeStandard a),
      normalForm_mem_blockStabilizer h d e a ha c⟩ : blockStabilizer c) ∈
        (blockRepresentation c).ker ↔ KernelParameters c d e a := by
  rw [blockRepresentation_kernel_iff]
  simp_rw [← representation_vector_eq_iff]
  simp_rw [normalForm_vector_fixed_iff h d e a ha]
  constructor
  · intro hf
    have h0 := hf (parameters c 0 0) rfl
    have he : c.val.val * e.1.val = 0 ∨ c.val.val * e.1.val = c.val.val := h0.2
    have hs : golayHalfOverlap c.val d.1 + golayHalfOverlap e.1 c.val +
        cocodePairing c.val a = 0 := by
      simpa [wordSign, parameters, subsetWord_zero] using h0.1
    have hd : c.val.val * d.1.val = 0 ∨ c.val.val * d.1.val = c.val.val := by
      apply (evenSubset_annihilator c d.1.val).mp
      intro J
      have hj := (hf (parameters c J 0) rfl).1
      change binaryDot (subsetWord c J) d.1.val + golayHalfOverlap c.val d.1 +
        golayHalfOverlap e.1 c.val + cocodePairing c.val a = 0 at hj
      rw [add_assoc, add_assoc, ← add_assoc (golayHalfOverlap c.val d.1), hs, add_zero] at hj
      exact hj
    refine ⟨hd, he, ?_⟩
    rw [halfOverlap_eq_zero_of_intersection c d.1 hd,
      golayHalfOverlap_symmetric e.1 c.val,
      halfOverlap_eq_zero_of_intersection c e.1 he, zero_add, zero_add] at hs
    exact hs
  · rintro ⟨hd, he, ha0⟩ p hp
    refine ⟨?_, by simpa only [hp] using he⟩
    have hpc : parameterOctad p = c := Subtype.ext hp
    have hj : binaryDot p.J d.1.val = 0 := by
      rw [← subsetWord_subsetOfParameters p]
      have hd' : (parameterOctad p).val.val * d.1.val = 0 ∨
          (parameterOctad p).val.val * d.1.val = (parameterOctad p).val.val := by
        simpa only [hpc] using hd
      exact (evenSubset_annihilator (parameterOctad p) d.1.val).mpr hd' _
    simp only [wordSign, hj, hp, halfOverlap_eq_zero_of_intersection c d.1 hd,
      golayHalfOverlap_symmetric e.1 c.val, halfOverlap_eq_zero_of_intersection c e.1 he,
      ha0, zero_add]

/-- The actual radical intersected with the published block stabilizer.
The assertion that all of `R` stabilizes the block is a further group theorem. -/
def blockActor (c : Octad) : Subgroup (blockStabilizer c) :=
  (R.subgroupOf N1).comap (blockStabilizer c).subtype

/-- Restriction of the existing block action to the actual radical elements. -/
def blockAction (c : Octad) : Representation ℝ (blockActor c) (block c) :=
  (blockRepresentation c).comp (blockActor c).subtype

/-- The concrete collected radical word in the actual block actor. -/
def wordActor (h : GeneratorLaws) (d e : ParkerLoop) (a : Cocode)
    (ha : EvenCocode a) (c : Octad) : blockActor c :=
  ⟨⟨normalForm d e (parkerCocodeStandard a),
    normalForm_mem_blockStabilizer h d e a ha c⟩, normalForm_mem_R d e a ha⟩

/-- A direct application to the radical restriction of the published action. -/
theorem wordActor_kernel_iff (h : GeneratorLaws) (d e : ParkerLoop)
    (a : Cocode) (ha : EvenCocode a) (c : Octad) :
    wordActor h d e a ha c ∈ (blockAction c).ker ↔ KernelParameters c d e a :=
  normalForm_block_kernel_iff h d e a ha c

/-- The action still intertwines the literal inclusion into the Griess space. -/
theorem blockAction_inclusion (c : Octad) (g : blockActor c) (v : block c) :
    blockInclusion c (blockAction c g v) =
      LocalC.cRepresentation (LocalC.n1ToC g.val.val) (blockInclusion c v) :=
  blockRepresentation_inclusion c g.val v

end Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
