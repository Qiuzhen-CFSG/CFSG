module

public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Radical.Translations
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Octad weight lines and irreducibility

The first-family eigenvalues retain the half-overlap sign in 29.12(2).
Golay restriction onto an octad and the even-subset annihilator theorem
show that these characters distinguish exactly the complement classes.
Consequently their common eigenspaces in the literal block are precisely
the one-dimensional spans of its positively signed class vectors.

Successively removing unwanted coefficients with differences of diagonal
operators extracts each coordinate inside any invariant subspace. The actual
second-family actors then move its nonzero coordinate to every basis line,
with the exact half-overlap sign. This proves irreducibility of `blockAction`
from `GeneratorLaws`, without assuming global collection or an extraspecial
quotient. The parent source assembly supplies the three generator laws.

Source: Aschbacher, *Sporadic Groups*, 29.13(4) and the weight-space argument
in 30.1, printed pp. 160–163. The full-space fixed-space equality of 29.13(2)
and generation by zero-half-overlap translations are separate obligations.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
open TrialitySpin Atlas.Codes Atlas.Fischer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The subset-dependent binary character is well defined modulo complementation. -/
def firstCharacter (c : Octad) (d : ParkerLoop) : SubsetClass c → ParkerBit :=
  Quotient.lift (fun J => binaryDot (subsetWord c J) d.1.val) (by
    intro J K h
    rcases h with rfl | h
    · rfl
    · change J = complementSubset c K at h
      rw [h, subsetWord_complement, LinearMap.map_add₂,
        golay_selfOrthogonal d.1.prop c.val.val c.val.prop, add_zero])

@[simp] theorem firstCharacter_mk (c : Octad) (d : ParkerLoop) (J : EvenSubset c) :
    firstCharacter c d (subsetClass c J) = binaryDot (subsetWord c J) d.1.val := rfl

/-- The actual real eigenvalue, including the half-overlap term. -/
def firstWeight (c : Octad) (d : ParkerLoop) (a : SubsetClass c) : ℝ :=
  if firstCharacter c d a + golayHalfOverlap c.val d.1 = 0 then 1 else -1

theorem firstWeight_ne_zero (c : Octad) (d : ParkerLoop) (a : SubsetClass c) :
    firstWeight c d a ≠ 0 := by unfold firstWeight; split <;> norm_num

theorem firstWeight_eq_iff (c : Octad) (d : ParkerLoop) (a b : SubsetClass c) :
    firstWeight c d a = firstWeight c d b ↔ firstCharacter c d a = firstCharacter c d b := by
  have hi : Function.Injective (fun t : ParkerBit => if t = 0 then (1 : ℝ) else -1) := by
    intro x y he
    rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;> norm_num at *
  exact hi.eq_iff.trans add_right_cancel_iff

private theorem subsetWord_mul_octad (c : Octad) (J : EvenSubset c) :
    c.val.val * subsetWord c J = subsetWord c J := by
  funext i
  by_cases hi : c.val.val i = 0
  · simp [subsetWord, hi]
  · have hc : c.val.val i = 1 := (bit_cases _).resolve_left hi
    simp [hc]

private theorem subsetWord_dot_intersection (c : Octad) (J : EvenSubset c) (w : BinaryWord) :
    binaryDot (subsetWord c J) (c.val.val * w) = binaryDot (subsetWord c J) w := by
  change (∑ i : Omega, subsetWord c J i * (c.val.val i * w i)) =
    ∑ i : Omega, subsetWord c J i * w i
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : c.val.val i = 0
  · simp [subsetWord, hi]
  · have hc : c.val.val i = 1 := (bit_cases _).resolve_left hi
    simp [hc]

/-- Distinct complement classes have distinct first-family characters. -/
theorem firstCharacter_separates (c : Octad) (a b : SubsetClass c) :
    (∀ d : ParkerLoop, firstCharacter c d a = firstCharacter c d b) ↔ a = b := by
  refine Quotient.inductionOn₂ a b fun J K => ?_
  constructor
  · intro h
    have hz (d : ParkerLoop) : binaryDot (subsetWord c (J + K)) d.1.val = 0 := by
      rw [subsetWord_add, LinearMap.map_add₂, ← firstCharacter_mk, ← firstCharacter_mk,
        show firstCharacter c d (subsetClass c J) = firstCharacter c d (subsetClass c K) from h d,
        CharTwo.add_self_eq_zero]
    have ha : c.val.val * subsetWord c (J + K) = 0 ∨
        c.val.val * subsetWord c (J + K) = c.val.val := by
      apply (evenSubset_annihilator c _).mp
      intro L
      obtain ⟨e, he⟩ := exists_golay_intersection c L
      rw [binaryDot_symmetric, ← he, subsetWord_dot_intersection]
      exact hz (e, 0)
    rw [subsetWord_mul_octad, subsetWord_add] at ha
    apply (subsetClass_eq c J K).mpr
    rcases ha with he | he
    · left
      apply subsetWord_injective c
      funext i
      have hi := congrFun he i
      exact (eq_neg_of_add_eq_zero_left hi).trans (CharTwo.neg_eq _)
    · right
      apply subsetWord_injective c
      rw [subsetWord_complement]
      calc
        subsetWord c J = (subsetWord c J + subsetWord c K) + subsetWord c K := by
          funext i
          change _ = (_ + _) + subsetWord c K i
          rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        _ = c.val.val + subsetWord c K := by rw [he]
        _ = _ := add_comm _ _
  · intro he d
    exact congrArg (firstCharacter c d) he

theorem firstWeight_separates (c : Octad) (a b : SubsetClass c) :
    (∀ d : ParkerLoop, firstWeight c d a = firstWeight c d b) ↔ a = b := by
  simp_rw [firstWeight_eq_iff]
  exact firstCharacter_separates c a b

/-- The published action is diagonal on the actual complement-class basis. -/
theorem blockAction_first_blockVector (h : GeneratorLaws) (c : Octad)
    (d : ParkerLoop) (a : SubsetClass c) :
    blockAction c (firstActor h d c) (blockVector c a) =
      firstWeight c d a • blockVector c a := by
  refine Quotient.inductionOn a fun J => ?_
  exact blockAction_first_weight h d c (parameters c J 0) rfl


theorem blockAction_first_basis (h : GeneratorLaws) (c : Octad)
    (d : ParkerLoop) (a : SubsetClass c) :
    blockAction c (firstActor h d c) (blockBasis c a) =
      firstWeight c d a • blockBasis c a := by
  simpa only [blockBasis_apply] using blockAction_first_blockVector h c d a

/-- Every coefficient transforms by its own, separated character. -/
theorem blockAction_first_coeff (h : GeneratorLaws) (c : Octad)
    (d : ParkerLoop) (v : block c) (a : SubsetClass c) :
    (blockBasis c).repr (blockAction c (firstActor h d c) v) a =
      firstWeight c d a * (blockBasis c).repr v a := by
  have he : ((blockBasis c).coord a).comp (blockAction c (firstActor h d c)) =
      firstWeight c d a • (blockBasis c).coord a := by
    apply (blockBasis c).ext
    intro b
    simp only [LinearMap.comp_apply, blockAction_first_basis,
      map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      LinearMap.smul_apply, smul_eq_mul, Finsupp.single_apply]
    by_cases hb : b = a
    · subst b; simp
    · simp [hb]
  exact LinearMap.congr_fun he v

/-- The simultaneous first-family eigenvector equations cut out exactly one
line in the literal octad block. Zero is allowed, as it is in the line. -/
theorem first_eigenvectors_iff (h : GeneratorLaws) (c : Octad)
    (a : SubsetClass c) (v : block c) :
    (∀ d : ParkerLoop, blockAction c (firstActor h d c) v = firstWeight c d a • v) ↔
      v ∈ Submodule.span ℝ {blockVector c a} := by
  constructor
  · intro hv
    have hzero (b : SubsetClass c) (hb : b ≠ a) : (blockBasis c).repr v b = 0 := by
      by_contra hn
      apply hb
      apply (firstWeight_separates c b a).mp
      intro d
      have he := congrArg (fun w => (blockBasis c).repr w b) (hv d)
      rw [blockAction_first_coeff] at he
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at he
      exact mul_right_cancel₀ hn he
    apply Submodule.mem_span_singleton.mpr
    refine ⟨(blockBasis c).repr v a, ?_⟩
    apply (blockBasis c).repr.injective
    ext b
    rw [← blockBasis_apply, map_smul, Module.Basis.repr_self]
    by_cases hb : b = a
    · subst b; simp
    · simp [Ne.symm hb, hzero b hb]
  · intro hv d
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, blockAction_first_blockVector, smul_comm]

/-- The common weight subspace, with the source actors and source eigenvalues. -/
def firstWeightSpace (h : GeneratorLaws) (c : Octad) (a : SubsetClass c) :
    Submodule ℝ (block c) :=
  ⨅ d : ParkerLoop, LinearMap.ker
    (blockAction c (firstActor h d c) - firstWeight c d a • LinearMap.id)

theorem firstWeightSpace_eq (h : GeneratorLaws) (c : Octad) (a : SubsetClass c) :
    firstWeightSpace h c a = Submodule.span ℝ {blockVector c a} := by
  ext v
  simpa only [firstWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    using first_eigenvectors_iff h c a v

theorem firstWeightSpace_finrank (h : GeneratorLaws) (c : Octad) (a : SubsetClass c) :
    Module.finrank ℝ (firstWeightSpace h c a) = 1 := by
  rw [firstWeightSpace_eq]
  exact finrank_span_singleton ((blockVector_linearIndependent c).ne_zero a)


private theorem filter_coefficients (h : GeneratorLaws) (c : Octad)
    (U : Subrepresentation (blockAction c)) (v : block c) (hv : v ∈ U)
    (a : SubsetClass c) (s : Finset (SubsetClass c)) :
    ∃ w : block c, w ∈ U ∧ (blockBasis c).repr w a = (blockBasis c).repr v a ∧
      ∀ b ∈ s, b ≠ a → (blockBasis c).repr w b = 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨v, hv, rfl, by simp⟩
  | @insert b s hbs ih =>
    obtain ⟨w, hw, hwa, hws⟩ := ih
    by_cases hba : b = a
    · refine ⟨w, hw, hwa, ?_⟩
      intro j hj hja
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (hja hba).elim
      · exact hws j hj hja
    obtain ⟨d, hd⟩ : ∃ d : ParkerLoop, firstWeight c d a ≠ firstWeight c d b := by
      by_contra hn
      push Not at hn
      exact hba ((firstWeight_separates c a b).mp hn).symm
    let t : ℝ := firstWeight c d a - firstWeight c d b
    have ht : t ≠ 0 := sub_ne_zero.mpr hd
    let u : block c := t⁻¹ • (blockAction c (firstActor h d c) w - firstWeight c d b • w)
    have hu (j : SubsetClass c) : (blockBasis c).repr u j =
        (t⁻¹ * (firstWeight c d j - firstWeight c d b)) * (blockBasis c).repr w j := by
      simp only [u, map_smul, map_sub, Finsupp.smul_apply, Finsupp.sub_apply,
        smul_eq_mul, blockAction_first_coeff]
      ring
    refine ⟨u, U.toSubmodule.smul_mem _
      (U.toSubmodule.sub_mem (U.apply_mem_toSubmodule _ hw) (U.toSubmodule.smul_mem _ hw)),
      ?_, ?_⟩
    · rw [hu, show firstWeight c d a - firstWeight c d b = t from rfl,
        inv_mul_cancel₀ ht, one_mul, hwa]
    · intro j hj hja
      rcases Finset.mem_insert.mp hj with rfl | hj
      · rw [hu, sub_self, mul_zero, zero_mul]
      · rw [hu, hws j hj hja, mul_zero]

/-- First-family invariance permits extraction of each individual coefficient.
This supplies the irreducibility argument without an extraspecial-group premise. -/
theorem coefficient_blockVector_mem (h : GeneratorLaws) (c : Octad)
    (U : Subrepresentation (blockAction c)) (v : block c) (hv : v ∈ U)
    (a : SubsetClass c) : (blockBasis c).repr v a • blockVector c a ∈ U := by
  obtain ⟨w, hw, hwa, hws⟩ := filter_coefficients h c U v hv a Finset.univ
  have he : (blockBasis c).repr v a • blockVector c a = w := by
    apply (blockBasis c).repr.injective
    ext b
    rw [← blockBasis_apply, map_smul, Module.Basis.repr_self]
    by_cases hb : b = a
    · subst b; simpa using hwa.symm
    · simp [Ne.symm hb, hws b (Finset.mem_univ b) hb]
  exact he.symm ▸ hw

/-- The actual second-family actors move any basis vector to a signed copy of any
other; the coefficient is exactly the source half-overlap sign. -/
theorem blockAction_second_transitive (h : GeneratorLaws) (c : Octad)
    (a b : SubsetClass c) :
    ∃ e : ParkerLoop, blockAction c (secondActor h e c) (blockVector c a) =
      (if golayHalfOverlap e.1 c.val = 0 then (1 : ℝ) else -1) • blockVector c b := by
  refine Quotient.inductionOn₂ a b fun J K => ?_
  obtain ⟨e, he⟩ := blockAction_translation h c J K 0
  refine ⟨e, Subtype.ext ?_⟩
  exact he.trans (vector_sign_bit (parameters c K 0) (golayHalfOverlap e.1 c.val))

/-- Irreducibility on the literal block follows from separated diagonal weights
and the actual signed translations, without global radical collection. -/
theorem blockAction_isIrreducible (h : GeneratorLaws) (c : Octad) :
    Representation.IsIrreducible (blockAction c) := by
  have : Nontrivial (block c) := Module.nontrivial_of_finrank_pos
    (by rw [block_finrank]; decide)
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro he
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule he)
  intro U
  by_cases hU : U.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hU)
  right
  obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  obtain ⟨a, ha⟩ : ∃ a : SubsetClass c, (blockBasis c).repr v a ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hne
    apply (blockBasis c).repr.injective
    ext b
    simpa using hn b
  have haU : blockVector c a ∈ U :=
    (U.toSubmodule.smul_mem_iff ha).mp (coefficient_blockVector_mem h c U v hv a)
  have hbU (b : SubsetClass c) : blockVector c b ∈ U := by
    obtain ⟨e, he⟩ := blockAction_second_transitive h c a b
    have hu := U.apply_mem_toSubmodule (secondActor h e c) haU
    rw [he] at hu
    apply (U.toSubmodule.smul_mem_iff (s :=
      if golayHalfOverlap e.1 c.val = 0 then (1 : ℝ) else -1) (by split <;> norm_num)).mp hu
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  rw [← span_blockVector c]
  apply Submodule.span_le.mpr
  rintro _ ⟨b, rfl⟩
  exact hbU b

end Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
