module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.MatrixQuotient

/-!
# Concrete candidates for elementary-pair incidence in the max2 quotient

The first candidate is the stabilizer of the three binary rows 23, 1024,
and 1047 under inverse right multiplication. The second is the closure of
three explicit words in the quotient generators. The word instructions are
also evaluable in H, so actual lifts are available independently of any
subgroup recognition.

These definitions make no coverage, order, or ambient placement claim.
`ElementaryMatrixIncidence` is the remaining finite quotient calculation;
`InvolutionMatrixOverlapLift` requires an actual max4 conjugate containing
the full inverse image of each candidate. These are separate obligations.

Untrusted witness search: `Geometry/source/check_candidates.g` and
`second_words.json`, recovered from the retained earlier workspace. GAP finds
two order-2304 pair products. Both have elementary Sylow three-subgroups, and
only one lies in a conjugate of the first candidate. Thus a single-line
incidence assertion must not replace the two-candidate obligation below.
These observations guide the definitions and are not used as Lean premises.

Source context: Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528
of `refs/quasithin.pdf`), citing Aschbacher, *Overgroups of Sylow subgroups
in sporadic groups* (1986); GLS3 Table 5.3i, printed p.270. Matrix and word
provenance is documented in the imported `MatrixQuotient` module.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

attribute [local irreducible] Janko4.modelGroup

/-- Binary row coordinates, using the same bit order as the quotient matrices. -/
def involutionMatrixVector (n : ℕ) : Multiplicative OuterImageComparison.BinaryVector :=
  Multiplicative.ofAdd (fun j => if n.testBit j.val then 1 else 0)

/-- A specified three-vector line in the short orbit of the matrix quotient. -/
def involutionMatrixLine : Set (Multiplicative OuterImageComparison.BinaryVector) :=
  {involutionMatrixVector 23, involutionMatrixVector 1024, involutionMatrixVector 1047}

/-- The stabilizer of the specified line under inverse right multiplication. -/
def involutionMatrixLineStabilizer : Subgroup LowerBound.quotientSubgroup :=
  (MulAction.stabilizer (MulAut (Multiplicative OuterImageComparison.BinaryVector))
    involutionMatrixLine).comap
      (OuterImageComparison.rowAction.comp LowerBound.quotientSubgroup.subtype)

/-- Instructions for three words in the original quotient generators.
These specify the second candidate; no coverage or order is asserted here. -/
def involutionSecondInstructions : Fin 3 → List (Bool × ℤ) :=
  ![[(true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1)],
    [(true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)],
    [(true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1)]]

/-- Evaluate the same three words in any group, permitting actual source lifts. -/
def involutionSecondWord {G : Type*} [Group G] (x y : G) (i : Fin 3) : G :=
  ((involutionSecondInstructions i).map (fun z => (if z.1 then y else x) ^ z.2)).prod

/-- Three literal elements of the certified matrix quotient. -/
def involutionMatrixSecondGenerator (i : Fin 3) : LowerBound.quotientSubgroup :=
  involutionSecondWord ⟨LowerBound.quotientX, LowerBound.quotientX_mem⟩
    ⟨LowerBound.quotientY, LowerBound.quotientY_mem⟩ i

/-- The second concrete candidate, defined by the three displayed words. -/
def involutionMatrixSecondSubgroup : Subgroup LowerBound.quotientSubgroup :=
  Subgroup.closure (Set.range involutionMatrixSecondGenerator)

/-- The two specified candidates, with no assertion yet that they cover pairs. -/
def involutionMatrixCandidate : Bool → Subgroup LowerBound.quotientSubgroup
  | false => involutionMatrixLineStabilizer
  | true => involutionMatrixSecondSubgroup

/-- The actual matrix quotient map, with codomain restricted to its proved image. -/
noncomputable def involutionSourceMatrixMap :
    sourceSubgroup →* LowerBound.quotientSubgroup :=
  involutionSourceMatrixQuotientEquiv.toMonoidHom.comp involutionSourceQuotientMap

@[simp] theorem involutionSourceMatrixMap_coe (x : sourceSubgroup) :
    (involutionSourceMatrixMap x : LowerBound.QuotientMatrixˣ) = LowerBound.quotientMap x := rfl

theorem involutionSourceMatrixMap_surjective : Function.Surjective involutionSourceMatrixMap :=
  involutionSourceMatrixQuotientEquiv.surjective.comp
    (QuotientGroup.mk'_surjective (pCore 2 sourceSubgroup))

theorem involutionSourceMatrixMap_ker :
    involutionSourceMatrixMap.ker = pCore 2 sourceSubgroup := by
  rw [involutionSourceMatrixMap, MonoidHom.ker_comp_of_injective _ _
    involutionSourceMatrixQuotientEquiv.injective]
  exact QuotientGroup.ker_mk' _

/-- The finite incidence calculation, stated only in the certified matrix quotient. -/
def ElementaryMatrixIncidence : Prop :=
  ∀ (S : Sylow 2 LowerBound.quotientSubgroup) (R : Subgroup LowerBound.quotientSubgroup),
    IsElementaryAbelian 3 R → Nat.card R = 3 ^ 2 →
    (R : Set LowerBound.quotientSubgroup) * (S : Set LowerBound.quotientSubgroup) =
      (S : Set LowerBound.quotientSubgroup) * (R : Set LowerBound.quotientSubgroup) →
    ∃ (i : Bool) (u : LowerBound.quotientSubgroup),
      R ⊔ (S : Subgroup LowerBound.quotientSubgroup) ≤
        (involutionMatrixCandidate i).map (MulAut.conj u).toMonoidHom

/-- Two fixed inverse-image placements. Each includes the entire kernel. -/
def InvolutionMatrixOverlapLift : Prop :=
  ∀ i : Bool, ∃ g : Janko4.Model,
    (involutionMatrixCandidate i).comap involutionSourceMatrixMap ≤
      involutionSourceMax4Overlap g


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
