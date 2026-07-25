module

public import FeitThompson.BGsection3.Remaining
public import FeitThompson.LinearAlgebra.MatrixBlocks

/-!
# Matrix trace infrastructure for Wielandt fixed-point arguments

This file contains the matrix-trace packages that are specific to the
Wielandt fixed-point setup but independent of the homocyclic source-core
construction.
-/

noncomputable section

namespace Wielandt

universe u

/-- The fixed-subspace rank appearing in the elementary-abelian form of
Wielandt's theorem. -/
@[expose] public noncomputable def fixedSubspaceFinrank
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G) : ℕ :=
  letI : MulDistribMulAction A V :=
    MulDistribMulAction.compHom V A.subtype
  Module.finrank (ZMod p)
    ↥((Representation.ofElementaryAbelianAction
        (A := A) (G := V) (p := p)).fixedSubspace
      (⊤ : Subgroup A))


public structure RectangularReindexedBlockTraceData
    {G κ : Type u} [Group G] [Fintype κ]
    (A : Subgroup G) [Fintype A] (q : ℕ)
    (M : G → Matrix κ κ (ZMod q)) (r : ℕ) : Type (u + 1) where
  leftIndex : Type u
  rightIndex : Type u
  [instFintypeLeftIndex : Fintype leftIndex]
  [instFintypeRightIndex : Fintype rightIndex]
  [instDecidableEqLeftIndex : DecidableEq leftIndex]
  [instDecidableEqRightIndex : DecidableEq rightIndex]
  indexEquiv : κ ≃ leftIndex ⊕ rightIndex
  leftColumn : Matrix (leftIndex ⊕ rightIndex) leftIndex (ZMod q)
  rightColumn : Matrix (leftIndex ⊕ rightIndex) rightIndex (ZMod q)
  topRow : Matrix leftIndex (leftIndex ⊕ rightIndex) (ZMod q)
  bottomRow : Matrix rightIndex (leftIndex ⊕ rightIndex) (ZMod q)
  card_right : Fintype.card rightIndex = r
  inverse_blocks :
    matrixOfBlockColumns leftColumn rightColumn *
      matrixOfBlockRows topRow bottomRow = 1
  bottom_right_identity : ∀ a : A,
    bottomRow * Matrix.reindex indexEquiv indexEquiv (M (a : G)) * rightColumn = 1
  top_left_sum_zero :
    (∑ a : A, topRow * Matrix.reindex indexEquiv indexEquiv (M (a : G)) * leftColumn) = 0


public structure ReindexedBlockTraceData
    {G κ : Type u} [Group G] [Fintype κ]
    (A : Subgroup G) [Fintype A] (q : ℕ)
    (M : G → Matrix κ κ (ZMod q)) (r : ℕ) : Type (u + 1) where
  leftIndex : Type u
  rightIndex : Type u
  [instFintypeLeftIndex : Fintype leftIndex]
  [instFintypeRightIndex : Fintype rightIndex]
  [instDecidableEqLeftIndex : DecidableEq leftIndex]
  [instDecidableEqRightIndex : DecidableEq rightIndex]
  indexEquiv : κ ≃ leftIndex ⊕ rightIndex
  P : Matrix (leftIndex ⊕ rightIndex) (leftIndex ⊕ rightIndex) (ZMod q)
  Q : Matrix (leftIndex ⊕ rightIndex) (leftIndex ⊕ rightIndex) (ZMod q)
  card_right : Fintype.card rightIndex = r
  inverse_blocks : P * Q = 1
  bottom_right_identity : ∀ a : A,
    (Q * Matrix.reindex indexEquiv indexEquiv (M (a : G)) * P).toBlocks₂₂ = 1
  top_left_sum_zero :
    (∑ a : A, (Q * Matrix.reindex indexEquiv indexEquiv (M (a : G)) * P).toBlocks₁₁) = 0

/-- Assemble rectangular block data into the square block-data package used by
the trace calculation. -/
public def RectangularReindexedBlockTraceData.toReindexedBlockTraceData
    {G κ : Type u} [Group G] [Fintype κ]
    {A : Subgroup G} [Fintype A] {q : ℕ}
    {M : G → Matrix κ κ (ZMod q)} {r : ℕ}
    (D : RectangularReindexedBlockTraceData (G := G) (κ := κ) A q M r) :
    ReindexedBlockTraceData (G := G) (κ := κ) A q M r := by
  classical
  letI : Fintype D.leftIndex := D.instFintypeLeftIndex
  letI : Fintype D.rightIndex := D.instFintypeRightIndex
  letI : DecidableEq D.leftIndex := D.instDecidableEqLeftIndex
  letI : DecidableEq D.rightIndex := D.instDecidableEqRightIndex
  refine {
    leftIndex := D.leftIndex
    rightIndex := D.rightIndex
    instFintypeLeftIndex := D.instFintypeLeftIndex
    instFintypeRightIndex := D.instFintypeRightIndex
    instDecidableEqLeftIndex := D.instDecidableEqLeftIndex
    instDecidableEqRightIndex := D.instDecidableEqRightIndex
    indexEquiv := D.indexEquiv
    P := matrixOfBlockColumns D.leftColumn D.rightColumn
    Q := matrixOfBlockRows D.topRow D.bottomRow
    card_right := D.card_right
    inverse_blocks := D.inverse_blocks
    bottom_right_identity := ?_
    top_left_sum_zero := ?_ }
  · intro a
    rw [matrixOfBlockRows_mul_toBlocks₂₂]
    exact D.bottom_right_identity a
  · calc
      (∑ a : A,
          (matrixOfBlockRows D.topRow D.bottomRow *
            Matrix.reindex D.indexEquiv D.indexEquiv (M (a : G)) *
            matrixOfBlockColumns D.leftColumn D.rightColumn).toBlocks₁₁) =
          ∑ a : A, D.topRow * Matrix.reindex D.indexEquiv D.indexEquiv (M (a : G)) *
            D.leftColumn := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [matrixOfBlockRows_mul_toBlocks₁₁]
      _ = 0 := D.top_left_sum_zero

/-- The trace formula supplied by one package of reindexed block data. -/
public theorem ReindexedBlockTraceData.trace_sum
    {G κ : Type u} [Group G] [Fintype κ]
    {A : Subgroup G} [Fintype A] {q : ℕ}
    {M : G → Matrix κ κ (ZMod q)} {r : ℕ}
    (D : ReindexedBlockTraceData (G := G) (κ := κ) A q M r) :
    Matrix.trace (∑ a : A, M (a : G)) = (r * Nat.card A : ZMod q) := by
  classical
  letI : Fintype D.leftIndex := D.instFintypeLeftIndex
  letI : Fintype D.rightIndex := D.instFintypeRightIndex
  letI : DecidableEq D.leftIndex := D.instDecidableEqLeftIndex
  letI : DecidableEq D.rightIndex := D.instDecidableEqRightIndex
  calc
    Matrix.trace (∑ a : A, M (a : G)) =
        (Fintype.card D.rightIndex : ZMod q) * (Nat.card A : ZMod q) :=
      trace_model_subgroup_sum_of_reindexed_block_data
        (A := A) (q := q) (M := M) (e := D.indexEquiv)
        (P := D.P) (Q := D.Q) (hPQ := D.inverse_blocks)
        (h22 := D.bottom_right_identity) (h11 := D.top_left_sum_zero)
    _ = (r * Nat.card A : ZMod q) := by
      rw [D.card_right]

/-- A matrix-valued lift with the expected subgroup trace sums supplies the
trace function used in the prime-power congruence step. -/
public theorem exists_trace_sum_function_of_matrix_trace_model
    {G ι κ : Type*} [Group G] [Fintype G] [Fintype ι] [Fintype κ]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (r : ι → ℕ) (q : ℕ)
    (M : G → Matrix κ κ (ZMod q))
    (htrace : ∀ i : ι,
      Matrix.trace (∑ a : A i, M (a : G)) =
        (r i * Nat.card (A i) : ZMod q)) :
    ∃ F : G → ZMod q,
      ∀ i : ι,
        (∑ a : A i, F (a : G)) =
          (r i * Nat.card (A i) : ZMod q) := by
  classical
  refine ⟨fun g => Matrix.trace (M g), ?_⟩
  intro i
  rw [← Matrix.trace_sum]
  exact htrace i

/-- A packaged matrix trace model for subgroup sums. -/
public structure MatrixTraceModel
    (G ι : Type u) [Group G] [Fintype G] [Fintype ι]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (q : ℕ) (r : ι → ℕ) : Type (u + 1) where
  matrixIndex : Type u
  [instFintypeMatrixIndex : Fintype matrixIndex]
  matrixLift : G → Matrix matrixIndex matrixIndex (ZMod q)
  trace_sum : ∀ i : ι,
    Matrix.trace (∑ a : A i, matrixLift (a : G)) =
      (r i * Nat.card (A i) : ZMod q)

/-- Unpack a matrix trace model into the previous existential form. -/
public theorem MatrixTraceModel.exists_matrix_trace_model
    {G ι : Type u} [Group G] [Fintype G] [Fintype ι]
    {A : ι → Subgroup G}
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {q : ℕ} {r : ι → ℕ}
    (D : MatrixTraceModel (G := G) (ι := ι) A q r) :
    ∃ κ' : Type u, ∃ hκ : Fintype κ',
      letI : Fintype κ' := hκ
      ∃ M' : G → Matrix κ' κ' (ZMod q),
        ∀ i : ι,
          Matrix.trace (∑ a : A i, M' (a : G)) =
            (r i * Nat.card (A i) : ZMod q) := by
  classical
  letI : Fintype D.matrixIndex := D.instFintypeMatrixIndex
  exact ⟨D.matrixIndex, inferInstance, D.matrixLift, D.trace_sum⟩

/-- A matrix trace model supplies the trace function used in the congruence
step. -/
public theorem MatrixTraceModel.exists_trace_sum_function
    {G ι : Type u} [Group G] [Fintype G] [Fintype ι]
    {A : ι → Subgroup G}
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {q : ℕ} {r : ι → ℕ}
    (D : MatrixTraceModel (G := G) (ι := ι) A q r) :
    ∃ F : G → ZMod q,
      ∀ i : ι,
        (∑ a : A i, F (a : G)) =
          (r i * Nat.card (A i) : ZMod q) := by
  classical
  letI : Fintype D.matrixIndex := D.instFintypeMatrixIndex
  exact exists_trace_sum_function_of_matrix_trace_model
    (A := A) (r := r) (q := q) D.matrixLift D.trace_sum

/-- The common matrix lift before choosing subgroup block decompositions. -/
public structure CommonMatrixLift (G : Type u) [Group G] (q : ℕ) : Type (u + 1) where
  matrixIndex : Type u
  [instFintypeMatrixIndex : Fintype matrixIndex]
  [instDecidableEqMatrixIndex : DecidableEq matrixIndex]
  matrixLift : G → Matrix matrixIndex matrixIndex (ZMod q)

/-- Block decompositions for every subgroup of a fixed common matrix lift. -/
public structure CommonMatrixLiftBlockFamily
    {G ι : Type u} [Group G] [Fintype G] [Fintype ι]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (q : ℕ) (r : ι → ℕ)
    (L : CommonMatrixLift G q) : Type (u + 1) where
  blockData :
    letI : Fintype L.matrixIndex := L.instFintypeMatrixIndex
    ∀ i : ι, ReindexedBlockTraceData (G := G) (κ := L.matrixIndex) (A i) q L.matrixLift (r i)

/-- A block family over a common lift is a matrix trace model. -/
public def CommonMatrixLiftBlockFamily.toMatrixTraceModel
    {G ι : Type u} [Group G] [Fintype G] [Fintype ι]
    {A : ι → Subgroup G}
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {q : ℕ} {r : ι → ℕ} {L : CommonMatrixLift G q}
    (D : CommonMatrixLiftBlockFamily (G := G) (ι := ι) A q r L) :
    MatrixTraceModel (G := G) (ι := ι) A q r := by
  classical
  letI : Fintype L.matrixIndex := L.instFintypeMatrixIndex
  refine {
    matrixIndex := L.matrixIndex
    instFintypeMatrixIndex := L.instFintypeMatrixIndex
    matrixLift := L.matrixLift
    trace_sum := ?_ }
  intro i
  exact ReindexedBlockTraceData.trace_sum (D.blockData i)


public structure RectangularCommonMatrixLiftBlockFamily
    {G ι : Type u} [Group G] [Fintype G] [Fintype ι]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (q : ℕ) (r : ι → ℕ)
    (L : CommonMatrixLift G q) : Type (u + 1) where
  blockData :
    letI : Fintype L.matrixIndex := L.instFintypeMatrixIndex
    ∀ i : ι,
      RectangularReindexedBlockTraceData (G := G) (κ := L.matrixIndex)
        (A i) q L.matrixLift (r i)

/-- Assemble a rectangular block family into the square block family used by
the trace model. -/
public def RectangularCommonMatrixLiftBlockFamily.toCommonMatrixLiftBlockFamily
    {G ι : Type u} [Group G] [Fintype G] [Fintype ι]
    {A : ι → Subgroup G}
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {q : ℕ} {r : ι → ℕ} {L : CommonMatrixLift G q}
    (D : RectangularCommonMatrixLiftBlockFamily (G := G) (ι := ι) A q r L) :
    CommonMatrixLiftBlockFamily (G := G) (ι := ι) A q r L := by
  classical
  letI : Fintype L.matrixIndex := L.instFintypeMatrixIndex
  refine { blockData := ?_ }
  intro i
  exact (D.blockData i).toReindexedBlockTraceData


public structure RectangularCommonMatrixLiftBlockData
    (G V ι : Type u) [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (e : ℕ) : Type (u + 1) where
  commonLift : CommonMatrixLift G (p ^ e)
  blockFamily : RectangularCommonMatrixLiftBlockFamily (G := G) (ι := ι) A (p ^ e)
    (fun i => fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i)) commonLift


public structure CommonMatrixLiftBlockData
    (G V ι : Type u) [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (e : ℕ) : Type (u + 1) where
  matrixIndex : Type u
  [instFintypeMatrixIndex : Fintype matrixIndex]
  matrixLift : G → Matrix matrixIndex matrixIndex (ZMod (p ^ e))
  blockData : ∀ i : ι,
    ReindexedBlockTraceData (G := G) (κ := matrixIndex) (A i) (p ^ e) matrixLift
      (fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i))

/-- Assemble rectangular common lift/block data into the square block-data
package used downstream. -/
public def RectangularCommonMatrixLiftBlockData.toCommonMatrixLiftBlockData
    {G V ι : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    (D : RectangularCommonMatrixLiftBlockData (G := G) (V := V) (ι := ι) (p := p) A e) :
    CommonMatrixLiftBlockData (G := G) (V := V) (ι := ι) (p := p) A e := by
  classical
  letI : Fintype D.commonLift.matrixIndex := D.commonLift.instFintypeMatrixIndex
  let Dfam := D.blockFamily.toCommonMatrixLiftBlockFamily
  refine {
    matrixIndex := D.commonLift.matrixIndex
    instFintypeMatrixIndex := D.commonLift.instFintypeMatrixIndex
    matrixLift := D.commonLift.matrixLift
    blockData := ?_ }
  intro i
  exact Dfam.blockData i

/-- Forget the subgroup block decompositions from a common lift/block-data
package. -/
public def CommonMatrixLiftBlockData.toCommonMatrixLift
    {G V ι : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    (D : CommonMatrixLiftBlockData (G := G) (V := V) (ι := ι) (p := p) A e) :
    CommonMatrixLift G (p ^ e) where
  matrixIndex := D.matrixIndex
  instFintypeMatrixIndex := D.instFintypeMatrixIndex
  instDecidableEqMatrixIndex := Classical.decEq D.matrixIndex
  matrixLift := D.matrixLift

/-- Forget only the ambient construction, retaining the per-subgroup block data
as a family over the common matrix lift. -/
public def CommonMatrixLiftBlockData.toBlockFamily
    {G V ι : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    (D : CommonMatrixLiftBlockData (G := G) (V := V) (ι := ι) (p := p) A e) :
    CommonMatrixLiftBlockFamily (G := G) (ι := ι) A (p ^ e)
      (fun i => fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i))
      (CommonMatrixLiftBlockData.toCommonMatrixLift A D) := by
  classical
  letI : Fintype D.matrixIndex := D.instFintypeMatrixIndex
  refine { blockData := ?_ }
  intro i
  exact D.blockData i

/-- A common lift/block-data package is a matrix trace model. -/
public def CommonMatrixLiftBlockData.toMatrixTraceModel
    {G V ι : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    [Fintype G] [Fintype ι]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    (D : CommonMatrixLiftBlockData (G := G) (V := V) (ι := ι) (p := p) A e) :
    MatrixTraceModel (G := G) (ι := ι) A (p ^ e)
      (fun i => fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i)) :=
  CommonMatrixLiftBlockFamily.toMatrixTraceModel
    (CommonMatrixLiftBlockData.toBlockFamily A D)

/-- A common lift/block-data package supplies the matrix trace model. -/
public theorem CommonMatrixLiftBlockData.exists_matrix_trace_model
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Fintype ι] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    (D : CommonMatrixLiftBlockData (G := G) (V := V) (ι := ι) (p := p) A e) :
    ∃ κ' : Type u, ∃ hκ : Fintype κ',
      letI : Fintype κ' := hκ
      ∃ M' : G → Matrix κ' κ' (ZMod (p ^ e)),
        ∀ i : ι,
          Matrix.trace (∑ a : A i, M' (a : G)) =
            (fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i) *
              Nat.card (A i) : ZMod (p ^ e)) := by
  classical
  exact MatrixTraceModel.exists_matrix_trace_model (D.toMatrixTraceModel A)

/-- Unpack a common lift/block-data package into the tuple-shaped endpoint used
by the earlier matrix-trace infrastructure. -/
public theorem CommonMatrixLiftBlockData.exists_tuple
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Fintype ι] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ}
    (D : CommonMatrixLiftBlockData (G := G) (V := V) (ι := ι) (p := p) A e) :
    ∃ κ : Type u, ∃ hκ : Fintype κ,
      letI : Fintype κ := hκ
      ∃ M : G → Matrix κ κ (ZMod (p ^ e)),
      ∃ l : ι → Type u, ∃ ridx : ι → Type u,
      ∃ hl : ∀ i, Fintype (l i), ∃ hr : ∀ i, Fintype (ridx i),
      ∃ hdl : ∀ i, DecidableEq (l i), ∃ hdr : ∀ i, DecidableEq (ridx i),
        letI : ∀ i, Fintype (l i) := hl
        letI : ∀ i, Fintype (ridx i) := hr
        letI : ∀ i, DecidableEq (l i) := hdl
        letI : ∀ i, DecidableEq (ridx i) := hdr
        ∃ be : ∀ i, κ ≃ l i ⊕ ridx i,
        ∃ P : ∀ i, Matrix (l i ⊕ ridx i) (l i ⊕ ridx i) (ZMod (p ^ e)),
        ∃ Q : ∀ i, Matrix (l i ⊕ ridx i) (l i ⊕ ridx i) (ZMod (p ^ e)),
          (∀ i, Fintype.card (ridx i) =
            fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i)) ∧
          (∀ i, P i * Q i = 1) ∧
          (∀ i, ∀ a : A i,
            (Q i * Matrix.reindex (be i) (be i) (M (a : G)) * P i).toBlocks₂₂ = 1) ∧
          (∀ i,
            (∑ a : A i,
              (Q i * Matrix.reindex (be i) (be i) (M (a : G)) * P i).toBlocks₁₁) = 0) := by
  classical
  letI : Fintype D.matrixIndex := D.instFintypeMatrixIndex
  refine ⟨D.matrixIndex, inferInstance, D.matrixLift,
    (fun i => (D.blockData i).leftIndex),
    (fun i => (D.blockData i).rightIndex),
    (fun i => (D.blockData i).instFintypeLeftIndex),
    (fun i => (D.blockData i).instFintypeRightIndex),
    (fun i => (D.blockData i).instDecidableEqLeftIndex),
    (fun i => (D.blockData i).instDecidableEqRightIndex),
    (fun i => (D.blockData i).indexEquiv),
    (fun i => (D.blockData i).P),
    (fun i => (D.blockData i).Q), ?_, ?_, ?_, ?_⟩
  · intro i
    exact (D.blockData i).card_right
  · intro i
    exact (D.blockData i).inverse_blocks
  · intro i a
    exact (D.blockData i).bottom_right_identity a
  · intro i
    exact (D.blockData i).top_left_sum_zero


public theorem exists_matrix_trace_model_of_common_lift_and_block_data
    {G ι κ : Type u} [Group G] [Fintype G] [Fintype ι] [Fintype κ]
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (q : ℕ) (M : G → Matrix κ κ (ZMod q))
    (r : ι → ℕ)
    (l : ι → Type u) (ridx : ι → Type u)
    [∀ i, Fintype (l i)] [∀ i, Fintype (ridx i)]
    [∀ i, DecidableEq (l i)] [∀ i, DecidableEq (ridx i)]
    (e : ∀ i, κ ≃ l i ⊕ ridx i)
    (P Q : ∀ i, Matrix (l i ⊕ ridx i) (l i ⊕ ridx i) (ZMod q))
    (hcard : ∀ i, Fintype.card (ridx i) = r i)
    (hPQ : ∀ i, P i * Q i = 1)
    (h22 : ∀ i, ∀ a : A i,
      (Q i * Matrix.reindex (e i) (e i) (M (a : G)) * P i).toBlocks₂₂ = 1)
    (h11 : ∀ i,
      (∑ a : A i,
        (Q i * Matrix.reindex (e i) (e i) (M (a : G)) * P i).toBlocks₁₁) = 0) :
    ∃ κ' : Type u, ∃ hκ : Fintype κ',
      letI : Fintype κ' := hκ
      ∃ M' : G → Matrix κ' κ' (ZMod q),
        ∀ i : ι,
          Matrix.trace (∑ a : A i, M' (a : G)) =
            (r i * Nat.card (A i) : ZMod q) := by
  classical
  refine ⟨κ, inferInstance, M, ?_⟩
  intro i
  have htrace :=
    trace_model_subgroup_sum_of_reindexed_block_data
      (A := A i) (q := q) (M := M) (e := e i)
      (P := P i) (Q := Q i) (hPQ := hPQ i) (h22 := h22 i) (h11 := h11 i)
  calc
    Matrix.trace (∑ a : A i, M (a : G)) =
        (Fintype.card (ridx i) : ZMod q) * (Nat.card (A i) : ZMod q) := htrace
    _ = (r i * Nat.card (A i) : ZMod q) := by
      rw [hcard i]
