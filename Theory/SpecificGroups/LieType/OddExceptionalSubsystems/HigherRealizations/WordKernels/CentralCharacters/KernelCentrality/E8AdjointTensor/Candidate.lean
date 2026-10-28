module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.Transport
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.AdjointBlocks.Coordinates
public import Theory.AlgebraicGroup.RootSystems.IntegralChevalleyOperatorOrientation

/-!+# The signed integral E6 operator tensor in the E8 carrier

Each E6 root is reached by its source Tits route. We transport the corresponding
E8 simple operator along the image of that same route, multiplying by the source
carrier sign and the source bipartite operator orientation. The Cartan values are
the negative simple orientation times the raising/lowering commutator. Thus the
three simple values are `εᵢ Eᵢ`, `-εᵢ Fᵢ`, and `-εᵢ [Eᵢ,Fᵢ]`.

This fixes the actual integral tensor and proves pinning of both signed simple
operators. Its commutator identities are separate obligations; neither covariance
nor an `IntegralAdjointData` instance is asserted here.

Source: GLS3 §§1.10–1.12 and 2.6.2 (`refs/KGroup/GLS3/chapter2.tex`),
the common integral lattice for a closed root subsystem.
-/

@[expose] public section
noncomputable section

open Matrix Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open scoped Classical

namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor

attribute [local instance] Classical.decEq
local instance candidateRootFintype : Fintype typeE8Roots := Fintype.ofFinite _

/-- The 248 coordinates of the ambient integral Geck carrier. -/
abbrev TargetIndex := typeE8RootPairing_base.support ⊕ typeE8Roots

/-- Use the source route and source operator orientation for both polarities. -/
def rootTensor (r : typeE6Roots) : Matrix TargetIndex TargetIndex ℤ :=
  let := typeE6RootPairing.indexNeg
  if typeE6RootPairing_base.IsPos r then
    let q := rootRoute (P := typeE6RootPairing) (b := typeE6RootPairing_base) r
    simpleRouteOperatorOrientation true q.word q.simple •
      transportedMatrix (q.word.map AdjointBlocks.baseE8)
        (eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 q.simple))
  else
    let q := rootRoute (P := typeE6RootPairing) (b := typeE6RootPairing_base) (-r)
    simpleRouteOperatorOrientation false q.word q.simple •
      transportedMatrix (q.word.map AdjointBlocks.baseE8)
        (fMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 q.simple))

/-- One E8 integral endomorphism for each of the 78 source coordinates. -/
def tensor : Index → Matrix TargetIndex TargetIndex ℤ
  | Sum.inr r => rootTensor r
  | Sum.inl i =>
      -simpleOperatorOrientation (b := typeE6RootPairing_base) i •
        (eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) *
            fMatrix (AdjointBlocks.baseE8 i) -
          fMatrix (AdjointBlocks.baseE8 i) * eMatrix (AdjointBlocks.baseE8 i))

/-- Positive simple coordinates have the source bipartite normalization. -/
theorem tensor_simple (i : typeE6RootPairing_base.support) :
    tensor (Sum.inr (i : typeE6Roots)) =
      simpleOperatorOrientation (b := typeE6RootPairing_base) i •
        eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) := by
  simp [tensor, rootTensor, typeE6RootPairing_base.isPos_of_mem_support i.property,
    simpleRouteOperatorOrientation, titsWordSign]

/-- Negative simple coordinates have the additional minus sign. -/
theorem tensor_neg_simple (i : typeE6RootPairing_base.support) :
    let := typeE6RootPairing.indexNeg
    tensor (Sum.inr (-i : typeE6Roots)) =
      -simpleOperatorOrientation (b := typeE6RootPairing_base) i •
        fMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) := by
  let := typeE6RootPairing.indexNeg
  dsimp only
  have hi := typeE6RootPairing_base.isPos_of_mem_support i.property
  have hn : ¬typeE6RootPairing_base.IsPos (-i : typeE6Roots) := by
    rw [RootPairing.Base.IsPos.neg_iff_not]
    exact not_not_intro hi
  rw [tensor, rootTensor, if_neg hn, neg_neg]
  dsimp only
  simp only [rootRoute_word_simple, rootRoute_simple, List.map_nil,
    transportedMatrix_nil, simpleRouteOperatorOrientation,
    titsWordSign, one_mul, signedSimpleOperatorOrientation_false]

/-- The Cartan normalization is fixed in the same source convention. -/
theorem tensor_cartan (i : typeE6RootPairing_base.support) :
    tensor (Sum.inl i) =
      -simpleOperatorOrientation (b := typeE6RootPairing_base) i •
        (eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) *
            fMatrix (AdjointBlocks.baseE8 i) -
          fMatrix (AdjointBlocks.baseE8 i) * eMatrix (AdjointBlocks.baseE8 i)) := rfl

/-- Both signed, numbered first operators belong to the integral tensor image. -/
theorem pinning (a : Bool × Fin 6) :
    ∃ x : Index → ℤ, ∑ j, x j • tensor j = e8Family.dividedPower a 1 := by
  let := typeE6RootPairing.indexNeg
  rcases a with ⟨s, i⟩
  cases s
  · refine ⟨Pi.single (Sum.inr (-(simpleIndex i) : typeE6Roots))
      (-simpleOperatorOrientation (b := typeE6RootPairing_base) (simpleIndex i)), ?_⟩
    simp only [Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, tensor_neg_simple, smul_smul, neg_mul_neg, simpleOperatorOrientation_sq,
      one_smul, AdjointBlocks.baseE8_numbered]
    simp [e8Family, numberedFamily, simpleFamily]
  · refine ⟨Pi.single (Sum.inr (simpleIndex i : typeE6Roots))
      (simpleOperatorOrientation (b := typeE6RootPairing_base) (simpleIndex i)), ?_⟩
    simp only [Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, tensor_simple, smul_smul, simpleOperatorOrientation_sq,
      one_smul, AdjointBlocks.baseE8_numbered]
    simp [e8Family, numberedFamily, simpleFamily]

/-- The integral linear extension of the fixed coordinate tensor. -/
def adjointMap : (Index → ℤ) →ₗ[ℤ] Matrix TargetIndex TargetIndex ℤ := tensorMap tensor ℤ

theorem adjointMap_apply (x : Index → ℤ) : adjointMap x = ∑ j, x j • tensor j := by
  simp [adjointMap, tensorMap_apply]

theorem adjointMap_single (j : Index) : adjointMap (Pi.single j 1) = tensor j := by
  simpa [adjointMap] using tensorMap_single tensor ℤ j

/-- The six positive infinitesimal identities, on every source basis vector. -/
def PositiveCommutators : Prop :=
  ∀ (i : typeE6RootPairing_base.support) (j : Index),
    adjointMap (eMatrix (P := typeE6RootPairing) i *ᵥ Pi.single j 1) =
      eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) * tensor j -
        tensor j * eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i)

/-- The six negative infinitesimal identities, on every source basis vector. -/
def NegativeCommutators : Prop :=
  ∀ (i : typeE6RootPairing_base.support) (j : Index),
    adjointMap (fMatrix (P := typeE6RootPairing) i *ᵥ Pi.single j 1) =
      fMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) * tensor j -
        tensor j * fMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i)

/-- Opposition fixes source Cartan coordinates and exchanges opposite roots;
on the target tensor its conjugation has the additional integral minus sign. -/
def IntegralOppositionCovariance : Prop :=
  ∀ x : Index → ℤ,
    adjointMap
      (omegaMatrix (P := typeE6RootPairing) (b := typeE6RootPairing_base) *ᵥ x) =
      -(omegaMatrix (P := typeE8RootPairing) (b := typeE8RootPairing_base) *
        adjointMap x * omegaMatrix (P := typeE8RootPairing) (b := typeE8RootPairing_base))

end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
