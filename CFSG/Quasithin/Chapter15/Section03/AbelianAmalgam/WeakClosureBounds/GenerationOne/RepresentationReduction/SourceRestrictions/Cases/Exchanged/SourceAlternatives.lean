module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.ModelComparisons
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.BorelMarkings
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.PairCoordinates
public import Theory.Representation.BinaryOffender.IrreducibleOrbitAction
public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.BinaryPermutation

/-!
# The complete exchanged-component restriction alternatives

This is an input interface for F.9.18(5), not a proof of that theorem.
Here V is the source tilde space, I is tilde-I, IH is its H-orbit,
and IK = [IH,K]. A hat is always the image modulo C_V(K₀).
In particular the orthogonal and tensor rows identify I itself, whereas
the natural constituent row identifies its central image. The four-copy
row retains O² of the action of C_H(K₀) on IH, not its two-core.

Every model is a concrete representation and every identification retains
both a group equivalence and a linear intertwiner. No fixed-space or
FF-exclusion hypothesis is part of this interface.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), F.9.18(5),
printed pp.325--326; A.1.40--42, pp.31--32; application on p.1152.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Matrix
open scoped MatrixGroups TensorProduct
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
open RemainingModels BorelReduction BorelReduction.SourceCases

variable {D E V X : Type*} [Group D] [Group E]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup X] [Module (ZMod 2) X]

/-- An identification of a literal invariant subspace, with no further quotient. -/
structure LiteralIdentification (ρ : Representation (ZMod 2) D V)
    (K : Subgroup D) (I : Submodule (ZMod 2) V)
    (hI : K ≤ subspaceStabilizer ρ I) (σ : Representation (ZMod 2) E X) where
  groupEquiv : K ≃* E
  linearEquiv : I ≃ₗ[ZMod 2] X
  equivariant : ∀ g v, linearEquiv ((invariantSubspace ρ K I hI).toRepresentation g v) =
    σ (groupEquiv g) (linearEquiv v)

/-- The K-action on the image of I modulo C_V(K₀), keeping K and K₀ distinct. -/
structure HatIdentification (ρ : Representation (ZMod 2) D V)
    (K K₀ : Subgroup D) (hK : K ≤ K₀) (I : Submodule (ZMod 2) V)
    (hI : K₀ ≤ subspaceStabilizer ρ I) (σ : Representation (ZMod 2) E X) where
  groupEquiv : K ≃* E
  linearEquiv : centralQuotient ρ K₀ I ≃ₗ[ZMod 2] X
  equivariant : ∀ (g : K) v,
    linearEquiv (centralQuotientRepresentation ρ K₀ I hI (inclusion hK g) v) =
      σ (groupEquiv g) (linearEquiv v)

/-- All component groups in the initial sentence of F.9.18(5). -/
def FiveComponentList (K : Subgroup D) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
    1 < n ∧ Nat.card F = 2 ^ n ∧ Nonempty (K ≃* PSL(2,F))) ∨
  (∃ m : ℕ, 0 < m ∧ Nonempty (K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∨
  Nonempty (K ≃* alternatingGroup (Fin 5)) ∨ Nonempty (K ≃* PSL(3,ZMod 2))

/-- The actual four-dimensional A₅ natural module. -/
def alternatingFiveNatural :=
  (BinaryPermutation.coreRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype

/-- Four isomorphic copies, with one common action and actor identification. -/
def fourCopies (σ : Representation (ZMod 2) E X) :
    Representation (ZMod 2) E (Fin 4 → X) where
  toFun g :=
    { toFun := fun v i => σ g (v i)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp [Module.End.mul_apply]

/-- The tensor of the two actual three-dimensional binary natural actions. -/
def binaryThreeTensor : Representation (ZMod 2)
    (SL(3,ZMod 2) × SL(3,ZMod 2))
    ((Fin 3 → ZMod 2) ⊗[ZMod 2] (Fin 3 → ZMod 2)) :=
  Representation.tprod
    ((specialLinearNatural (k := ZMod 2) 3).comp (MonoidHom.fst _ _))
    ((specialLinearNatural (k := ZMod 2) 3).comp (MonoidHom.snd _ _))

variable (ρ : Representation (ZMod 2) D V)
  (K K₀ T : Subgroup D) (hK : K ≤ K₀) (I : Submodule (ZMod 2) V)
  (hI : K₀ ≤ subspaceStabilizer ρ I)

/-- All natural constituent possibilities, including the exceptional groups
which will only be discarded by comparison with the actual E.2.2 model. -/
inductive FiveNatural : Prop
  | linear (F : Type) [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
      (n : ℕ) (positive : 0 < n) (card : Nat.card F = 2 ^ n)
      (identification : HatIdentification ρ K K₀ hK I hI
        (restrictScalars (specialLinearNatural (k := F) 2)))
  | suzuki (m : ℕ) (positive : 0 < m)
      (identification : HatIdentification ρ K K₀ hK I hI (suzukiNatural m))
  | alternatingFive
      (identification : HatIdentification ρ K K₀ hK I hI alternatingFiveNatural)
  | binaryThree
      (identification : HatIdentification ρ K K₀ hK I hI (specialLinearNatural (k := ZMod 2) 3))

local instance fixedBinaryAlgebra (n : ℕ) :
    Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.fixedField n) := ZMod.algebra _ 2
local instance hermitianBinaryModule (n : ℕ) [NeZero n] :
    Module (ZMod 2) (OrthogonalFourMinus.FiniteModel.Space n) :=
  Module.compHom _ (algebraMap (ZMod 2) (OrthogonalFourMinus.FiniteModel.fixedField n))

/-- The genuine even-exponent orthogonal constituent, realized by Hermitian
matrices over the quadratic extension of its fixed half-field. -/
def FiveEvenOrthogonal : Prop :=
  ∃ (n : ℕ) (_ : NeZero n),
    Nonempty (HatIdentification ρ K K₀ hK I hI (SL2.BinarySmall.hermitian n))

/-- The common (5iii) clauses, with the literal IH and IK and the direct
sum in the hatted space. No equality of IK with I is silently imposed. -/
structure FiveSplit (t : D) : Prop where
  mem_T : t ∈ T
  outside : t ∉ normalizer (K : Set D)
  sum : (orbitSpan ρ ⊤ I).map (fixedSpace ρ K₀).mkQ =
    (subspaceCommutator ρ (orbitSpan ρ ⊤ I) K).map (fixedSpace ρ K₀).mkQ ⊔
    (rightConjugate ρ (subspaceCommutator ρ (orbitSpan ρ ⊤ I) K) t).map
      (fixedSpace ρ K₀).mkQ
  disjoint : Disjoint
    ((subspaceCommutator ρ (orbitSpan ρ ⊤ I) K).map (fixedSpace ρ K₀).mkQ)
    ((rightConjugate ρ (subspaceCommutator ρ (orbitSpan ρ ⊤ I) K) t).map
      (fixedSpace ρ K₀).mkQ)
  centralizer : subspaceCommutator ρ (orbitSpan ρ ⊤ I) K =
    orbitSpan ρ ⊤ I ⊓ fixedSpace ρ (K.conjBy t⁻¹)

/-- The centralizer-action clause in (5iiic), on the actual action image.
The two-residual is internal to that image. -/
def FiveCentralizerAction : Prop :=
  let IH := orbitSpan ρ ⊤ I
  let A := restrictedSubgroup ρ IH (centralizer (K₀ : Set D))
  Nonempty (pResidual 2 A ≃* Multiplicative (ZMod 5)) ∨
    Nonempty (pResidual 2 A ≃* Multiplicative (Fin 2 → ZMod 5))

/-- The five complete module rows of F.9.18(5). Natural and even-orthogonal
constituents remain separate subalternatives of (iiia). -/
inductive FiveAlternatives : Prop
  | orthogonal (F : Type) [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
      (n : ℕ) (positive : 0 < n) (card : Nat.card F = 2 ^ n)
      (component : K ≃* PSL(2,F))
      (invariant : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ I)
      (identification : LiteralIdentification ρ K₀ I hI (omegaNatural (F := F)))
  | tensor
      (component : K ≃* PSL(3,ZMod 2))
      (invariant : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ I)
      (identification : LiteralIdentification ρ K₀ I hI binaryThreeTensor)
  | constituent (t : D) (split : FiveSplit ρ K K₀ T I t)
      (first : (subspaceCommutator ρ (orbitSpan ρ ⊤ I) K).map (fixedSpace ρ K₀).mkQ =
        I.map (fixedSpace ρ K₀).mkQ)
      (module_case : FiveNatural ρ K K₀ hK I hI ∨ FiveEvenOrthogonal ρ K K₀ hK I hI)
  | twoBinaryThree (t s : D) (split : FiveSplit ρ K K₀ T I t)
      (component : K ≃* PSL(3,ZMod 2))
      (mem_T : s ∈ T) (normalizes : s ∈ normalizer (K : Set D))
      (moves : s ∉ subspaceStabilizer ρ I)
      (sum : subspaceCommutator ρ (orbitSpan ρ ⊤ I) K = I ⊔ rightConjugate ρ I s)
      (disjoint : Disjoint I (rightConjugate ρ I s))
      (dimension : Module.finrank (ZMod 2) I = 3)
  | fourBinaryThree (t : D) (split : FiveSplit ρ K K₀ T I t)
      (component : K ≃* PSL(3,ZMod 2))
      (invariant : K ≤ subspaceStabilizer ρ (subspaceCommutator ρ (orbitSpan ρ ⊤ I) K))
      (identification : LiteralIdentification ρ K
        (subspaceCommutator ρ (orbitSpan ρ ⊤ I) K) invariant
        (fourCopies (specialLinearNatural (k := ZMod 2) 3)))
      (centralizer_action : FiveCentralizerAction ρ K₀ I)

/-- The full earlier conclusion supplied by the F.9.18 owner. Its proof,
including the source coset-geometry hypotheses, is not asserted here. -/
structure FullFiveConclusion : Prop where
  component : FiveComponentList K
  alternatives : FiveAlternatives ρ K K₀ T hK I hI

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
