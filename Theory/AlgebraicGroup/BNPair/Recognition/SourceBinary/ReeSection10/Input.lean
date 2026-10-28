module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SixH
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiRootLayers
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.RootReflections
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceSigned
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceNormalizer
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.GlobalRealizations

/-!
# Literal input for the Fong--Seitz Section 10 construction

`ReeSixHData` is the source-side contract for the octagonal reconstruction.
It is deliberately stated on the same `MarkedQuotient Q` and `SplitData`
used by the earlier source arguments.  The two rank-one equivalences, their
whole Borel normalizer maps, the actual root reflections, the common-field
identification, the Cartan separation and the two Section 10 relation
packages remain explicit fields.  In particular this is not a wrapper around
`RootData` or a tag identifying the quotient with a Ree model.

The relation fields state the displayed (10.2)--(10.3) subgroup equalities,
including the ordered product in (10.3)(i), both center identifications in
(10.3)(iii), and their actual `N`-conjugates. These remain preceding source
inputs, rather than consequences of a desired coordinate presentation.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}

/-- The source root and its right-conjugate notation used in (10.2)--(10.3).
These definitions keep the paper's `Uᵢʷ` convention on the marked quotient. -/
def U (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2) :
    Subgroup (X ⧸ Q.D) := simpleRoot Q split i

def Uat (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
    (w : Weyl Q) : Subgroup (X ⧸ Q.D) := rootAt Q split i w

def nConj {Q : MarkedQuotient P} (A : Subgroup (X ⧸ Q.D)) (n : Q.tits.N) : Subgroup (X ⧸ Q.D) :=
  rightConjugate A (n : X ⧸ Q.D)

def omega {Q : MarkedQuotient P} (A : Subgroup (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D) := omegaOneAmbient A

def phi {Q : MarkedQuotient P} (A : Subgroup (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D) :=
  (frattini A).map A.subtype

/-- The center of a source subgroup, embedded back in the same quotient. -/
def zeta {Q : MarkedQuotient P} (A : Subgroup (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D) :=
  (center A).map A.subtype

/-! The explicit source-level commutator and Frattini content retained from
Fong--Seitz (10.2)--(10.3).  Every clause is quantified over the actual
normalizer `N`; no Weyl-class equality is substituted for the source relation.
The superscripts are right-conjugation words, with source `s₁,s₂` represented
by `Q.simple 0,Q.simple 1`. In particular the target in (10.2)(ii) is
`U₁^s₂`, and the second commutator factor in (10.2)(iii) is a linear root.
-/
structure SixHRelations (Q : MarkedQuotient P) (split : SplitData Q.tits) where
  ten_two_i : ∀ n : Q.tits.N,
    ⁅nConj (U Q split 0) n,
      nConj (Uat Q split 0 (Q.simple 1 * Q.simple 0)) n⁆ = ⊥
  ten_two_ii_left : ∀ n : Q.tits.N,
    ⁅nConj (U Q split 1) n,
      nConj (Uat Q split 1 (Q.simple 0 * Q.simple 1)) n⁆ =
      nConj (Uat Q split 0 (Q.simple 1)) n
  ten_two_ii_right : ∀ n : Q.tits.N,
    ⁅nConj (omega (U Q split 1)) n,
      nConj (Uat Q split 1 (Q.simple 0 * Q.simple 1)) n⁆ = ⊥
  ten_two_iii_left : ∀ n : Q.tits.N,
    ⁅nConj (U Q split 1) n,
      nConj (Uat Q split 0
        (Q.simple 1 * Q.simple 0 * Q.simple 1)) n⁆ =
      nConj (omega (Uat Q split 1 (Q.simple 0 * Q.simple 1))) n
  ten_two_iii_right : ∀ n : Q.tits.N,
    ⁅nConj (omega (U Q split 1)) n,
      nConj (Uat Q split 0
        (Q.simple 1 * Q.simple 0 * Q.simple 1)) n⁆ = ⊥
  ten_two_iv_left : ∀ n : Q.tits.N,
    ⁅nConj (U Q split 0) n,
      nConj (Uat Q split 0
        (Q.simple 1 * Q.simple 0 * Q.simple 1)) n⁆ = ⊥
  ten_two_iv_right : ∀ n : Q.tits.N,
    ⁅nConj (U Q split 1) n,
      nConj (Uat Q split 1
        (Q.simple 0 * Q.simple 1 * Q.simple 0)) n⁆ = ⊥
  ten_two_v : ∀ n : Q.tits.N,
    ⁅nConj (omega (U Q split 1)) n,
      nConj (Uat Q split 0 (Q.simple 1 * Q.simple 0)) n⁆ ≤
      nConj (omega (Uat Q split 1 (Q.simple 0 * Q.simple 1))) n
  ten_three_frattini : ∀ n : Q.tits.N,
    ⁅nConj (simpleRemainder Q split 1) n,
      nConj (simpleRemainder Q split 1) n⁆ =
      phi (nConj (simpleRemainder Q split 1) n)
  ten_three_product : ∀ n : Q.tits.N,
    (phi (nConj (simpleRemainder Q split 1) n) : Set (X ⧸ Q.D)) =
      (nConj (omega (Uat Q split 1 (Q.simple 0 * Q.simple 1))) n : Set (X ⧸ Q.D)) *
      (nConj (Uat Q split 0 (Q.simple 1 * Q.simple 0 * Q.simple 1)) n : Set (X ⧸ Q.D)) *
      (nConj (omega (Uat Q split 1 (Q.simple 0 * Q.simple 1 * Q.simple 0))) n : Set (X ⧸ Q.D)) *
      (nConj (Uat Q split 0 (Q.simple 1 * Q.simple 0)) n : Set (X ⧸ Q.D)) *
      (nConj (omega (Uat Q split 1 (Q.simple 0))) n : Set (X ⧸ Q.D))
  ten_three_frattini_square : ∀ n : Q.tits.N,
    phi (phi (nConj (simpleRemainder Q split 1) n)) = ⊥
  ten_three_center : ∀ n : Q.tits.N,
    ⁅phi (nConj (simpleRemainder Q split 1) n),
      nConj (simpleRemainder Q split 1) n⁆ =
      omega (nConj (Uat Q split 1 (Q.simple 0 * Q.simple 1 * Q.simple 0)) n)
  ten_three_center_remainder : ∀ n : Q.tits.N,
    omega (nConj (Uat Q split 1 (Q.simple 0 * Q.simple 1 * Q.simple 0)) n) =
      zeta (nConj (simpleRemainder Q split 1) n)
  ten_three_center_unipotent : ∀ n : Q.tits.N,
    zeta (nConj (simpleRemainder Q split 1) n) = zeta (nConj split.U n)

/-- The literal rank-one and (6H) input retained by Section 10.

The `relations` field is the source-level subgroup package, rather than
desired presentation data.  This keeps the construction honest: a later
owner must provide the printed relations and their transport by the actual
normalizer before forming any charts.
-/
structure ReeSixHData (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (n m : ℕ) where
  rotation_eight : rotationOrder Q = 8
  linear_degree_odd : Odd n
  linear : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n
  linearSylow : Sylow 2 (PSL2BinaryMatrixGroup n)
  linearBorel : (quotientBorel Q 0).map linear.toMonoidHom =
    normalizer (linearSylow : Set (PSL2BinaryMatrixGroup n))
  suzuki : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m
  suzukiBorel : (quotientBorel Q 1).map suzuki.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m))
  reflections : ∀ i, Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource.RootReflection Q split i
  common_field : n = 2 * m + 1
  hcore : Q.tits.B.normalCore = ⊥
  cartan_card : Nat.card (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) =
    (2 ^ (2 * m + 1) - 1) ^ 2
  independent_root_centralizer :
    ((Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) ⊓
      centralizer (simpleRoot Q split 0 : Set (X ⧸ Q.D))) ⊓
      centralizer (simpleRoot Q split 1 : Set (X ⧸ Q.D)) = ⊥
  panel_kernel_centralizer : ∀ i,
    ((Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) ⊓
      embeddedPanelKernel Q i) ≤
      centralizer (rankOneRootGroup Q split i : Set (X ⧸ Q.D))
  relations : SixHRelations Q split

end Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
