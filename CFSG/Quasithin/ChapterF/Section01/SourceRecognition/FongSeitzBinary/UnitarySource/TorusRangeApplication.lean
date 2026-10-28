module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.ActorCartanApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FullTorus

/-!
# Full U4 torus, Borel and endpoint placements on the original quotient

The intrinsic scalar map covers the true panel kernel, and the aligned
SL2 torus covers the remaining Cartan action. Hence the torus already
constructed in CartanApplication equals the entire B ∩ N. Its tensor
roots generate U; consequently the Borel is the full source Borel and
adjoining each common Weyl lift gives the actual oriented endpoint.

The Cartan-order and Frattini premises in this stable tensor interface
are supplied from original actor quotient maps by
ActorCartanApplication.marked_four_actor_cartan_cards. That theorem
preserves both field orders without assuming their identification.
Remainder containment, the irreducible core action, and the genuine
same-core tensor realization remain explicit source obligations, with
the earlier structural producer qt-dgs85-quadrangle-structure. Tensor
equivariance, compatible labels and remaining Weyl laws remain with
qt-dgs85-unitary-source-recognition. No full recognition is asserted.

Source: Fong--Seitz II (8B), pp.201--202, and I (6A)(b), pp.37--38.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MonoidAlgebra MatrixGroups IsMulCommutative
open Theory.PSL2.SemilinearCoverage
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Representation.OrthogonalFourMinus
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource.FourCartanSource
variable {G E : Type*} [Group G] [Field E] [Finite E] [CharP E 2]
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (Q : SourceQuotient L S) (split : SplitData Q.tits) (i : Fin 2)
variable (hm : rotationOrder Q = 4)

variable (hV : simpleRemainder Q split (1-i) ≤ HexagonStructure.localKernel Q (1-i))
variable (μ : HexagonStructure.localGroup Q split (1-i) ≃* PSL(2,E))

local instance : IsElementaryAbelian 2
    ((simpleRemainder Q split (1-i)) ⧸ frattini (simpleRemainder Q split (1-i))) :=
  coreFrattini_elementary Q split (1-i)

local instance : CommGroup
    ((simpleRemainder Q split (1-i)) ⧸ frattini (simpleRemainder Q split (1-i))) := inferInstance
local instance : AddCommGroup (CoreSpace Q split (1-i)) := inferInstance
local instance : Module (ZMod 2) (CoreSpace Q split (1-i)) :=
  IsElementaryAbelian.isVectorSpace 2

variable [Representation.IsIrreducible (coreActorRepresentation Q split (1-i) hV)]
local instance : Field (CoreEnd Q split (1-i) hV) := inferInstance

variable (h : HypothesisF11 L S) (n : ℕ) (hn : 0 < n)
variable (hcard : Nat.card (coreCartan Q (1-i)) = 2^n-1)
variable (hphi : frattini (simpleRemainder Q split (1-i)) = ⊥)
variable (σ : E ≃+* E) (hσ : Function.Involutive σ)
variable (hq : Nat.card (UnitaryFourSylow.FixedField E σ) = 2^n)

local instance : Field (CoreCoefficientField Q split (1-i) hV n) := inferInstance
local instance : Module (CoreCoefficientField Q split (1-i) hV n)
    (coreActorRepresentation Q split (1-i) hV).asModule :=
  coreCoefficientModule Q split (1-i) hV n
local instance : Module (UnitaryFourSylow.FixedField E σ) (FourTensor.Core E σ hσ) :=
  inferInstance

local instance : RingHomInvPair
    (coefficients Q split i hV h n hn hcard σ hq).toRingHom
    (coefficients Q split i hV h n hn hcard σ hq).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (coefficients Q split i hV h n hn hcard σ hq)
local instance : RingHomInvPair
    (coefficients Q split i hV h n hn hcard σ hq).symm.toRingHom
    (coefficients Q split i hV h n hn hcard σ hq).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (coefficients Q split i hV h n hn hcard σ hq)

variable (ψ : FourTensor.Core E σ hσ ≃ₛₗ[(coefficients Q split i hV h n hn hcard σ hq).toRingHom]
  (coreActorRepresentation Q split (1-i) hV).asModule)


local notation "η" => coefficients Q split i hV h n hn hcard σ hq
local notation "rSource" => roots Q split i hm hV μ h n hn hcard hphi σ hσ hq ψ
local notation "hSource" => cartan Q split i hm hV μ h n hn hcard σ hq

/-- The constructed torus is the entire original Cartan, not merely a subgroup. -/
theorem cartan_range : (hSource).range = Q.tits.B ⊓ Q.tits.N :=
  intrinsicFourCartan_range Q split (1-i) hV μ (reflection Q split i hm)
    n hn (MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h (1-i))
    hcard σ η

/-- The same positive root maps and torus generate the full Borel. -/
theorem borel_eq : (rSource).borel hSource = Q.tits.B := by
  change (rSource).generated ⊔ (hSource).range = Q.tits.B
  rw [roots_generate,cartan_range]
  exact split.factorization

/-- The small-field point endpoint retains its original orientation. -/
theorem point_eq : (rSource).borel hSource ⊔ closure
    {((quadrangleLifts Q split hm i).t : (generated L S) ⧸ Q.D)} =
      Q.tits.standardParabolic {Q.simple i} := by
  rw [borel_eq]
  exact (MarkedWeyl.Lifts.simple_parabolic Q i _ (quadrangleLifts Q split hm i).t_class).symm

/-- The large-field plane endpoint uses the same full Borel and quotient. -/
theorem plane_eq : (rSource).borel hSource ⊔ closure
    {((quadrangleLifts Q split hm i).s : (generated L S) ⧸ Q.D)} =
      Q.tits.standardParabolic {Q.simple (1-i)} := by
  rw [borel_eq]
  exact (MarkedWeyl.Lifts.simple_parabolic Q (1-i) _ (quadrangleLifts Q split hm i).s_class).symm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource.FourCartanSource
