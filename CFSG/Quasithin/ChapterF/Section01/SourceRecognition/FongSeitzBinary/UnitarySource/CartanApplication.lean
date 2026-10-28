module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FourCartan
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorScalars
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CartanPinning
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.ActorWeylApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.CoefficientApplication

/-!
# Constructed U₄ torus and linear Weyl equations on the original quotient

Align the entire SL₂ actor with the reflection from the common source
Weyl section. Choose coefficients by their proved order and construct the
scalar lift from the actual Cartan kernel. A genuine tensor intertwiner
on the same original Frattini section now supplies the four root maps,
all positive relations, all exact torus weights and the linear Weyl
relations in the conventions of FourPresentation.parameters. The torus
lies in the actual B ∩ N. The roots generate the literal original S image,
so four_originalS_collected applies and both Weyl lifts generate all Y.
Either endpoint orientation is retained, including the smallest fields.

This is an intermediate source construction. Remainder containment, the
Cartan-kernel order, triviality of this remainder's Frattini subgroup and
the tensor realization are still explicit source inputs. Their original
unitary discharge remains with qt-dgs85-unitary-source-recognition; the
local linear-actor, elementary-remainder and irreducible-action producers
are QuadraticLinearActors.marked_quadratic_linear_sixA and
QuadraticIrreducibility.original_quadratic_remainder_irreducible, owned by
qt-dgs85-quadrangle-structure. The other endpoint's compatible field labels,
nonlinear Weyl equations and the U₅ source branch are not proved here.
No full unitary marking or original-source recognition is asserted.

Source: Fong--Seitz I (6A), pp.37--38; II (8B), pp.201--202;
AS F.1.1; DGS Theorem D, p.224.
-/

@[expose] public noncomputable section
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

def reflection : HexagonStructure.RootReflection Q split (1-i) where
  val := (quadrangleLifts Q split hm i).s
  class_eq := (quadrangleLifts Q split hm i).s_class
  mem_rankOne := (quadrangleLifts_actor Q split hm i).1

variable (hV : simpleRemainder Q split (1-i) ≤ HexagonStructure.localKernel Q (1-i))
variable (μ : HexagonStructure.localGroup Q split (1-i) ≃* PSL(2,E))

def actor : SL2 E →* ((generated L S) ⧸ Q.D) :=
  GTwoSource.alignedPinningHom Q split (1-i) hV μ (reflection Q split i hm)

def coreActorHom : SL2 E →* coreActor Q split (1-i) :=
  (inclusion le_sup_right).comp
    (GTwoSource.alignedPinning Q split (1-i) hV μ (reflection Q split i hm)).toMonoidHom

@[simp] theorem coreActorHom_coe (g : SL2 E) :
    (coreActorHom Q split i hm hV μ g : (generated L S) ⧸ Q.D) =
      actor Q split i hm hV μ g := rfl

theorem actor_weyl : actor Q split i hm hV μ (Theory.PSL2.SemilinearCoverage.weyl E) =
    ((quadrangleLifts Q split hm i).s : (generated L S) ⧸ Q.D) :=
  GTwoSource.alignedPinningHom_weyl Q split (1-i) hV μ _

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

def coefficients : UnitaryFourSylow.FixedField E σ ≃+*
    CoreCoefficientField Q split (1-i) hV n :=
  coreCoefficientFieldEquiv Q split (1-i) hV n hn
    (MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h (1-i))
    hcard σ hq

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
local notation "eTensor" => intrinsicTensorRealization Q split (1-i) hV n hphi σ hσ η ψ
local notation "vTensor" => tensorEmbedding Q split σ hσ (1-i) eTensor
local notation "lActor" => actor Q split i hm hV μ
local notation "cScalar" => intrinsicScalar Q split (1-i) hV n hn
  (MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h (1-i)) hcard σ η

-- The missing source module classification is an intertwiner on this same core.
variable (hlinear : ∀ g v, ψ (hermitianAction (FourTensor.conjugation E σ) hσ g v) =
  coreCoefficientRepresentation Q split (1-i) hV n (coreActorHom Q split i hm hV μ g) (ψ v))

theorem scalarActor_commute (a : (UnitaryFourSylow.FixedField E σ)ˣ) (g : SL2 E) :
    Commute (cScalar a) (lActor g) :=
  intrinsicScalar_commute Q split (1-i) hV n hn
    (MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h (1-i))
    hcard σ η a (coreActorHom Q split i hm hV μ g)

def cartan : FourWeyl.torusParameters E σ →* ((generated L S) ⧸ Q.D) :=
  FourCartan.hom E σ lActor cScalar (scalarActor_commute Q split i hm hV μ h n hn hcard σ hq)

theorem cartan_le : (cartan Q split i hm hV μ h n hn hcard σ hq).range ≤ Q.tits.B ⊓ Q.tits.N := by
  rintro x ⟨p,rfl⟩
  change cScalar (FourCartan.determinant E σ p) *
    lActor (Theory.PSL2.SemilinearCoverage.tor (FourCartan.coroot E σ p)) ∈ _
  apply Subgroup.mul_mem
  · exact (intrinsicScalar_mem Q split (1-i) hV n hn
      (MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h (1-i))
      hcard σ η _).1
  · exact GTwoSource.alignedTorus_mem_cartan Q split (1-i) hV μ (reflection Q split i hm) _

include hlinear in
theorem tensor_equivariant (g : SL2 E) (v : FourTensor.Core E σ hσ) :
    lActor g * vTensor (.ofAdd v) * (lActor g)⁻¹ =
      vTensor (.ofAdd (hermitianAction (FourTensor.conjugation E σ) hσ g v)) :=
  intrinsicTensorRealization_actor Q split (1-i) hV n hphi σ hσ η ψ
    (coreActorHom Q split i hm hV μ) hlinear g v

def roots := FourTensor.roots E σ hσ lActor vTensor

theorem roots_generate :
    (roots Q split i hm hV μ h n hn hcard hphi σ hσ hq ψ).generated = split.U := by
  apply four_generated_eq_unipotent Q split σ hσ lActor vTensor (1-i)
  · exact GTwoSource.alignedSimpleParameter_range Q split (1-i) hV μ (reflection Q split i hm)
  · exact tensorEmbedding_range Q split σ hσ (1-i) eTensor

include hlinear in
theorem positive_relations : FourPositive.Relations E σ hσ
    (roots Q split i hm hV μ h n hn hcard hphi σ hσ hq ψ) :=
  FourTensor.relations E σ hσ lActor vTensor
    (tensor_equivariant Q split i hm hV μ h n hn hcard hphi σ hσ hq ψ hlinear)

include hlinear in
theorem torus_laws : (roots Q split i hm hV μ h n hn hcard hphi σ hσ hq ψ).TorusLaws
    (cartan Q split i hm hV μ h n hn hcard σ hq) :=
  FourCartan.torusLaws E σ hσ lActor cScalar
    (scalarActor_commute Q split i hm hV μ h n hn hcard σ hq) vTensor
    (tensor_equivariant Q split i hm hV μ h n hn hcard hphi σ hσ hq ψ hlinear)
    (intrinsicTensorRealization_scalar Q split (1-i) hV n hn
      (MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h (1-i))
      hcard hphi σ hσ η ψ)

include hlinear in
/-- Literal application to the original quotient map and original Sylow subgroup. -/
theorem originalS_collected (x : (generated L S) ⧸ Q.D)
    (hx : x ∈ (S.subgroupOf (generated L S)).map Q.q) :
    ∃ a d c b, x = (roots Q split i hm hV μ h n hn hcard hphi σ hσ hq ψ).word a d c b :=
  UnitaryPresentation.four_originalS_collected h Q split σ hσ _
    (positive_relations Q split i hm hV μ h n hn hcard hphi σ hσ hq ψ hlinear)
    (roots_generate Q split i hm hV μ h n hn hcard hphi σ hσ hq ψ).ge x hx

theorem full_generate : ReflectionLaws.fullGenerated
    (roots Q split i hm hV μ h n hn hcard hphi σ hσ hq ψ)
    (cartan Q split i hm hV μ h n hn hcard σ hq)
    ((quadrangleLifts Q split hm i).s : (generated L S) ⧸ Q.D)
    ((quadrangleLifts Q split hm i).t : (generated L S) ⧸ Q.D) = ⊤ :=
  marked_positive_fullGenerated Q split hm (originalMarkedIso Q) h i _ _
    (roots_generate Q split i hm hV μ h n hn hcard hphi σ hσ hq ψ)

local notation "rSource" => roots Q split i hm hV μ h n hn hcard hphi σ hσ hq ψ
local notation "hSource" => cartan Q split i hm hV μ h n hn hcard σ hq
local notation "sSource" => ((MarkedWeyl.Lifts.s (quadrangleLifts Q split hm i)) : (generated L S) ⧸ Q.D)

include hlinear in
/-- The four exact weights required by FourPresentation.parameters. -/
theorem torus_parameters (p : FourWeyl.torusParameters E σ) :
    (∀ a : E, hSource p * (rSource).A (.ofAdd a) * (hSource p)⁻¹ =
      (rSource).A (.ofAdd (((p.val.1:E)/(p.val.2:E))*a))) ∧
    (∀ d : UnitaryFourSylow.FixedField E σ,
      hSource p * (rSource).D (.ofAdd d) * (hSource p)⁻¹ =
      (rSource).D (.ofAdd (FourPositive.normParameter E σ hσ p.val.1 d))) ∧
    (∀ c : E, hSource p * (rSource).C (.ofAdd c) * (hSource p)⁻¹ =
      (rSource).C (.ofAdd (((p.val.1:E)*σ (p.val.2:E))*c))) ∧
    (∀ b : UnitaryFourSylow.FixedField E σ,
      hSource p * (rSource).B (.ofAdd b) * (hSource p)⁻¹ =
      (rSource).B (.ofAdd (FourPositive.normParameter E σ hσ p.val.2 b))) := by
  have he := tensor_equivariant Q split i hm hV μ h n hn hcard hphi σ hσ hq ψ hlinear
  have hs := intrinsicTensorRealization_scalar Q split (1-i) hV n hn
    (MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h (1-i))
    hcard hphi σ hσ η ψ
  exact ⟨FourCartan.hom_A E σ hσ lActor cScalar
      (scalarActor_commute Q split i hm hV μ h n hn hcard σ hq) vTensor p,
    FourCartan.hom_D E σ hσ lActor cScalar
      (scalarActor_commute Q split i hm hV μ h n hn hcard σ hq) vTensor he hs p,
    FourCartan.hom_C E σ hσ lActor cScalar
      (scalarActor_commute Q split i hm hV μ h n hn hcard σ hq) vTensor he hs p,
    FourCartan.hom_B E σ hσ lActor cScalar
      (scalarActor_commute Q split i hm hV μ h n hn hcard σ hq) vTensor he hs p⟩

include hlinear in
theorem weyl_B (b : UnitaryFourSylow.FixedField E σ) :
    sSource * (rSource).B (.ofAdd b) * sSource = (rSource).D (.ofAdd b) := by
  have he := FourCartan.weyl_B E σ hσ lActor vTensor
    (tensor_equivariant Q split i hm hV μ h n hn hcard hphi σ hσ hq ψ hlinear) b
  simpa only [roots,actor_weyl] using he

include hlinear in
theorem weyl_D (d : UnitaryFourSylow.FixedField E σ) :
    sSource * (rSource).D (.ofAdd d) * sSource = (rSource).B (.ofAdd d) := by
  have hs : sSource * sSource = 1 := by
    have he := congrArg (fun z : Q.tits.N => (z : (generated L S) ⧸ Q.D))
      (quadrangleLifts_equations Q split hm i).1
    simpa only [coe_pow,coe_one,pow_two,coe_mul] using he
  rw [← weyl_B Q split i hm hV μ h n hn hcard hphi σ hσ hq ψ hlinear d]
  calc
    _ = (sSource*sSource) * (rSource).B (.ofAdd d) * (sSource*sSource) := by
      simp only [mul_assoc]
    _ = _ := by rw [hs,one_mul,mul_one]

include hlinear in
theorem weyl_C (c : E) :
    sSource * (rSource).C (.ofAdd c) * sSource = (rSource).C (.ofAdd (σ c)) := by
  have he := FourCartan.weyl_C E σ hσ lActor vTensor
    (tensor_equivariant Q split i hm hV μ h n hn hcard hphi σ hσ hq ψ hlinear) c
  simpa only [roots,actor_weyl] using he

theorem weyl_cartan (p : FourWeyl.torusParameters E σ) :
    sSource * hSource p * sSource = hSource (FourCells.swapParameter E σ p) := by
  have he := FourCartan.weyl_hom E σ lActor cScalar
    (scalarActor_commute Q split i hm hV μ h n hn hcard σ hq) p
  simpa only [cartan,actor_weyl] using he

theorem weyl_A (a : E) (ha : a ≠ 0) :
    sSource * (rSource).A (.ofAdd a) * sSource =
      (rSource).A (.ofAdd a⁻¹) * hSource (FourBruhat.aTorus E σ a ha) *
        sSource * (rSource).A (.ofAdd a⁻¹) := by
  have he := FourCartan.weyl_A E σ hσ lActor cScalar
    (scalarActor_commute Q split i hm hV μ h n hn hcard σ hq) vTensor a ha
  simpa only [roots,cartan,actor_weyl] using he


end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource.FourCartanSource
