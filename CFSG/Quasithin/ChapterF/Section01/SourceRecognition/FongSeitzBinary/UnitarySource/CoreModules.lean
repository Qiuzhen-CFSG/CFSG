module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorPanels
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.CoreField
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.Generation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MarkedLocal

/-!
# Source core modules and their original quotient equations

Hypothesis F.1.1 supplies local characteristic two at both marked endpoints.
It therefore makes the constructed action of H ∩ Kᵢ faithful on the literal
Frattini section of U ∩ U^s, with no perfect-factor hypothesis. The actor's
double transitivity is applied to representatives in the original endpoint.
The conjugation formulas below use the actual Q.q on generated L S.

With the earlier-source remainder containment and H Rᵢ irreducibility,
the same section constructs the finite scalar field and its faithful
Cartan embedding. Its scalar equation retains the original quotient
representatives. These two premises still belong to
qt-dgs85-unitary-source-recognition; this is not completed unitary recognition.
The dimensions, natural/tensor realizations, common-field comparison,
remaining U5 equations and full torus/Weyl markings remain to be supplied.

Source: Fong--Seitz I (2B), (3B), (6A), pp.9,13,37--38;
II (8B)--(8C), pp.201--203; AS F.1.1; DGS Theorem D, p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The genuine original hypotheses discharge faithfulness at both endpoints,
including when the marking comes from the geometric quotient. -/
theorem marked_core_representation_injective
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2) :
    Function.Injective (coreFrattiniRepresentation Q split i) :=
  coreFrattiniRepresentation_injective Q split i (MarkedLocal.parabolic_core_selfCentralizing Q e h i)

variable (Q : SourceQuotient L S) (split : SplitData Q.tits) (i : Fin 2)

private theorem original_endpoint_quotient (g : parabolic L S i) :
    Q.q ⟨g,parabolic_le_generated i g.property⟩ =
      (MarkedLocal.endpoint Q (originalMarkedIso Q) i g : (generated L S) ⧸ Q.D) := by
  fin_cases i
  · exact (originalMarkedIso_left_apply Q g).symm
  · exact (originalMarkedIso_right_apply Q g).symm

/-- The actor's two-point transport is performed by an actual original endpoint
representative; the root-actor membership uses its literal Q.q-image. -/
theorem original_actor_pair_transport
    (a b c d : Panel Q i) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : parabolic L S i,
      Q.q ⟨g,parabolic_le_generated i g.property⟩ ∈ rootActor Q split i ∧
      MarkedLocal.endpoint Q (originalMarkedIso Q) i g • a = c ∧
      MarkedLocal.endpoint Q (originalMarkedIso Q) i g • b = d := by
  obtain ⟨r,ha,hb⟩ := MulAction.is_two_pretransitive_iff.mp
    (panelActor_two_pretransitive Q split i) hab hcd
  let g := (MarkedLocal.endpoint Q (originalMarkedIso Q) i).symm r.val
  have he : MarkedLocal.endpoint Q (originalMarkedIso Q) i g = r.val :=
    MulEquiv.apply_symm_apply _ _
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [original_endpoint_quotient Q i g,he]
    exact r.property
  · rw [he]
    exact ha
  · rw [he]
    exact hb

/-- The constructed binary action retains the original representatives and
both actual quotient maps, including the Frattini quotient. -/
theorem original_core_representation_quotient
    (a v : generated L S) (ha : Q.q a ∈ coreCartan Q i)
    (hv : Q.q v ∈ simpleRemainder Q split i) :
    ∃ w : simpleRemainder Q split i,
      (w : (generated L S) ⧸ Q.D) = Q.q (a*v*a⁻¹) ∧
      coreFrattiniRepresentation Q split i ⟨Q.q a,ha⟩
        (Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) ⟨Q.q v,hv⟩)) =
        Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) w) := by
  let w := coreCartanAction Q split i ⟨Q.q a,ha⟩ ⟨Q.q v,hv⟩
  refine ⟨w, ?_, ?_⟩
  · rw [coreCartanAction_apply, map_mul,map_mul,map_inv]
  · rw [coreFrattiniRepresentation_apply,toMul_ofMul,coreFrattiniAction_mk]

variable (hV : simpleRemainder Q split i ≤ HexagonStructure.localKernel Q i)

/-- The scalar embedding into the commuting ring is constructed from the
actual core action. Earlier-source irreducibility will make this ring a field. -/
theorem original_core_scalar_injective (h : HypothesisF11 L S) :
    Function.Injective (coreScalarUnits Q split i hV) :=
  coreScalarUnits_injective Q split i hV
    (MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h i)

/-- Source conjugation is the action of the constructed scalar operators
on this SAME core. Row-specific irreducibility and dimensions are still needed
to identify the coefficient field. -/
theorem original_core_scalar_quotient
    (a v : generated L S) (ha : Q.q a ∈ coreCartan Q i)
    (hv : Q.q v ∈ simpleRemainder Q split i) :
    ∃ w : simpleRemainder Q split i,
      (w : (generated L S) ⧸ Q.D) = Q.q (a*v*a⁻¹) ∧
      (coreActorRepresentation Q split i hV).asModuleEquiv
        ((coreScalarUnits Q split i hV ⟨Q.q a,ha⟩ : CoreEnd Q split i hV) •
          (coreActorRepresentation Q split i hV).asModuleEquiv.symm
            (Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) ⟨Q.q v,hv⟩))) =
        Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split i)) w) := by
  obtain ⟨w,hw,he⟩ := original_core_representation_quotient Q split i a v ha hv
  refine ⟨w,hw,?_⟩
  rw [coreScalarUnits_smul,LinearEquiv.apply_symm_apply]
  exact he

variable [Representation.IsIrreducible (coreActorRepresentation Q split i hV)]

/-- Fong--Seitz's scalar-order divisibility, with the field constructed as
the commuting ring and local characteristic two discharged from F.1.1. -/
theorem original_core_scalar_field_order (h : HypothesisF11 L S) :
    Nat.card (coreCartan Q i) ∣ Nat.card (CoreEnd Q split i hV) - 1 :=
  coreCartan_card_dvd_field_sub_one Q split i hV
    (MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h i)

include split hV in
/-- Cyclicity is obtained from the same faithful scalar action. -/
theorem original_core_cartan_isCyclic (h : HypothesisF11 L S) : IsCyclic (coreCartan Q i) :=
  coreCartan_isCyclic Q split i hV
    (MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h i)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
