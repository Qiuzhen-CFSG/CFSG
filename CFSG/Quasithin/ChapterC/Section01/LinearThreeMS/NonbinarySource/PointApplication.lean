module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.ComponentDescent
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CentralSections
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NoncoreOffenders
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.FrattiniSections
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.IntrinsicCore
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.SylowSections
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.SylowInitialQuotient
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.RadicalInitial
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.DoubledRadical
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NaturalCenter
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear.Source

/-!
# Sylow-omega sections at the original Chapter 11 point

The escaping original point supplies the intrinsic MS hypotheses on LR₁.
Apply the Sylow-section theorem to its literal S'=T∩LR₁. Each of the three
nonblock module rows splits Ω₁Z(S') over its vectors in Q, Z(Q), or [Z(Q),L].
The existing point-fixer computation then identifies the two-core of the
computed section-fixer product as R₁, including at q=4.

These are applications to the actual PointModuleCases setup, retaining the
original field, quotient marking, and radical. Their section models remain
explicit. The intrinsic classification and its contrary radical inequality
must still be proved before the Chapter 11 block follows. No original
fixed-factor centrality is used.

For an abelian whole core outside field four, the intrinsic component-core
centrality and the faithful marked SL₃ action are now supplied directly by
ComponentDescent. The exceptional cover and recognition of the descended
whole module remain open.
For nonabelian Q too, the literal Z(Q) and [Z(Q),L] now have the original
faithful SL₃ action outside field four. The entire Ω₁(Z(Q)) has an FF
action through its actual centralizer quotient at every nonbinary field.
A maximum elementary subgroup of the actual Sylow T∩LR₁ now gives best
offenders simultaneously on that central omega and the initial layer, and its
whole-action image escapes the two-core. The whole central-omega and abelian
whole-core offender groups contain the original covering component, including
at field four. These supply action inputs for the remaining PointModuleCases
recognition. The literal whole Frattini quotient now has its action kernel
inside the original two-core and, outside field four, a faithful marked SL₃
representation with full displacement generation.
The actual Sylow T∩LR₁ now has the unconditional initial-factor splitting
and noncentral omega, including at field four. Its radical comparison passes
exactly to the faithful initial fixed-space action. A doubled initial section
now gives the strict inequality. If the whole commutator centralizes O₂(LR₁),
the precise PointModuleCases follow and the original escaping point is an
SL₃-even block with V=V_M. Abelianity of O₂(LR₁) suffices, also at field four.
The general noncentral whole-core branches remain open.
Source: Aschbacher--Smith C.1.34(2)--(4), printed pp.136--137, and 11.1.5,
printed pp.765--766.
-/


public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.PointApplication
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open SourceInterface
open Chapter11.ChosenNaturalSource.LocalGeometry
open Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
open Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks
open Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
  (f : InvariantFlag (.sl3 m))
  (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
local notation "P" => (((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) : Subgroup G)

include hescape

/-- The original escaping point has the literal Sylow-omega splitting in the
doubled row, including at field four. -/
theorem doubled_omega_split
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L (msQ L (f.Ri 0)) ⊥ (linearThreeActor e) ((specialLinearNatural (k := S.field.Carrier) 3).prod (specialLinearNatural (k := S.field.Carrier) 3))) :
    SourceInterface.omegaCenterIn P =
      (msQ L (f.Ri 0) ⊓ centralizer (P : Set G)) ⊔
        (SourceInterface.omegaCenterIn P ⊓ centralizer (L : Set G)) ∧
    (msQ L (f.Ri 0) ⊓ centralizer (P : Set G)) ⊓
      (SourceInterface.omegaCenterIn P ⊓ centralizer (L : Set G)) = ⊥ := by
  have h := doubled_sylow_section
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary
    (pointSylow_isSylowIn D S f) (radical_le_pointSylow D S f) e hm
  exact ⟨h.1,h.2.1⟩

/-- The actual point geometry evaluates the two-core of the section fixer.
This is the concrete comparison that the source radical inequality must
contradict; the intrinsic inequality itself is not assumed proved. -/
theorem doubled_fixer_core
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L (msQ L (f.Ri 0)) ⊥ (linearThreeActor e) ((specialLinearNatural (k := S.field.Carrier) 3).prod (specialLinearNatural (k := S.field.Carrier) 3))) :
    ((L ⊓ centralizer ((msQ L (f.Ri 0) ⊓ centralizer (P : Set G) : Subgroup G) : Set G)) ⊔
      f.Ri 0).pCoreIn 2 = f.Ri 0 := by
  rw [←doubled_sylow_centralizer
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary
    (pointSylow_isSylowIn D S f) (radical_le_pointSylow D S f) e hm]
  exact model_rows_centralizer_core D S m f e (Or.inl hm)

/-- The original escaping point has the literal Sylow-omega splitting in the
natural center row, including at field four. -/
theorem natural_center_omega_split
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L (SourceInterface.centerIn (msQ L (f.Ri 0))) ⊥ (linearThreeActor e) (specialLinearNatural (k := S.field.Carrier) 3)) :
    SourceInterface.omegaCenterIn P =
      (SourceInterface.centerIn (msQ L (f.Ri 0)) ⊓ centralizer (P : Set G)) ⊔
        (SourceInterface.omegaCenterIn P ⊓ centralizer (L : Set G)) ∧
    (SourceInterface.centerIn (msQ L (f.Ri 0)) ⊓ centralizer (P : Set G)) ⊓
      (SourceInterface.omegaCenterIn P ⊓ centralizer (L : Set G)) = ⊥ := by
  have h := natural_center_sylow_section
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary
    (pointSylow_isSylowIn D S f) (radical_le_pointSylow D S f) e hm
  exact ⟨h.1,h.2.1⟩

/-- The actual point geometry evaluates the two-core of the section fixer.
This is the concrete comparison that the source radical inequality must
contradict; the intrinsic inequality itself is not assumed proved. -/
theorem natural_center_fixer_core
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L (SourceInterface.centerIn (msQ L (f.Ri 0))) ⊥ (linearThreeActor e) (specialLinearNatural (k := S.field.Carrier) 3)) :
    ((L ⊓ centralizer ((SourceInterface.centerIn (msQ L (f.Ri 0)) ⊓ centralizer (P : Set G) : Subgroup G) : Set G)) ⊔
      f.Ri 0).pCoreIn 2 = f.Ri 0 := by
  rw [←natural_center_sylow_centralizer
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary
    (pointSylow_isSylowIn D S f) (radical_le_pointSylow D S f) e hm]
  exact model_rows_centralizer_core D S m f e (Or.inr (Or.inl hm))

/-- The original escaping point has the literal Sylow-omega splitting in the
natural center commutator row, including at field four. -/
theorem natural_center_commutator_omega_split
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L (⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆) ⊥ (linearThreeActor e) (specialLinearNatural (k := S.field.Carrier) 3)) :
    SourceInterface.omegaCenterIn P =
      (⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ ⊓ centralizer (P : Set G)) ⊔
        (SourceInterface.omegaCenterIn P ⊓ centralizer (L : Set G)) ∧
    (⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ ⊓ centralizer (P : Set G)) ⊓
      (SourceInterface.omegaCenterIn P ⊓ centralizer (L : Set G)) = ⊥ := by
  have h := natural_center_commutator_sylow_section
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary
    (pointSylow_isSylowIn D S f) (radical_le_pointSylow D S f) e hm
  exact ⟨h.1,h.2.1⟩

/-- The actual point geometry evaluates the two-core of the section fixer.
This is the concrete comparison that the source radical inequality must
contradict; the intrinsic inequality itself is not assumed proved. -/
theorem natural_center_commutator_fixer_core
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L (⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆) ⊥ (linearThreeActor e) (specialLinearNatural (k := S.field.Carrier) 3)) :
    ((L ⊓ centralizer ((⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ ⊓ centralizer (P : Set G) : Subgroup G) : Set G)) ⊔
      f.Ri 0).pCoreIn 2 = f.Ri 0 := by
  rw [←natural_center_commutator_sylow_centralizer
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary
    (pointSylow_isSylowIn D S f) (radical_le_pointSylow D S f) e hm]
  exact model_rows_centralizer_core D S m f e (Or.inr (Or.inr hm))

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.PointApplication

namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.PointApplication
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter11.ChosenNaturalSource.LocalGeometry
open Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
open Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks
open Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
  (f : InvariantFlag (.sl3 m))
  (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))

include hescape

/-- The original escaping point with abelian whole core has no intrinsic
component-core action outside the exceptional field four. -/
theorem abelian_core_centralizes_componentCore (h4 : S.field.degree ≠ 2)
    (hc : IsMulCommutative (msQ L (f.Ri 0))) :
    msQ L (f.Ri 0) ≤ centralizer (L.pCoreIn 2 : Set G) :=
  ComponentDescent.abelian_msQ_centralizes_componentCore
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary h4 hc

/-- The descended action at the original Chapter 11 point retains its full
quotient marking and actual conjugation on the entire Q. -/
theorem abelian_core_descended_action (h4 : S.field.degree ≠ 2)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hc : IsMulCommutative (msQ L (f.Ri 0))) :
    ∃ a : SL(3,S.field.Carrier) →* MulAut (msQ L (f.Ri 0)), Function.Injective a ∧
      ∀ (l : L) (x : msQ L (f.Ri 0)), (a (linearThreeActor e l) x : G) =
        l * (x : G) * (l : G)⁻¹ :=
  ComponentDescent.exists_descendedAction
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary h4 e hc

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.PointApplication

namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.PointApplication
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open SourceInterface
open Chapter11.ChosenNaturalSource.LocalGeometry
open Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
open Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks
open Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
  (f : InvariantFlag (.sl3 m))
  (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))

include hescape

/-- Nonabelian Q at the escaping point has its entire center centralized
by O₂(L), outside the exceptional field four. -/
theorem center_centralizes_componentCore (h4 : S.field.degree ≠ 2) :
    SourceInterface.centerIn (msQ L (f.Ri 0)) ≤ centralizer (L.pCoreIn 2 : Set G) :=
  CentralSections.center_centralizes_componentCore
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary h4

/-- The whole center in PointModuleCases carries the original faithful
SL₃ action, with no assumption that Q is abelian. -/
theorem center_descended_action (h4 : S.field.degree ≠ 2)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) :
    ∃ a : SL(3,S.field.Carrier) →* MulAut (SourceInterface.centerIn (msQ L (f.Ri 0))),
      Function.Injective a ∧
      ∀ (l : L) (x : SourceInterface.centerIn (msQ L (f.Ri 0))),
        (a (linearThreeActor e l) x : G) = l * (x : G) * (l : G)⁻¹ :=
  CentralSections.exists_centerAction
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary h4 e

/-- The fourth PointModuleCases row retains its literal moved-center
subgroup and its original quotient marking under descent. -/
theorem center_commutator_descended_action (h4 : S.field.degree ≠ 2)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) :
    ∃ a : SL(3,S.field.Carrier) →*
        MulAut (⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ : Subgroup G),
      Function.Injective a ∧
      ∀ (l : L) (x : (⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ : Subgroup G)),
        (a (linearThreeActor e l) x : G) = l * (x : G) * (l : G)⁻¹ :=
  CentralSections.exists_centerCommutatorAction
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary h4 e

open scoped IsMulCommutative

/-- The point's whole-core central omega has an FF action on its exact
centralizer quotient, including field four and nonabelian Q. -/
theorem coreOmega_isFF :
    let hm := point_linearThreeMSPair D S m f (point_msPair D S f hescape)
    letI := CentralSections.coreOmegaLayer_normal hm S.nonbinary
    letI := CentralSections.coreOmegaLayer_elementary (K := L) (R := f.Ri 0)
    Representation.BinaryOffender.IsFFModule (CentralSections.coreOmegaRepresentation hm S.nonbinary) :=
  CentralSections.coreOmega_isFF
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary


/-- A maximum elementary subgroup of the actual Sylow T∩LR₁ offends on
both central-omega layers and escapes the whole-section actor's two-core. -/
theorem coreOmega_sylow_bestOffenders :
    let hm := point_linearThreeMSPair D S m f (point_msPair D S f hescape)
    let J := L ⊔ f.Ri 0
    let P := ((T : Subgroup G) ⊓ J).subgroupOf J
    let E := CentralSections.coreOmegaLayer (K := L) (R := f.Ri 0)
    letI := CentralSections.coreOmegaLayer_normal hm S.nonbinary
    letI := CentralSections.coreOmegaLayer_elementary (K := L) (R := f.Ri 0)
    let q := QuotientGroup.mk' (centralizer (E : Set J))
    ∃ A ∈ Stellmacher.elementaryAbelianMaxSubgroups P,
      (¬ A ≤ pCore 2 J) ∧
      Representation.BinaryOffender.IsBestOffender (CentralSections.coreOmegaRepresentation hm S.nonbinary) (A.map q) ∧
      (¬ A.map q ≤ pCore 2 (J ⧸ centralizer (E : Set J))) ∧
      Representation.BinaryOffender.IsBestOffender (centralOmegaRepresentation L (f.Ri 0))
        (A.map (centralOmegaProjection L (f.Ri 0))) :=
  NoncoreOffenders.coreOmega_bestOffenders
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary _
    (comap_mono (radical_le_pointSylow D S f))

/-- The original point component belongs to the whole central-omega
best-offender group with no exception at field four. -/
theorem coreOmega_component_le_offenders :
    let hm := point_linearThreeMSPair D S m f (point_msPair D S f hescape)
    let J := L ⊔ f.Ri 0
    let E := CentralSections.coreOmegaLayer (K := L) (R := f.Ri 0)
    letI := CentralSections.coreOmegaLayer_normal hm S.nonbinary
    letI := CentralSections.coreOmegaLayer_elementary (K := L) (R := f.Ri 0)
    (L.subgroupOf J).map (QuotientGroup.mk' (centralizer (E : Set J))) ≤
      Representation.BinaryOffender.offenderSubgroup (CentralSections.coreOmegaRepresentation hm S.nonbinary) :=
  NoncoreOffenders.coreOmega_component_le_offenders
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary

/-- In the abelian point branch, the entire component image lies in the
best-offender group on the original whole core, including at field four. -/
theorem abelian_core_component_le_offenders (hc : IsMulCommutative (msQ L (f.Ri 0))) :
    let hm := point_linearThreeMSPair D S m f (point_msPair D S f hescape)
    let J := L ⊔ f.Ri 0
    let Q := (⁅pCore 2 J,L.subgroupOf J⁆ : Subgroup J)
    letI := component_normal hm S.nonbinary
    letI := abelian_joinCore_elementary hm S.nonbinary hc
    (L.subgroupOf J).map (QuotientGroup.mk' (centralizer (Q : Set J))) ≤
      Representation.BinaryOffender.offenderSubgroup (wholeCoreRepresentation hm S.nonbinary hc) :=
  NoncoreOffenders.abelian_core_component_le_offenders
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary hc

/-- The original point's whole Frattini action has only a two-group kernel,
including for the original field-four radical. -/
theorem frattini_action_kernel_le :
    let hm := point_linearThreeMSPair D S m f (point_msPair D S f hescape)
    (FrattiniSections.frattiniAction hm S.nonbinary).ker ≤ pCore 2 (L ⊔ f.Ri 0 : Subgroup G) :=
  FrattiniSections.frattiniAction_kernel_le
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary

/-- The entire Frattini section at the actual point retains the original
full SL₃ marking and is generated by its displacements outside field four. -/
theorem frattini_representation (h4 : S.field.degree ≠ 2)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) :
    let Q := msQ L (f.Ri 0)
    letI := FrattiniSections.frattini_elementary (K := L) (R := f.Ri 0)
    ∃ ρ : Representation (ZMod 2) SL(3,S.field.Carrier) (Additive (Q ⧸ frattini Q)),
      Function.Injective ρ ∧
      (∀ (k : L) (x x' : Q), (x' : G) = k * (x : G) * (k : G)⁻¹ →
        ρ (linearThreeActor e k) (Additive.ofMul (QuotientGroup.mk' (frattini Q) x)) =
          Additive.ofMul (QuotientGroup.mk' (frattini Q) x')) ∧
      Representation.BinaryOffender.subspaceCommutator ρ ⊤ ⊤ = ⊤ :=
  FrattiniSections.exists_frattiniRepresentation
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary h4 e

/-- The actual point component core centralizes its whole Frattini section
outside field four, without requiring the commutator core to be abelian. -/
theorem componentCore_commutator_le_frattini (h4 : S.field.degree ≠ 2) :
    ⁅L.pCoreIn 2,msQ L (f.Ri 0)⁆ ≤ frattiniIn (msQ L (f.Ri 0)) :=
  FrattiniSections.componentCore_commutator_le_frattini
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary h4


/-- The actual escaping point's commutator core is the full intrinsic O₂(L)
outside field four, without an abelianity or module-model assumption. -/
theorem core_eq_componentCore (h4 : S.field.degree ≠ 2) :
    msQ L (f.Ri 0) = L.pCoreIn 2 :=
  IntrinsicCore.msQ_eq_componentCore
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary h4

/-- The whole-core discrepancy at the actual point is confined to field four. -/
theorem degree_eq_two_of_core_ne (hne : msQ L (f.Ri 0) ≠ L.pCoreIn 2) :
    S.field.degree = 2 :=
  IntrinsicCore.degree_eq_two_of_core_ne
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary hne

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.PointApplication

namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.PointApplication
open scoped IsMulCommutative
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open SourceInterface
open Chapter11.ChosenNaturalSource.LocalGeometry
open Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
open Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks
open Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
  (f : InvariantFlag (.sl3 m))
  (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
local notation "P" => (((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) : Subgroup G)
include hescape

/-- The literal Chapter11 Sylow has its canonical initial-factor splitting
without any whole-core module premise, including at q=4. -/
theorem initial_sylowOmega_split :
    SourceInterface.omegaCenterIn P =
      (initialMoved L (f.Ri 0) ⊓ centralizer (P : Set G)) ⊔
        SourceInterface.omegaCenterIn (L ⊔ f.Ri 0) ∧
    (initialMoved L (f.Ri 0) ⊓ centralizer (P : Set G)) ⊓
      SourceInterface.omegaCenterIn (L ⊔ f.Ri 0) = ⊥ :=
  SylowInitial.sylowOmega_split_center
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary
    (pointSylow_isSylowIn D S f) (radical_le_pointSylow D S f)

/-- The original point's Sylow-omega centralizer is computed on the
initial moved module, independently of nonabelian whole-core sections. -/
theorem initial_sylow_centralizer :
    (L ⊔ f.Ri 0) ⊓ centralizer (SourceInterface.omegaCenterIn P : Set G) =
      (L ⊓ centralizer ((initialMoved L (f.Ri 0) ⊓
        centralizer (P : Set G) : Subgroup G) : Set G)) ⊔ f.Ri 0 :=
  SylowInitial.join_centralizer
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary
    (pointSylow_isSylowIn D S f) (radical_le_pointSylow D S f)

/-- The genuine MS input itself excludes the central-omega row of the
smaller PointModuleCases contract at the original Sylow T∩LR₁. -/
theorem sylowOmega_not_central_intrinsic :
    ¬ SourceInterface.omegaCenterIn P ≤ SourceInterface.centerIn (L ⊔ f.Ri 0) :=
  SylowInitial.sylowOmega_not_central
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary
    (pointSylow_isSylowIn D S f)

/-- The remaining radical comparison at the original point is exactly
its comparison in the faithful initial action; no extra kernel is assumed. -/
theorem radical_comparison_initial_action :
    let J := L ⊔ f.Ri 0
    let q := centralOmegaProjection L (f.Ri 0)
    MSNotCentralizerCore L (f.Ri 0) P ↔
      ((f.Ri 0).subgroupOf J).map q ≠
        (NormalElementaryQuotient.fixedSpaceFixer (centralOmegaRepresentation L (f.Ri 0))
          (((P).subgroupOf J).map q)).pCoreIn 2 :=
  SylowInitial.notCentralizerCore_iff_initial_action
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary
    (pointSylow_isSylowIn D S f)

/-- The actual point's initial module has natural order, or the strict
radical inequality already holds at the original Sylow T∩LR₁. -/
theorem initial_order_or_radical_inequality :
    Nat.card (initialMoved L (f.Ri 0)) = 2^(3*S.field.degree) ∨
      MSNotCentralizerCore L (f.Ri 0) P := by
  rcases RadicalInitial.initial_order_or_radical_inequalities
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary with hc | hr
  · exact Or.inl hc
  · exact Or.inr (hr P (pointSylow_isSylowIn D S f) (radical_le_pointSylow D S f))

/-- A doubled model on the literal initial point module proves the
required strict inequality, without any whole-core recognition premise. -/
theorem radical_inequality_of_initial_doubled
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L (initialMoved L (f.Ri 0)) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := S.field.Carrier) 3).prod
        (specialLinearNatural (k := S.field.Carrier) 3))) :
    MSNotCentralizerCore L (f.Ri 0) P :=
  RadicalInitial.notCentralizerCore_of_initial_doubled
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary e hm
    (pointSylow_isSylowIn D S f) (radical_le_pointSylow D S f)

/-- Centrality of the whole original commutator in O₂(LR₁) closes the
precise PointModuleCases contract, including its original radical inequality. -/
theorem pointModuleCases_of_central
    (hz : msQ L (f.Ri 0) ≤ centralizer ((L ⊔ f.Ri 0).pCoreIn 2 : Set G)) :
    ∃ e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier),
      PointModuleCases D S (f.Ri 0) P e := by
  obtain ⟨e,he⟩ := RadicalInitial.moduleAlternatives_of_central
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary hz
    (pointSylow_isSylowIn D S f) (radical_le_pointSylow D S f)
  exact ⟨e,pointModuleCases_of_alternatives D S (f.Ri 0) P e he⟩

/-- The original escaping point is a genuine SL₃-even block and V=V_M
in the central-core branch. No intrinsic classifier remains as an input. -/
theorem escaping_point_block_of_central
    (hz : msQ L (f.Ri 0) ≤ centralizer ((L ⊔ f.Ri 0).pCoreIn 2 : Set G)) :
    V = Chapter11.Source.conjugateSpan (normalizer (L : Set G)) V ∧
      ChapterC.IsSL3EvenBlock L S.field.degree := by
  obtain ⟨e,he⟩ := pointModuleCases_of_central D S m f hescape hz
  have hb := block_of_pointModuleCases D S m f e he
  exact ⟨(point_blocks_with_span D (Or.inl hb)).1,hb⟩

/-- Abelianity of the original join two-core supplies the same actual
point recognition, including the field-four specialization. -/
theorem escaping_point_block_of_abelian_joinCore
    (hc : IsMulCommutative ((L ⊔ f.Ri 0).pCoreIn 2)) :
    V = Chapter11.Source.conjugateSpan (normalizer (L : Set G)) V ∧
      ChapterC.IsSL3EvenBlock L S.field.degree :=
  escaping_point_block_of_central D S m f hescape
    (msQ_le_joinCore.trans (le_centralizer_iff_isMulCommutative.mpr hc))


/-- A doubled model of the whole original point core supplies the literal
radical inequality in odd field degree, with no ambient centrality premise. -/
theorem radical_inequality_of_whole_doubled (ho : Odd S.field.degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L (msQ L (f.Ri 0)) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := S.field.Carrier) 3).prod
        (specialLinearNatural (k := S.field.Carrier) 3))) :
    MSNotCentralizerCore L (f.Ri 0) P :=
  DoubledRadical.notCentralizerCore_of_doubled
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary ho e hm
    (pointSylow_isSylowIn D S f) (radical_le_pointSylow D S f)

/-- Whole doubled recognition is sufficient for the exact PointModuleCases
contract in odd degree; its radical clause is proved on T∩LR₁. -/
theorem pointModuleCases_of_doubled (ho : Odd S.field.degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L (msQ L (f.Ri 0)) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := S.field.Carrier) 3).prod
        (specialLinearNatural (k := S.field.Carrier) 3))) :
    PointModuleCases D S (f.Ri 0) P e :=
  pointModuleCases_of_alternatives D S (f.Ri 0) P e
    (Or.inr (Or.inl ⟨hm,radical_inequality_of_whole_doubled D S m f hescape ho e hm⟩))

/-- Apply the completed doubled row to the original escaping point. -/
theorem escaping_point_block_of_doubled (ho : Odd S.field.degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L (msQ L (f.Ri 0)) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := S.field.Carrier) 3).prod
        (specialLinearNatural (k := S.field.Carrier) 3))) :
    V = Chapter11.Source.conjugateSpan (normalizer (L : Set G)) V ∧
      ChapterC.IsSL3EvenBlock L S.field.degree := by
  have hb := block_of_pointModuleCases D S m f e
    (pointModuleCases_of_doubled D S m f hescape ho e hm)
  exact ⟨(point_blocks_with_span D (Or.inl hb)).1,hb⟩

/-- A doubled model of the whole original point core supplies the literal
radical inequality in every nonbinary field degree, with no ambient centrality premise. -/
theorem radical_inequality_of_whole_doubled_all_degrees
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L (msQ L (f.Ri 0)) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := S.field.Carrier) 3).prod
        (specialLinearNatural (k := S.field.Carrier) 3))) :
    MSNotCentralizerCore L (f.Ri 0) P :=
  DoubledRadical.notCentralizerCore_of_doubled_all_degrees
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary e hm
    (pointSylow_isSylowIn D S f) (radical_le_pointSylow D S f)

/-- Whole doubled recognition is sufficient for the exact PointModuleCases
contract in every nonbinary degree; its radical clause is proved on T∩LR₁. -/
theorem pointModuleCases_of_doubled_all_degrees
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L (msQ L (f.Ri 0)) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := S.field.Carrier) 3).prod
        (specialLinearNatural (k := S.field.Carrier) 3))) :
    PointModuleCases D S (f.Ri 0) P e :=
  pointModuleCases_of_alternatives D S (f.Ri 0) P e
    (Or.inr (Or.inl ⟨hm,radical_inequality_of_whole_doubled_all_degrees D S m f hescape e hm⟩))

/-- Apply the completed doubled row to the original escaping point. -/
theorem escaping_point_block_of_doubled_all_degrees
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L (msQ L (f.Ri 0)) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := S.field.Carrier) 3).prod
        (specialLinearNatural (k := S.field.Carrier) 3))) :
    V = Chapter11.Source.conjugateSpan (normalizer (L : Set G)) V ∧
      ChapterC.IsSL3EvenBlock L S.field.degree := by
  have hb := block_of_pointModuleCases D S m f e
    (pointModuleCases_of_doubled_all_degrees D S m f hescape e hm)
  exact ⟨(point_blocks_with_span D (Or.inl hb)).1,hb⟩


/-- In the original point row the natural whole center is the actual initial
moved subgroup, with the original field and full component marking. -/
theorem natural_center_eq_initial
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L (SourceInterface.centerIn (msQ L (f.Ri 0))) ⊥ (linearThreeActor e)
      (specialLinearNatural (k := S.field.Carrier) 3)) :
    SourceInterface.centerIn (msQ L (f.Ri 0)) = initialMoved L (f.Ri 0) :=
  NaturalCenter.center_eq_initial
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary e hm

/-- The fourth point row's natural moved center supplies a splitting of the
entire center and component-core centrality, including at field four. -/
theorem natural_moved_center_structure
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L ⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ ⊥
      (linearThreeActor e) (specialLinearNatural (k := S.field.Carrier) 3)) :
    ⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ = initialMoved L (f.Ri 0) ∧
      SourceInterface.centerIn (msQ L (f.Ri 0)) ≤ centralizer (L.pCoreIn 2 : Set G) ∧
      ⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ ⊔
        (SourceInterface.centerIn (msQ L (f.Ri 0)) ⊓ centralizer (L : Set G)) =
          SourceInterface.centerIn (msQ L (f.Ri 0)) ∧
      ⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ ⊓
        (SourceInterface.centerIn (msQ L (f.Ri 0)) ⊓ centralizer (L : Set G)) = ⊥ := by
  let h := point_linearThreeMSPair D S m f (point_msPair D S f hescape)
  exact ⟨NaturalCenter.centerCommutator_eq_initial h S.nonbinary e hm,
    NaturalCenter.center_centralizes_componentCore h S.nonbinary e hm,
    NaturalCenter.center_split h S.nonbinary e hm⟩

/-- The original full point center has a faithful full SL₃ action, including
at field four, from the same natural moved-center premise. -/
theorem natural_moved_center_action
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (hm : HasSectionModel L ⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ ⊥
      (linearThreeActor e) (specialLinearNatural (k := S.field.Carrier) 3)) :
    ∃ b : SL(3,S.field.Carrier) →* MulAut (SourceInterface.centerIn (msQ L (f.Ri 0))),
      Function.Injective b ∧ ∀ (k : L) (z : SourceInterface.centerIn (msQ L (f.Ri 0))),
        (b (linearThreeActor e k) z : G) = k * (z : G) * (k : G)⁻¹ :=
  NaturalCenter.exists_centerAction
    (point_linearThreeMSPair D S m f (point_msPair D S f hescape)) S.nonbinary e hm

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.PointApplication
