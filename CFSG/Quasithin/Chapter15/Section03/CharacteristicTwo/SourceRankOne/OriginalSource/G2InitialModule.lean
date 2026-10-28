module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.G2Holomorph
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.Quasithin.Rank
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.NaturalLayerRecognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.Geometry
public import Theory.Representation.NormalElementaryQuotient.IrrPlusCommutator
/-!
# The actual initial G₂ module from the original MS source

The original Sylow pair and characteristic-two condition make the omega orbit
faithful modulo O₂(I). The component quotient is the simple group G₂(2)′;
its image is the two-residual of I/O₂(I), with trivial centralizer. The actual
central-omega action is therefore a faithful FF module. The source-correct
FF classification identifies its moved/fixed section with the natural G₂
six-space and identifies the moving subgroup of the original omega orbit.

All quotient maps and conjugation formulas are literal. The fixed part is
retained; this does not identify the full commutator [O₂(I),L]. Its separate
Frattini containment is the remaining MS93 (3.6) input.
Source: Meierfrankenfeld–Stellmacher (1993), (2.2), (3.2)(vii), pp.857,863–866;
Aschbacher–Smith C.1.32 and 15.3.31, pp.136,1132.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.CentralCover
open EightGeometry.NaturalModule.Recognition ChapterC
open Stellmacher.PushingUp.AmalgamGraph
namespace G2Holomorph
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} (s : SourceData KnownSimple.IsKnownSimple d c)

include s

private theorem relative_product : ∀ g : I,
    ∃ l ∈ c.L.subgroupOf I, ∃ r ∈ d.S.subgroupOf I, l * r = g := by
  let _ := s.normal
  intro g
  have hg : g ∈ c.L.subgroupOf I ⊔ d.S.subgroupOf I := by
    rw [←subgroupOf_sup (component_le c)
      ((Chapter1.isSylowIn_iff.mp ⟨s.sylow,s.sylow_eq⟩).2.1),←s.generated,subgroupOf_self]
    trivial
  exact mem_sup_of_normal_left.mp hg

private theorem core_self_centralizing : centralizer (pCore 2 I : Set I) ≤ pCore 2 I := by
  rw [←s.characteristicTwo]
  exact centralizer_generalizedFitting_le I

variable (m : Parabolics.RankTwoParabolicMarking d I c.L CentralCover.BlockModels.G2.Actor
      Parabolics.g2DerivedParabolic)

include m

private noncomputable def relativeCoreEquiv :
    ((c.L.subgroupOf I) ⧸ pCore 2 (c.L.subgroupOf I)) ≃*
      commutator (Atlas.G2.Model (ZMod 2)) := by
  let e := subgroupOfEquivOfLe (component_le c)
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (Classical.choose (source_g2_quotient_marking s m))

theorem initial_orbit_centralizer :
    centralizer (MSCentralOrbit.omegaOrbit (d.S.subgroupOf I) : Set I) = pCore 2 I := by
  let _ := s.normal
  let _ := Atlas.G2.isSimple_commutator_binary
  let _ := (relativeCoreEquiv s m).isSimpleGroup
  exact MSCentralOrbit.omegaOrbit_centralizer (c.L.subgroupOf I) (d.S.subgroupOf I)
    (edge_two_group s) (edge_ne_bot s) (core_le_edge s) (core_self_centralizing s)
    (relative_product s) (edge_characteristic s)

theorem central_omega_centralizer :
    centralizer (omegaCenterIn (pCore 2 I) : Set I) = pCore 2 I :=
  MSCentralOrbit.centralOmega_centralizer (d.S.subgroupOf I) (core_le_edge s)
    (core_self_centralizing s) (initial_orbit_centralizer s m)


@[expose] def quotientComponent : Subgroup (I ⧸ pCore 2 I) :=
  (c.L.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))

private noncomputable def imageCoreEquiv :
    ((c.L.subgroupOf I) ⧸ pCore 2 (c.L.subgroupOf I)) ≃* quotientComponent (c := c) :=
  cComponentTwoCoreQuotientEquiv (Parabolics.Placement.ModelComparison.component_isCComponent_in d c)

noncomputable def quotientComponentEquiv :
    quotientComponent (c := c) ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
  (imageCoreEquiv (c := c)).symm.trans (relativeCoreEquiv s m)

theorem quotientComponent_card : Nat.card (quotientComponent (c := c)) = 6048 :=
  (Nat.card_congr (quotientComponentEquiv s m).toEquiv).trans
    (Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp))

theorem quotientComponent_simple : IsSimpleGroup (quotientComponent (c := c)) := by
  let _ := Atlas.G2.isSimple_commutator_binary
  exact (quotientComponentEquiv s m).isSimpleGroup

omit s m in
theorem quotientComponent_quasisimple : IsQuasisimple (quotientComponent (c := c)) := by
  let _ := c.core_quotient_quasisimple
  let e := subgroupOfEquivOfLe (component_le c)
  let eQ := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let _ := IsQuasisimple.of_mulEquiv eQ.symm
  exact IsQuasisimple.of_mulEquiv (imageCoreEquiv (c := c))

omit m in
theorem quotientComponent_residual :
    quotientComponent (c := c) = pResidual 2 (I ⧸ pCore 2 I) := by
  change (c.L.subgroupOf I).map (QuotientGroup.mk' _) = _
  rw [←residual_eq_component s, map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]

omit m in
theorem quotientComponent_normal : (quotientComponent (c := c)).Normal := by
  rw [quotientComponent_residual s]
  infer_instance

theorem quotientComponent_centralizer :
    centralizer (quotientComponent (c := c) : Set (I ⧸ pCore 2 I)) = ⊥ := by
  have hC : centralizer (quotientComponent (c := c) : Set (I ⧸ pCore 2 I)) ≤
      quotientComponent (c := c) := by
    rw [quotientComponent_residual s]
    exact centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2)
  apply le_bot_iff.mp
  intro x hx
  have hz : (⟨x,hC hx⟩ : quotientComponent (c := c)) ∈ center (quotientComponent (c := c)) := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hx y y.property)
  have he : quotientComponentEquiv s m ⟨x,hC hx⟩ = 1 :=
    Theory.SpecificGroups.g2_derived_two_center_eq_bot.le
      ((centerCongr (quotientComponentEquiv s m) ⟨_,hz⟩).property)
  exact congrArg Subtype.val ((quotientComponentEquiv s m).map_eq_one_iff.mp he)

omit m in
theorem quotientComponent_sqtk : IsSQTK KnownSimple.IsKnownSimple (quotientComponent (c := c)) := by
  have hsq : IsSQTK KnownSimple.IsKnownSimple (I ⧸ pCore 2 I) :=
    ⟨fun p hp ho => by
      let _ : Fact p.Prime := ⟨hp⟩
      exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 I) pCore_isPGroup).trans
        (s.sqtk.stronglyQuasithin p hp ho), s.sqtk.isKGroup.quotient _⟩
  exact hsq.subgroup _

theorem central_omega_FF :
    let q := QuotientGroup.mk' (pCore 2 I)
    let hker := (QuotientGroup.ker_mk' (pCore 2 I)).trans (central_omega_centralizer s m).symm
    Representation.BinaryOffender.IsFFModule
      (Representation.NormalElementaryQuotient.representation (omegaCenterIn (pCore 2 I)) q
        (QuotientGroup.mk'_surjective _) hker) := by
  exact MSCentralOrbit.centralOmega_isFFModule (d.S.subgroupOf I)
    (edge_characteristic s) (edge_two_group s) (edge_ne_bot s) (core_le_edge s)
    (core_self_centralizing s) (initial_orbit_centralizer s m)
    (QuotientGroup.mk' (pCore 2 I)) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)


@[expose] noncomputable def centralOmegaAction :
    Representation (ZMod 2) (I ⧸ pCore 2 I) (Additive (omegaCenterIn (pCore 2 I))) :=
  Representation.NormalElementaryQuotient.representation _ (QuotientGroup.mk' (pCore 2 I))
    (QuotientGroup.mk'_surjective _) ((QuotientGroup.ker_mk' _).trans
      (central_omega_centralizer s m).symm)

theorem centralOmegaAction_faithful : Function.Injective (centralOmegaAction s m) :=
  Representation.NormalElementaryQuotient.representation_injective _ _ _ _

theorem centralOmegaAction_apply (g : I) (v : Additive (omegaCenterIn (pCore 2 I))) :
    ((centralOmegaAction s m (QuotientGroup.mk' (pCore 2 I) g) v).toMul : I) =
      g * (v.toMul : I) * g⁻¹ :=
  Representation.NormalElementaryQuotient.representation_apply _ _ _ _ g v

theorem initial_edge_centralizer : BinaryMS.MS93.EdgeCentralizerCondition (d.S.subgroupOf I) :=
  MSCentralOrbit.edgeCentralizerCondition _ (edge_two_group s) (core_le_edge s)
    (initial_orbit_centralizer s m)

theorem initial_moved_natural :
    let := quotientComponent_normal s
    Representation.BinaryOffender.IsIrrPlus (centralOmegaAction s m) (quotientComponent (c := c))
      (Representation.BinaryOffender.subspaceCommutator (centralOmegaAction s m) ⊤
        (quotientComponent (c := c))) ∧
      Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
        ((ChapterB.QuasisimpleSource.MovedSection.ofNormal (centralOmegaAction s m)
          (quotientComponent (c := c))).action.comp (quotientComponent (c := c)).subtype)
        (Representation.g2DerivedNatural (ZMod 2))) := by
  let := quotientComponent_normal s
  let := quotientComponent_simple s m
  let := quotientComponent_quasisimple (c := c)
  exact RankTwo.G2.ff_card_g2_two_moved_natural _ _ (quotientComponent_card s m)
    (quotientComponent_centralizer s m) (quotientComponent_sqtk s)
    (centralOmegaAction_faithful s m) (central_omega_FF s m)

/-- The original Sylow omega orbit has the same moving subgroup as the full
central omega layer, with both commutators taken in the actual group I. -/
theorem initialCore_eq :
    ⁅MSCentralOrbit.omegaOrbit (d.S.subgroupOf I),c.L.subgroupOf I⁆ =
      ⁅omegaCenterIn (pCore 2 I),c.L.subgroupOf I⁆ := by
  let := quotientComponent_normal s
  let := quotientComponent_quasisimple (c := c)
  let : IsElementaryAbelian 2 (MSCentralOrbit.omegaOrbit (d.S.subgroupOf I)) :=
    MSCentralOrbit.omegaOrbit_elementary _ (core_le_edge s) (core_self_centralizing s)
  have hne : quotientComponent (c := c) ≠ ⊥ := by
    intro hz
    have hc := quotientComponent_card s m
    rw [hz,card_bot] at hc
    omega
  exact Representation.NormalElementaryQuotient.commutator_eq_of_irrPlus
    (MSCentralOrbit.omegaOrbit (d.S.subgroupOf I)) (omegaCenterIn (pCore 2 I))
    (MSCentralOrbit.omegaOrbit_le_centralOmega _ (core_le_edge s) (core_self_centralizing s))
    (QuotientGroup.mk' (pCore 2 I)) (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (initial_orbit_centralizer s m).symm)
    ((QuotientGroup.ker_mk' _).trans (central_omega_centralizer s m).symm)
    (c.L.subgroupOf I) (quotientComponent (c := c)) rfl hne
    (initial_moved_natural s m).1

end G2Holomorph
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
