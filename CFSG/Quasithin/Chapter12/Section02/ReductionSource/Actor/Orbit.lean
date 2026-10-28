module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Source
public import CFSG.Quasithin.ChapterD.Section03.SourceInternal
public import Theory.GroupTheory.ReducedNormal.ActionCore
public import Theory.Representation.BinaryOffender.Homogeneous.OrbitFixedSpace
/-!
# The actual T-orbit of a chosen Section 12.2 module

The normal component and Sylow subgroup generate LT. Its orbit of the chosen
Irr⁺ seed is therefore precisely the original T-orbit. The internal reduced
module theorem gives trivial two-core for this orbit's faithful action. The
image of L is quasisimple, has the original projective central quotient, and
is the generalized Fitting subgroup because the remaining quotient is a
two-group. Fixed-space orbit transport retains fixed-freeness of the seed.

All maps are restrictions of conjugation on R₂(LT). The last two identities
identify the represented space with the literal FSU module in G. There is
no assertion that the seed itself is T-invariant or that its ratio equals
the ratio of the full orbit.
Source: Aschbacher--Smith, 3.2.2--3.2.5, pp.579--580, applied in 12.2.2,
pp.794--795, and the odd linear-three branch of 13.1.4, p.867.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)

abbrev orbitSpace := orbitSpan (reducedRepresentation (L ⊔ (T : Subgroup G))) ⊤ D.space
abbrev orbitActor := subspaceActionImage (reducedRepresentation (L ⊔ (T : Subgroup G))) D.orbitSpace
abbrev orbitRepresentation := subspaceImageRepresentation
  (reducedRepresentation (L ⊔ (T : Subgroup G))) D.orbitSpace
abbrev orbitComponent : Subgroup D.orbitActor := restrictedSubgroup
  (reducedRepresentation (L ⊔ (T : Subgroup G))) D.orbitSpace
  (L.subgroupOf (L ⊔ (T : Subgroup G)))

theorem internalOrbitHypotheses (h : Hypothesis1221 K T L) :
    InternalModuleHypotheses K (reducedRepresentation (L ⊔ (T : Subgroup G)))
      (T.subtype le_sup_right) (L.subgroupOf (L ⊔ (T : Subgroup G))) D.space := by
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let e : X ≃* L := subgroupOfEquivOfLe le_sup_left
  have hX : pResidual 2 X = ⊤ := (pResidual_eq_top_iff 2 X).mpr
    (h.maximal_faithful.2.1.2.1.of_surjective e.symm.toMonoidHom e.symm.surjective)
  let eQ := QuotientGroup.congr (pCore 2 X) (pCore 2 L) e (pCore_map_iso 2 e)
  let := h.quasisimple
  have hQ : IsQuasisimple (X ⧸ pCore 2 X) := IsQuasisimple.of_mulEquiv eQ.symm
  have hsup : X ⊔ (T : Subgroup G).subgroupOf H = ⊤ := by
    rw [ ← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  refine ⟨h.join_sqtk, inferInstance, inferInstance, hX, ?_, ?_, D.irrPlus.isIrrPlus, ?_⟩
  · refine Or.inl ⟨X, h.maximal_faithful.1.1.1, hQ, ?_⟩
    exact (le_antisymm (iSup_conjugates_le_of_le_normalizer X _ X le_rfl
      le_normalizer_of_normal) (le_componentOrbit X _)).symm
  · exact ReducedNormal.normal_actor_representation_twoCore_eq_bot H X
  · change (X ⊔ (T : Subgroup G).subgroupOf H).pCoreIn 2 ≤ _
    rw [hsup]
    have he : (⊤ : Subgroup H).pCoreIn 2 = pCore 2 H := pCore_map_iso 2 topEquiv
    rw [he]
    exact ReducedNormal.representation_twoCore_stabilizes H D.space

 theorem orbit_twoCore_eq_bot (h : Hypothesis1221 K T L) : pCore 2 D.orbitActor = ⊥ :=
  (D.internalOrbitHypotheses h).faithfulOrbit_twoCore_eq_bot

omit [Finite G] in
theorem orbitSpace_component_invariant :
    L.subgroupOf (L ⊔ (T : Subgroup G)) ≤
      subspaceStabilizer (reducedRepresentation (L ⊔ (T : Subgroup G))) D.orbitSpace :=
  le_top.trans (orbitSpan_invariant _ ⊤ D.space)

def orbitHom : (L ⊔ (T : Subgroup G) : Subgroup G) →* D.orbitActor :=
  invariantActionHom (reducedRepresentation (L ⊔ (T : Subgroup G))) D.orbitSpace
    (orbitSpan_invariant _ ⊤ D.space)

omit [Finite G] in
theorem orbitHom_surjective : Function.Surjective D.orbitHom :=
  invariantActionHom_surjective _ _ _

omit [Finite G] in
theorem orbitComponent_eq_map : D.orbitComponent =
    (L.subgroupOf (L ⊔ (T : Subgroup G))).map D.orbitHom :=
  (invariantActionHom_map _ _ _ _).symm

omit [Finite G] in
instance orbitComponent_normal : D.orbitComponent.Normal := by
  let H := L ⊔ (T : Subgroup G)
  let : (L.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  rw [D.orbitComponent_eq_map]
  exact Normal.map inferInstance D.orbitHom D.orbitHom_surjective

omit [Finite G] in
theorem orbitComponent_ne_bot : D.orbitComponent ≠ ⊥ :=
  restrictedSubgroup_ne_bot _ _ D.orbitSpace_component_invariant
    (fun hw => D.irrPlus.isIrrPlus.not_le_fixedSpace _
      ((le_orbitSpan _ ⊤ D.space).trans hw))

omit [Finite G] in
instance orbitComponent_nontrivial : Nontrivial D.orbitComponent :=
  (Subgroup.nontrivial_iff_ne_bot _).mpr D.orbitComponent_ne_bot

def orbitComponentHom : L →* D.orbitComponent :=
  (restrictedActionSurjection (reducedRepresentation (L ⊔ (T : Subgroup G))) D.orbitSpace
    (L.subgroupOf (L ⊔ (T : Subgroup G))) D.orbitSpace_component_invariant).comp
      (subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm.toMonoidHom

omit [Finite G] in
theorem orbitComponentHom_surjective : Function.Surjective D.orbitComponentHom :=
  (restrictedActionSurjection_surjective _ _ _ D.orbitSpace_component_invariant).comp
    (subgroupOfEquivOfLe le_sup_left).symm.surjective

theorem orbitComponentHom_kills_core (h : Hypothesis1221 K T L) :
    pCore 2 L ≤ D.orbitComponentHom.ker := by
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let e : X ≃* L := subgroupOfEquivOfLe le_sup_left
  intro l hl
  have hx : e.symm l ∈ pCore 2 X := by
    have hm := mem_map_of_mem e.symm.toMonoidHom hl
    rwa [pCore_map_iso] at hm
  apply Subtype.ext
  apply subspaceImageRepresentation_injective _ _
  ext v
  exact congrArg (fun w : Additive (ReducedModule H) => (w.toMul.val : G))
    ((D.internalOrbitHypotheses h).actorCore_fixes (e.symm l) hx v.val)

def orbitComponentQuotientHom (h : Hypothesis1221 K T L) :
    (L ⧸ pCore 2 L) →* D.orbitComponent :=
  QuotientGroup.lift _ D.orbitComponentHom (D.orbitComponentHom_kills_core h)

theorem orbitComponentQuotientHom_surjective (h : Hypothesis1221 K T L) :
    Function.Surjective (D.orbitComponentQuotientHom h) :=
  QuotientGroup.lift_surjective_of_surjective _ _ D.orbitComponentHom_surjective _

theorem orbitComponent_quasisimple (h : Hypothesis1221 K T L) :
    IsQuasisimple D.orbitComponent := by
  let := h.quasisimple
  exact IsQuasisimple.of_surjective (D.orbitComponentQuotientHom h)
    (D.orbitComponentQuotientHom_surjective h)

def orbitCentralQuotientEquiv (h : Hypothesis1221 K T L) :
    ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃*
      (D.orbitComponent ⧸ center D.orbitComponent) := by
  let := h.quasisimple
  exact IsQuasisimple.centralQuotientEquiv (D.orbitComponentQuotientHom h)
    (D.orbitComponentQuotientHom_surjective h)


omit [Finite G] in
theorem orbit_quotient_isTwoGroup : IsPGroup 2 (D.orbitActor ⧸ D.orbitComponent) := by
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hp : IsPGroup 2 (H ⧸ X) := by
    apply isPGroup_quotient_of_sup_eq_top X ((T : Subgroup G).subgroupOf H)
      T.isPGroup'.comap_subtype
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hx : X ≤ D.orbitComponent.comap D.orbitHom := by
    intro x hx
    rw [mem_comap, D.orbitComponent_eq_map]
    exact mem_map_of_mem D.orbitHom hx
  exact hp.of_surjective (QuotientGroup.map _ _ D.orbitHom hx)
    (QuotientGroup.map_surjective_of_surjective _ _ D.orbitHom
      ((QuotientGroup.mk'_surjective _).comp D.orbitHom_surjective) hx)

theorem orbit_fitting (h : Hypothesis1221 K T L) :
    generalizedFitting D.orbitActor = D.orbitComponent := by
  let := D.orbitComponent_quasisimple h
  exact generalizedFitting_eq_of_quasisimple_two_quotient D.orbitComponent
    D.orbit_quotient_isTwoGroup (D.orbit_twoCore_eq_bot h)

omit [Finite G] in
theorem seed_inf_fixedSpace_eq_bot (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    D.space ⊓ fixedSpace (reducedRepresentation (L ⊔ (T : Subgroup G)))
      (L.subgroupOf (L ⊔ (T : Subgroup G))) = ⊥ := by
  have he := congrArg (Submodule.map D.space.subtype) (D.seed_fixedSpace_eq_bot hc)
  rw [fixedSpace_restrictedSubgroup _ _ _ D.irrPlus.invariant,
    Submodule.map_comap_subtype, Submodule.map_bot] at he
  simpa only [inf_comm] using he

theorem orbit_fixedSpace_eq_bot (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    fixedSpace D.orbitRepresentation D.orbitComponent = ⊥ := by
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have he := orbitSpan_inf_fixedSpace (reducedRepresentation H) X D.irrPlus.isIrrPlus
  rw [D.seed_inf_fixedSpace_eq_bot hc] at he
  simp only [orbitSpan, Submodule.map_bot, iSup_const] at he
  rw [fixedSpace_restrictedSubgroup _ _ _ D.orbitSpace_component_invariant]
  apply bot_unique
  intro v hv
  exact Subtype.ext (he.le ⟨v.property, hv⟩)

omit [Finite G] in
theorem seed_le_orbitSpace : D.space ≤ D.orbitSpace := le_orbitSpan _ ⊤ _


omit [Finite G] in
/-- The full local-join orbit is precisely the original T-orbit. -/
theorem orbitSpace_eq_sylowOrbit : D.orbitSpace =
    orbitSpan (reducedRepresentation (L ⊔ (T : Subgroup G)))
      ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))) D.space := by
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let Y := (T : Subgroup G).subgroupOf H
  have hgen : X ⊔ Y = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hstab : (⊤ : Subgroup H) ≤ subspaceStabilizer (reducedRepresentation H)
      (orbitSpan (reducedRepresentation H) Y D.space) := by
    rw [← hgen]
    exact sup_le (orbitSpan_component_invariant _ D.irrPlus.normalizes
      D.irrPlus.isIrrPlus) (orbitSpan_invariant _ _ _)
  apply le_antisymm (orbitSpan_le _ (le_orbitSpan _ _ _) hstab)
  exact orbitSpan_le _ (le_orbitSpan _ _ _) (le_top.trans (orbitSpan_invariant _ _ _))

omit [Finite G] in
/-- The orbit's ambient subgroup is the literal FSU module, with its original inclusion. -/
theorem orbitSpace_image : subspaceImage (L ⊔ (T : Subgroup G)) D.orbitSpace =
    componentOrbit V (T : Subgroup G) := by
  rw [D.orbitSpace_eq_sylowOrbit]
  have he := ReducedNormal.subspaceImage_orbitSpan (L ⊔ (T : Subgroup G))
    (T : Subgroup G) le_sup_right D.space
  change subspaceImage (L ⊔ (T : Subgroup G)) _ =
    componentOrbit (subspaceImage (L ⊔ (T : Subgroup G)) D.space) (T : Subgroup G) at he
  simpa only [D.image_eq, reducedRepresentation, reducedConjugation,
    ReducedNormal.representation, ReducedNormal.conjugation] using he

/-- The action is on the module supplied by the original Fundamental Setup. -/
theorem orbitSpace_image_fundamentalSetup (h : Hypothesis1221 K T L) :
    subspaceImage (L ⊔ (T : Subgroup G)) D.orbitSpace =
      (D.fundamentalSetup h).moduleSubgroup := by
  rw [D.orbitSpace_image, D.fundamentalSetup_module h]

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
