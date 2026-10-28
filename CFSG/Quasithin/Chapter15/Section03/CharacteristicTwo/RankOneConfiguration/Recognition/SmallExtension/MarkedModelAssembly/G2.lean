module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.Configurations
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedModelAssembly.Linear
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedModelAssembly.G2.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedModelAssembly.G2.QuotientPlane
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedModelAssembly.G2.PlaneGeometry
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.StandardPair

/-!
# The original marked G₂ block

The classified trace-zero quotient gives a genuine block model on the fixed
natural G₂(2)' carrier. Map the original V₂ through its full central quotient.
Its intersection with C(Y₊) is trivial, so its image is still a plane. The
original M ∩ L image stabilizes this plane and has order 96: this follows from
the actual small-parabolic marking and the compatible L/O₂(L) ≃ L* map.

The intrinsic plane theorem supplies compatible actor and coefficient changes:
an order-96 subgroup contains a Sylow two-subgroup, whose unique invariant plane
is the marked null plane after conjugation. The literal stabilizer order then
gives equality. Applying this theorem to the original V₂ image constructs the
marked block model without a placement premise. The full central kernel and
the source plane are retained. Final assembly with the other four model cases
belongs to the parent module.

Source: Aschbacher–Smith, proof of 15.3.31, printed p.1132 (PDF p.1149),
using C.1.7, C.1.30–34 and B.5.3–6. The root-parabolic conventions and
actual octonion model come from the licensed ATLAS port (LICENSES/ATLAS.txt).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedModelAssembly
open CentralCover CentralCover.BlockModels G2Coordinates
open Atlas.G2.BinaryParabolicPair
open MarkedMS.Constituents

variable {G : Type*} [Group G]

private theorem g2_derived_card : Nat.card G2.Actor = 6048 := by
  change Nat.card (commutator (Atlas.G2.Model (ZMod 2))) = 6048
  rw [commutator_eq_longRootClosure]
  exact Atlas.G2.BinaryException.card_H

private theorem g2Parabolic_card (i : Fin 2) : Nat.card (Parabolics.g2DerivedParabolic i) = 96 := by
  fin_cases i
  · change Nat.card ((Atlas.G2.LieParabolicSetup.parabolic₁ (F := ZMod 2)).subgroupOf _) = 96
    rw [Atlas.G2.LieParabolicSetup.parabolic₁_binary]
    exact card_derivedFirst
  · change Nat.card ((Atlas.G2.LieParabolicSetup.parabolic₂ (F := ZMod 2)).subgroupOf _) = 96
    exact card_derivedSecond

variable [Finite G] {κ : GroupClass} {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

private theorem g2_parabolic_card (s : SourceData κ d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq)
    (m : ChapterC.BlockModuleModel c.L (multiplicativeAction G2.action)) :
    Nat.card (((d.M ⊓ c.L).subgroupOf c.L).map
      (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L)))) = 96 := by
  obtain ⟨q, hq⟩ := ms.quotient
  let f := q.symm.trans m.quotientIso
  have ha : m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L)) =
      f.toMonoidHom.comp (componentMap d c) := by
    apply MonoidHom.ext
    intro l
    change m.quotientIso (QuotientGroup.mk' (pCore 2 c.L) l) =
      m.quotientIso (q.symm (componentMap d c l))
    rw [← hq, q.symm_apply_apply]
  have hcard : Nat.card (d.starImage I c.L) = 6048 :=
    (Nat.card_congr f.toEquiv).trans g2_derived_card
  rw [ha, ← map_map, MarkedModelAssembly.componentMap_parabolic_image,
    card_map_of_injective f.injective]
  cases hm with
  | linearThree n =>
    have h := (Nat.card_congr n.equiv.toEquiv).trans Matrix.PSL3Two.card_SL
    omega
  | symplecticDerived n =>
    have hc : Nat.card (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) = 360 := by
      rw [Nat.card_congr (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
        (F := ZMod 2) (by simp)).toEquiv, nat_card_alternatingGroup]
      norm_num
    have h := (Nat.card_congr n.equiv.toEquiv).trans hc
    omega
  | g2Derived n =>
    have h := g2Parabolic_card n.node
    rw [← n.intersection, card_map_of_injective n.equiv.injective] at h
    exact h


/-- The source inputs construct the natural model, an injective image of the
original V₂, and its order-96 stabilizing subgroup. No placement is assumed. -/
theorem g2_source_coordinates (s : SourceData κ d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq)
    (h : IsG2TwoBlock c.L) :
    ∃ m : ChapterC.BlockModuleModel c.L (multiplicativeAction G2.action),
      let cm := centerModel h.1 G2.action m
      let W := quotientPlane cm d.V₂
      let P := ((d.M ⊓ c.L).subgroupOf c.L).map cm.actorMap
      Function.Injective (planeMap cm s.plane_le_coreCenter) ∧
      Nat.card W = 4 ∧ Nat.card P = 96 ∧ P ≤ BlockModels.planeStabilizer G2.action W := by
  obtain ⟨m⟩ := exists_actualModel h
  let cm := centerModel h.1 G2.action m
  have hi : Function.Injective (planeMap cm s.plane_le_coreCenter) :=
    planeMap_injective cm s.plane_le_coreCenter s.contains (s.line.plane_fixed_trivial d)
  refine ⟨m, hi, ?_, g2_parabolic_card s hm ms m, ?_⟩
  · exact (quotientPlane_card cm s.plane_le_coreCenter hi).trans (d.action.card_plane _)
  · apply quotientPlane_stabilized cm s.plane_le_coreCenter
    rw [s.component_parabolic]
    exact inf_le_right

omit [Finite G] in
/-- Changing the two coordinates compatibly transports the original V₂ image
by precisely the chosen coefficient map. Its central kernel stays literal. -/
theorem g2_quotientPlane_recoordinate {L E : Subgroup G} (h : ChapterC.IsShort L)
    (m : ChapterC.BlockModuleModel L (multiplicativeAction G2.action))
    (f : G2.Actor ≃* G2.Actor) (e : G2.Coefficients ≃ₗ[ZMod 2] G2.Coefficients)
    (he : ∀ a v, e (G2.action a v) = G2.action (f a) (e v))
    (hE : E ≤ coreCenter L) :
    quotientPlane (centerModel h G2.action (recoordinate m f e he)) E =
      (quotientPlane (centerModel h G2.action m) E).map e.toLinearMap := by
  ext v
  rw [mem_quotientPlane _ hE]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(planeMap (centerModel h G2.action m) hE z).toAdd,
      (mem_quotientPlane _ hE _).mpr ⟨z, rfl⟩, ?_⟩
    exact congrArg Multiplicative.toAdd hz
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨z, hz⟩ := (mem_quotientPlane _ hE w).mp hw
    refine ⟨z, ?_⟩
    change Multiplicative.ofAdd (e (planeMap (centerModel h G2.action m) hE z).toAdd) = _
    rw [hz]
    rfl

/-- Assemble the G₂ source branch from the intrinsic binary plane-orbit theorem.
That independent theorem must supply both compatible coordinate maps, the
original plane's image and the exact stabilizer image. -/
theorem g2_marked_models_of_plane_geometry
    (geometry : ∀ (W : Submodule (ZMod 2) G2.Coefficients) (P : Subgroup G2.Actor),
      Nat.card W = 4 → Nat.card P = 96 → P ≤ BlockModels.planeStabilizer G2.action W →
      ∃ (f : G2.Actor ≃* G2.Actor) (e : G2.Coefficients ≃ₗ[ZMod 2] G2.Coefficients),
        (∀ a v, e (G2.action a v) = G2.action (f a) (e v)) ∧
        W.map e.toLinearMap = G2.markedPlane ∧
        P.map f.toMonoidHom = BlockModels.planeStabilizer G2.action G2.markedPlane)
    (s : SourceData κ d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq)
    (_hblock : ChapterC.IsBlock (c.L.subgroupOf (c.L ⊔ d.S)))
    (h : IsG2TwoBlock c.L) :
    ∃ m : ChapterC.BlockModuleModel c.L (multiplicativeAction G2.action),
      quotientPlane (centerModel h.1 G2.action m) d.V₂ = G2.markedPlane ∧
      ((d.M ⊓ c.L).subgroupOf c.L).map
        (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) =
          BlockModels.planeStabilizer G2.action G2.markedPlane ∧
      MarkedModels c.L d.V₂ (d.M ⊓ c.L) := by
  obtain ⟨m, _, hW, hP, hPW⟩ := g2_source_coordinates s hm ms h
  obtain ⟨f, e, he, hWe, hPe⟩ := geometry _ _ hW hP hPW
  let m' := recoordinate m f e he
  have hmark : ((d.M ⊓ c.L).subgroupOf c.L).map
      (m'.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) =
        BlockModels.planeStabilizer G2.action G2.markedPlane := by
    rw [map_map] at hPe
    exact hPe
  refine ⟨m', ?_, hmark, .g2 h.1 m' hmark⟩
  rw [g2_quotientPlane_recoordinate h.1 m f e he s.plane_le_coreCenter]
  exact hWe

/-- In the selected G₂ block branch, the original V₂ has exactly the canonical
null-plane coordinates, and the original M ∩ L maps onto its full stabilizer.
The model retains the literal blockFixed quotient and the natural derived action. -/
theorem g2_marked_model (s : SourceData κ d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq)
    (hblock : ChapterC.IsBlock (c.L.subgroupOf (c.L ⊔ d.S)))
    (h : IsG2TwoBlock c.L) :
    ∃ m : ChapterC.BlockModuleModel c.L (multiplicativeAction G2.action),
      quotientPlane (centerModel h.1 G2.action m) d.V₂ = G2.markedPlane ∧
      ((d.M ⊓ c.L).subgroupOf c.L).map
        (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) =
          BlockModels.planeStabilizer G2.action G2.markedPlane := by
  obtain ⟨m, hV, hP, _⟩ :=
    g2_marked_models_of_plane_geometry G2PlaneGeometry.geometry s hm ms hblock h
  exact ⟨m, hV, hP⟩

/-- The G₂ case of the common marked extension models, from precisely the
source inputs and the selected block alternative, with no geometric premise. -/
theorem g2_marked_models (s : SourceData κ d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq)
    (hblock : ChapterC.IsBlock (c.L.subgroupOf (c.L ⊔ d.S)))
    (h : IsG2TwoBlock c.L) :
    MarkedModels c.L d.V₂ (d.M ⊓ c.L) := by
  obtain ⟨m, _, hP⟩ := g2_marked_model s hm ms hblock h
  exact .g2 h.1 m hP

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedModelAssembly

end
