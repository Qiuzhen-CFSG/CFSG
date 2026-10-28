module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.Configurations
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedModelAssembly.Coordinates

/-!
# Actual marked models in the three surviving linear cases

The C.1.34 whole-core transports already preserve the quotient actor. Map the
original V₂ into the whole center under these coordinates. In the single-natural
cases its four elements give a plane directly. In the doubled case the literal
component parabolic has order 24 and has no fixed vector on this plane, so the
checked doubled-natural geometry supplies an actual equivariant natural
embedding containing it. The passage between pairs and two indexed copies
changes only the coefficient notation, never the actor.

Thus the full center and both dual summands in case (3) keep the same original
quotient equivalence. No placement, natural-copy or marking premise is added.
The earlier small MS conclusion and the original small parabolic marking remain
explicit source inputs; the two block branches are handled separately.

Source: Aschbacher–Smith, C.1.34(1)–(3), printed pp.136–137, and the proof
of 15.3.31, printed p.1132 (PDF p.1149).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedModelAssembly
open CentralCover CentralCover.LinearModels LinearThree MarkedMS.Constituents
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {L E : Subgroup G} {ρ : Representation (ZMod 2) SL V}

private noncomputable def markedPlane_of_embedding (m : FullCenter L ρ)
    (hE : E ≤ coreCenter L) (W : Submodule (ZMod 2) Space)
    (hd : Module.finrank (ZMod 2) W = 2)
    (f : Space →ₗ[ZMod 2] V) (hf : Function.Injective f)
    (he : ∀ a v, f (natural a v) = ρ a (f v))
    (hm : W.map f = centerPlane m E) : MarkedPlane m E where
  space := W
  dimension := hd
  embedding := f
  injective := hf
  equivariant := he
  contained := hE
  membership z := by
    rw [← coord_mem_centerPlane m E z, ← hm]
    constructor
    · rintro ⟨v, hv, heq⟩
      exact ⟨v, hv, (congrArg Multiplicative.ofAdd heq).symm⟩
    · rintro ⟨v, hv, heq⟩
      exact ⟨v, hv, (congrArg Multiplicative.toAdd heq).symm⟩

private noncomputable def naturalMarkedPlane (m : FullCenter L natural)
    (hE : E ≤ coreCenter L) (hcard : Nat.card E = 4) : MarkedPlane m E :=
  markedPlane_of_embedding m hE (centerPlane m E)
    (plane_dimension _ ((centerPlane_card m hE).trans hcard))
    LinearMap.id Function.injective_id (fun _ _ => rfl) (Submodule.map_id _)

private def pairCoordinates : (Space × Space) ≃ₗ[ZMod 2] (Fin 2 → Space) where
  toFun v := ![v.1, v.2]
  invFun v := (v 0, v 1)
  left_inv _ := rfl
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

private theorem pairCoordinates_action (a : SL) (v : Space × Space) :
    pairCoordinates ((natural.prod natural) a v) =
      repeated binaryNatural 2 a (pairCoordinates v) := by
  ext i j
  fin_cases i <;> rfl

private noncomputable def piCenter (m : FullCenter L (natural.prod natural)) :
    FullCenter L (repeated binaryNatural 2) where
  quotientIso := m.quotientIso
  equiv := m.equiv.trans pairCoordinates.toAddEquiv.toMultiplicative
  action l z := by
    change Multiplicative.ofAdd (pairCoordinates (m.equiv (centerConjugate L l z)).toAdd) = _
    rw [m.action]
    exact congrArg Multiplicative.ofAdd (pairCoordinates_action _ _)

private theorem mem_piCenter_plane (m : FullCenter L (natural.prod natural))
    (E : Subgroup G) (v : Fin 2 → Space) :
    v ∈ centerPlane (piCenter m) E ↔ pairCoordinates.symm v ∈ centerPlane m E := Iff.rfl

private noncomputable def doubledMarkedPlane (m : FullCenter L (natural.prod natural))
    (hE : E ≤ coreCenter L) (hcard : Nat.card E = 4)
    (P : Subgroup G) (hP : Nat.card ((P.subgroupOf L).map m.actor) = 24)
    (hn : P = L ⊓ normalizer (E : Set G))
    (hd : Disjoint (centerPlane (piCenter m) E)
      (fixedSpace (repeated binaryNatural 2) ((P.subgroupOf L).map m.actor))) :
    MarkedPlane m E := by
  have hs : ((P.subgroupOf L).map (piCenter m).actor) =
      subspaceStabilizer (repeated binaryNatural 2) (centerPlane (piCenter m) E) := by
    rw [hn, inf_subgroupOf_left]
    exact centerPlane_stabilizer (piCenter m) E hE
  let b := Classical.choice (BinaryGeometry.exists_binaryDoubledLine
    (centerPlane (piCenter m) E) ((P.subgroupOf L).map m.actor)
    ((centerPlane_card _ hE).trans hcard) hP hs.le hd)
  refine markedPlane_of_embedding m hE b.plane (plane_dimension _ b.plane_card)
    (pairCoordinates.symm.toLinearMap.comp b.embedding)
    (pairCoordinates.symm.injective.comp b.injective) ?_ ?_
  · intro a v
    apply pairCoordinates.injective
    change pairCoordinates (pairCoordinates.symm (b.embedding (natural a v))) =
      pairCoordinates ((natural.prod natural) a (pairCoordinates.symm (b.embedding v)))
    rw [LinearEquiv.apply_symm_apply, pairCoordinates_action,
      LinearEquiv.apply_symm_apply]
    exact b.equivariant a v
  · ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hmem : b.embedding w ∈ centerPlane (piCenter m) E := b.image.le ⟨w, hw, rfl⟩
      exact (mem_piCenter_plane m E _).mp hmem
    · intro hv
      have hh : pairCoordinates v ∈ b.plane.map b.embedding := by
        rw [b.image]
        apply (mem_piCenter_plane m E _).mpr
        rwa [pairCoordinates.symm_apply_apply]
      obtain ⟨w, hw, he⟩ := hh
      exact ⟨w, hw, (congrArg pairCoordinates.symm he).trans
        (pairCoordinates.symm_apply_apply v)⟩

variable [Finite G] {κ : GroupClass} {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

omit [Finite G] in
/-- Restricting the original quotient to M ∩ L gives the literal star parabolic. -/
theorem componentMap_parabolic_image :
    ((d.M ⊓ c.L).subgroupOf c.L).map (componentMap d c) =
      (d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L) := by
  ext a
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, component_le c l.property⟩, hl, rfl⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨⟨i, hi.2⟩, hi, Subtype.ext he⟩

private theorem linear_parabolic_card (s : SourceData κ d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq)
    (m : FullCenter c.L ρ) :
    Nat.card (((d.M ⊓ c.L).subgroupOf c.L).map m.actor) = 24 := by
  obtain ⟨q, hq⟩ := ms.quotient
  let f := q.symm.trans m.quotientIso
  have ha : m.actor = f.toMonoidHom.comp (componentMap d c) := by
    apply MonoidHom.ext
    intro l
    change m.quotientIso (QuotientGroup.mk' (pCore 2 c.L) l) =
      m.quotientIso (q.symm (componentMap d c l))
    rw [← hq, q.symm_apply_apply]
  rw [ha, ← map_map, componentMap_parabolic_image, card_map_of_injective f.injective]
  apply SourceReduction.marked_intersection_card_of_star_card d c hm
  exact (Nat.card_congr f.toEquiv).trans Matrix.PSL3Two.card_SL

/-- All three surviving linear cases acquire their actual V₂ marking.
The quotient actor is unchanged on the center and on both dual summands. -/
theorem linear_marked_models (s : SourceData κ d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq)
    (e : (c.L ⧸ pCore 2 c.L) ≃* SL)
    (h : MarkedMS.LinearThreeSurvivors c.L d.S e) :
    MarkedModels c.L d.V₂ (d.M ⊓ c.L) := by
  have hE := s.plane_le_coreCenter
  have hcard : Nat.card d.V₂ = 4 := d.action.card_plane _
  rcases linearModels_of_survivors e ms.core_eq h with
    ⟨m, _⟩ | ⟨⟨m, _⟩, _⟩ | ⟨⟨m, he⟩, hd, _⟩
  · exact .linearOne m (naturalMarkedPlane m.fullCenter hE hcard)
  · refine .linearTwo m (doubledMarkedPlane m.fullCenter hE hcard (d.M ⊓ c.L)
      (linear_parabolic_card s hm ms m.fullCenter) s.component_parabolic ?_)
    apply centerPlane_fixed_disjoint (piCenter m.fullCenter) d.V₂ d.Yplus (d.M ⊓ c.L)
    · exact s.component_residual ▸ map_subtype_le _
    · exact s.contains
    · exact s.line.plane_fixed_trivial d
  · refine .linearThree m (naturalMarkedPlane m hE hcard) ?_
    simpa only [FullCenter.actor, he,
      CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.linearThreeActor]
      using hd

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedModelAssembly

end
