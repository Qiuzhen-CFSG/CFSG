module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.Small
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.BlockTransport

/-!
# The original alternating-six contradiction from the whole natural core

The intrinsic natural model makes the two-core quotient simple. Its canonical
comparison with the original star action preserves the marked parabolic.
The actual V₂ maps injectively to a two-dimensional natural plane. Aligning
the parabolic Sylow subgroup identifies its stabilizer, and dual detection
then generates the whole core from Y₊, giving the original contradiction.

Only shortness and the model of the whole core remain explicit; no ambient
block witness or MS classification is used. A natural constituent does not
supply these hypotheses.
Source: Aschbacher–Smith 15.3.31, printed p.1132, and C.1.32.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.CentralCover
open CentralCover.BlockModels MarkedModelAssembly MarkedModelAssembly.AlternatingCoordinates
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

omit [Finite G] in
/-- The original derived symplectic marking gives parabolic order 24 under
any natural marking of the full intrinsic component quotient. -/
theorem source_alternating_parabolic_card
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (m : Parabolics.RankTwoParabolicMarking d I c.L
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))
      Parabolics.symplecticDerivedParabolic)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Alternating.Actor) :
    Nat.card (((d.M ⊓ c.L).subgroupOf c.L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L)))) = 24 := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (c.L ⧸ pCore 2 c.L) := e.isSimpleGroup
  let q := coreQuotientEquivStar d c s.normal s.sylow s.sylow_eq
  let f := q.symm.trans e
  have ha : e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L)) =
      f.toMonoidHom.comp (componentMap d c) := by
    apply MonoidHom.ext
    intro l
    change e (QuotientGroup.mk' (pCore 2 c.L) l) =
      e (q.symm (componentMap d c l))
    rw [← coreQuotientEquivStar_apply d c s.normal s.sylow s.sylow_eq,
      q.symm_apply_apply]
  rw [ha, ← map_map, componentMap_parabolic_image, card_map_of_injective f.injective]
  have hc := Theory.SpecificGroups.SymplecticFour.Binary.card_derivedParabolic m.node
  change Nat.card (Parabolics.symplecticDerivedParabolic m.node) = 24 at hc
  rw [← m.intersection, card_map_of_injective m.equiv.injective] at hc
  exact hc

/-- The full natural core is enough for the original alternating-six
contradiction. No additional ambient block classification is a premise. -/
theorem source_alternating_false_of_natural_core
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (mark : Parabolics.RankTwoParabolicMarking d I c.L
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))
      Parabolics.symplecticDerivedParabolic)
    (short : ChapterC.IsShort c.L)
    (model : ChapterC.BlockModuleModel c.L (multiplicativeAction Alternating.action)) : False := by
  let P := ((d.M ⊓ c.L).subgroupOf c.L).map
    (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L)))
  obtain ⟨a, ha⟩ := conjugate_contains_T0 P (source_alternating_parabolic_card s mark model.quotientIso)
  let model' := conjugateModel model a
  let cm := centerModel short Alternating.action model'
  let W := quotientPlane cm s.plane_le_coreCenter
  have he : ((d.M ⊓ c.L).subgroupOf c.L).map cm.actorMap =
      P.map (MulAut.conj a).toMonoidHom := by
    rw [map_map]
    rfl
  have hs : ((d.M ⊓ c.L).subgroupOf c.L).map cm.actorMap ≤
      BlockModels.planeStabilizer Alternating.action W := by
    rintro _ ⟨l, hl, rfl⟩
    apply quotientPlane_stable cm s.plane_le_coreCenter
    have hh : (l : G) ∈ c.L ⊓ normalizer (d.V₂ : Set G) := s.component_parabolic ▸ hl
    exact hh.2
  have hi : Function.Injective (planeMap cm s.plane_le_coreCenter) :=
    planeMap_injective cm s.plane_le_coreCenter s.contains (s.line.plane_fixed_trivial d)
  have hd : Module.finrank (ZMod 2) W = 2 :=
    plane_dimension W ((quotientPlane_card cm s.plane_le_coreCenter hi).trans
      (d.action.card_plane _))
  have ht : ∀ g ∈ T0, W.map (BinaryPermutation.naturalRepresentation (Fin 6) g) = W := by
    intro g hg
    let t : Alternating.Actor := ⟨g, hg.2⟩
    have hm : t ∈ ((d.M ⊓ c.L).subgroupOf c.L).map cm.actorMap := by
      rw [he]
      exact ha hg
    exact (mem_planeStabilizer_iff_map _ _ t).mp (hs hm)
  have hp : ((d.M ⊓ c.L).subgroupOf c.L).map cm.actorMap =
      BlockModels.planeStabilizer Alternating.action W := by
    apply eq_of_le_of_card_ge hs
    rw [canonicalPlane_unique W hd ht, canonical_stabilizer_card]
    exact (source_alternating_parabolic_card s mark model'.quotientIso).ge
  exact ContainedCoreModels.alternating_excluded s short model' W hd ht hp

/-- Literal original 15.3.31 application of the alternating natural-core endpoint. -/
theorem source_lemma_15_3_31_alternating_natural_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I)
    (m : Parabolics.RankTwoParabolicMarking d I c.L
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))
      Parabolics.symplecticDerivedParabolic)
    (short : ChapterC.IsShort c.L)
    (model : ChapterC.BlockModuleModel c.L (multiplicativeAction Alternating.action)) : False := by
  obtain ⟨s⟩ := source_smallData hG d hempty hM hu hmany hshadow hI hf c
  exact source_alternating_false_of_natural_core s m short model

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
