module
public import Theory.Representation.SL2FourNaturalOrbits.BorelDualCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.BorelRefinements.SourceCoordinates
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
public import Theory.GroupTheory.PCoreRestriction
/-!
# Dual and root factors for the marked Borel and its normalizer

The dual flag is the annihilator of the natural flag, using the literal
contragredient action. The marked root is the embedded two-core of both actors;
its conjugation action retains its additive-field coordinates and one-copy
chief-section coordinates. No normalizer-equivariant SL₂ marking is assumed.
The final conditional application pulls the dual flag through the original qH
map and the existing embedding into QH/CH(U).

Source: Aschbacher–Smith 14.7.70, printed p.1074/PDF p.1091.
The source marking, earlier 14.5.21 duality, and final count remain with their
existing assembly owners; they are explicit hypotheses here.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Subgroup Representation Representation.SL2FourNatural
open Representation.SL2FourNatural.BorelFactors Representation.SL2FourNatural.BorelDualCore
open Matrix.SpecialLinearGroup
variable (r : ChapterJ.L2FourAction)

/-- The annihilator flag in the literal contragredient action. -/
def actorDualLine (A : Subgroup ChapterJ.S5) (hAN : A ≤ normalizer r) :
    Subrepresentation (actorNatural r A).dual :=
  annihilator (actorNatural r A) (actorLine r A hAN)

abbrev actorDualQuotient (A : Subgroup ChapterJ.S5) (hAN : A ≤ normalizer r) :=
  (actorDualLine r A hAN).quotientRepresentation

def actorDualLineEquiv (A : Subgroup ChapterJ.S5) (hAN : A ≤ normalizer r) :
    RepEquiv (actorDualLine r A hAN).toRepresentation (actorQuotient r A hAN).dual :=
  annihilatorEquiv (actorNatural r A) (actorLine r A hAN)

def actorDualQuotientEquiv (A : Subgroup ChapterJ.S5) (hAN : A ≤ normalizer r) :
    RepEquiv (actorDualQuotient r A hAN) (actorLine r A hAN).toRepresentation.dual :=
  annihilatorQuotientEquiv (actorNatural r A) (actorLine r A hAN)

variable (A : Subgroup ChapterJ.S5) (hBA : borel r ≤ A) (hAN : A ≤ normalizer r)

include hBA in
theorem actorDualLine_irreducible : IsIrreducible (k := ZMod 2) (G := A) (V := (actorDualLine r A hAN).toSubmodule)
      (actorDualLine r A hAN).toRepresentation := by
  let := actorQuotient_irreducible r A hBA hAN
  exact annihilator_irreducible _ _

include hBA in
theorem actorDualQuotient_irreducible : IsIrreducible (actorDualQuotient r A hAN) := by
  let := actorLine_irreducible r A hBA hAN
  exact annihilatorQuotient_irreducible _ _

include hBA in
theorem actorDualLine_noncentral : ∃ g f, (actorDualLine r A hAN).toRepresentation g f ≠ f :=
  annihilator_noncentral _ _ (actorQuotient_noncentral r A hBA hAN)

include hBA in
theorem actorDualQuotient_noncentral : ∃ g f, actorDualQuotient r A hAN g f ≠ f :=
  annihilatorQuotient_noncentral _ _ (actorLine_noncentral r A hBA hAN)

theorem actorDualLine_finrank :
    Module.finrank (ZMod 2) (actorDualLine r A hAN).toSubmodule = 2 := by
  rw [(actorDualLineEquiv r A hAN).toLinearEquiv.finrank_eq, Subspace.dual_finrank_eq]
  exact quotient_finrank

theorem actorDualQuotient_finrank :
    Module.finrank (ZMod 2) (Module.Dual (ZMod 2) V ⧸ (actorDualLine r A hAN).toSubmodule) = 2 := by
  rw [(actorDualQuotientEquiv r A hAN).toLinearEquiv.finrank_eq, Subspace.dual_finrank_eq]
  exact line_finrank

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Subgroup Representation Representation.SL2FourNatural
open Representation.SL2FourNatural.BorelDualCore
open Chapter12.Section08 NoncentralChiefRefinement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

/-- The source flag uses exactly the dual action in exists_sourceDualEmbedding. -/
def sourceDualLine (h : CompatibleBorel d) :
    Subrepresentation (Representation.dual (d.naturalQuotient.action.comp (sourceActorMap d))) :=
  annihilator _ (sourceLine d h)

/-- Pullback along the literal qH map commutes with this contragredient action. -/
theorem source_dual_action_eq (h : CompatibleBorel d) :
    (actorNatural d.naturalQuotient (normalizer d.naturalQuotient)).dual.comp
      (sourceNormalizerMap d h) =
      (Representation.dual (d.naturalQuotient.action.comp (sourceActorMap d))) := by
  apply MonoidHom.ext
  intro b
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro v
  change a (d.naturalQuotient.action ((sourceActorMap d b)⁻¹) v) =
    a (d.naturalQuotient.action (sourceActorMap d b⁻¹) v)
  exact congrArg (fun g : ChapterJ.S5 => a (d.naturalQuotient.action g v))
    ((sourceActorMap d).map_inv b).symm

theorem sourceDualLine_irreducible (h : CompatibleBorel d) :
    IsIrreducible (k := ZMod 2) (G := B) (V := (sourceDualLine d h).toSubmodule)
      (sourceDualLine d h).toRepresentation := by
  let := sourceQuotient_irreducible d h
  exact annihilator_irreducible _ _

theorem sourceDualQuotient_irreducible (h : CompatibleBorel d) :
    IsIrreducible (sourceDualLine d h).quotientRepresentation := by
  let := sourceLine_irreducible d h
  exact annihilatorQuotient_irreducible _ _

/-- Both factors on the original source actor retain a moving vector. -/
theorem sourceDual_factors_noncentral (h : CompatibleBorel d) :
    (∃ b f, (sourceDualLine d h).toRepresentation b f ≠ f) ∧
    (∃ b f, (sourceDualLine d h).quotientRepresentation b f ≠ f) := by
  exact ⟨annihilator_noncentral _ _ (sourceQuotient_noncentral d h),
    annihilatorQuotient_noncentral _ _ (sourceLine_noncentral d h)⟩

theorem sourceDualLine_finrank (h : CompatibleBorel d) :
    Module.finrank (ZMod 2) (sourceDualLine d h).toSubmodule = 2 :=
  actorDualLine_finrank d.naturalQuotient _ le_rfl

theorem sourceDualQuotient_finrank (h : CompatibleBorel d) :
    Module.finrank (ZMod 2) (Module.Dual (ZMod 2) SL2FourNatural.V ⧸
      (sourceDualLine d h).toSubmodule) = 2 :=
  actorDualQuotient_finrank d.naturalQuotient _ le_rfl

variable {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- The annihilator's inclusion followed by the already constructed dual embedding.
This records the actual flag in QH/CH(U), with its original section action. -/
theorem exists_sourceDualFlagEmbedding (h : CompatibleBorel d) (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ∃ j : Multiplicative (Module.Dual (ZMod 2) SL2FourNatural.V) →*
        Section (sourceCentralizerNode d) (sourceQNode (F := F) (L := L)),
      Function.Injective j ∧
      (∀ (b : B) (a : Module.Dual (ZMod 2) SL2FourNatural.V),
        j (Multiplicative.ofAdd
          ((Representation.dual (d.naturalQuotient.action.comp (sourceActorMap d))) b a)) =
          sectionAction _ _ b (j (Multiplicative.ofAdd a))) ∧
      (∀ (b : B) (a : (sourceDualLine d h).toSubmodule),
        j (Multiplicative.ofAdd ((sourceDualLine d h).toRepresentation b a).val) =
          sectionAction _ _ b (j (Multiplicative.ofAdd a.val))) := by
  obtain ⟨j, hj, he⟩ := exists_sourceDualEmbedding d hc s hcomm
  exact ⟨j, hj, he, fun b a => he b a.val⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Subgroup Representation Representation.SL2FourNatural
open Representation.SL2FourNatural.BorelFactors Representation.SL2FourNatural.BorelDualCore
open Matrix.SpecialLinearGroup
open Theory.SpecificGroups.Alternating
open scoped commutatorElement
variable (r : ChapterJ.L2FourAction)

/-- The prescribed marking identifies this Borel with an even point stabilizer. -/
theorem borel_eq_even_stabilizer : ∃ i : Fin 5,
    borel r = alternatingGroup (Fin 5) ⊓ MulAction.stabilizer ChapterJ.S5 i := by
  let P := (upperUnipotentSylow F 2).mapSurjective (f := r.marking.toMonoidHom)
    r.marking.surjective
  obtain ⟨i, hi⟩ := FiveBorelOvergroups.sylow_normalizer_eq_stabilizer P
  have hb : B0.map r.marking.toMonoidHom = MulAction.stabilizer (alternatingGroup (Fin 5)) i := by
    rw [B0, rankOneBorel, map_equiv_normalizer_eq]
    exact hi
  refine ⟨i, ?_⟩
  rw [borel, markingHom, ← map_map, hb]
  ext x
  exact ⟨fun ⟨y, hy, he⟩ => he ▸ ⟨y.property, hy⟩,
    fun ⟨ha, hi⟩ => ⟨⟨x, ha⟩, hi, rfl⟩⟩

theorem normalizer_le_root_normalizer :
    normalizer r ≤ Subgroup.normalizer (root r : Set ChapterJ.S5) := by
  rw [← borel_twoCore]
  exact normalizer_le_normalizer_characteristic_image (borel r) (pCore 2 (borel r))

/-- The normalizer has the same embedded two-core as the Borel. -/
theorem normalizer_twoCore : (normalizer r).pCoreIn 2 = root r := by
  have hBN : borel r ≤ normalizer r := (borel r).le_normalizer
  have hn : normalizer r ≤ Subgroup.normalizer ((normalizer r).pCoreIn 2 : Set ChapterJ.S5) :=
    (normalizer r).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (normalizer r)))
  have hCB : (normalizer r).pCoreIn 2 ≤ borel r := by
    obtain ⟨i, hi⟩ := borel_eq_even_stabilizer r
    have hN : normalizer r = MulAction.stabilizer ChapterJ.S5 i := by
      rw [normalizer, hi, FiveBorelCentralFactor.even_stabilizer_normalizer]
    intro t ht
    have hti : t i = i := by
      have htN := pCoreIn_le 2 (normalizer r) ht
      rw [hN] at htN
      exact htN
    have heven : t ∈ alternatingGroup (Fin 5) := by
      by_contra heven
      obtain ⟨b, hb, hcube, hne⟩ := FiveBorelCentralFactor.odd_actor_cubic_witness i t hti
        (fun he => heven (Equiv.Perm.mem_alternatingGroup.mpr he))
      have hbN : b ∈ normalizer r := hBN (hi.symm ▸ hb)
      have hc : ⁅b, t⁆ ∈ (normalizer r).pCoreIn 2 := by
        rw [commutatorElement_def]
        exact (normalizer r).pCoreIn 2 |>.mul_mem
          ((Subgroup.mem_normalizer_iff.mp (hn hbN) t).mp ht)
          ((normalizer r).pCoreIn 2 |>.inv_mem ht)
      let c : (normalizer r).pCoreIn 2 := ⟨⁅b, t⁆, hc⟩
      have hpow : c ^ 3 = 1 := Subtype.ext hcube
      have hcop := (isPGroup_pCoreIn 2 (normalizer r)).orderOf_coprime
        (by decide : Nat.Coprime 2 3) c
      have hc1 : c = 1 := orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (orderOf_dvd_of_pow_eq_one hpow))
      exact hne (congrArg Subtype.val hc1)
    rw [hi]
    exact ⟨heven, hti⟩
  apply le_antisymm
  · rw [← borel_twoCore]
    exact (le_inf hCB le_rfl).trans (inf_pCoreIn_le_of_le 2 hBN)
  · rw [← borel_twoCore]
    exact pCoreIn_mono_of_normalizes hBN le_rfl

/-- The marked root has actual additive-field coordinates. -/
def rootCoordinates : root r ≃* Multiplicative F :=
  (U0.equivMapOfInjective (markingHom r) (markingHom_injective r)).symm.trans upperCoordinates

theorem rootCoordinates_symm (b : F) :
    (rootCoordinates r |>.symm (Multiplicative.ofAdd b)).val = markingHom r (upper b) := by
  change markingHom r (upperCoordinates.symm (Multiplicative.ofAdd b)).val = _
  rw [upperCoordinates_symm]

variable (A : Subgroup ChapterJ.S5) (hBA : borel r ≤ A) (hAN : A ≤ normalizer r)

/-- The actual actor's conjugation on the core in the marked additive coordinates. -/
def actorCore : Representation (ZMod 2) A F :=
  (coordinateAction (root r) (rootCoordinates r)).comp
    (Subgroup.inclusion (hAN.trans (normalizer_le_root_normalizer r)))

include hBA in
theorem actorCore_restriction (g : B0) (b : F) :
    actorCore r A hAN (borelToActor r A hBA g) b = coreAction g b := by
  apply Multiplicative.ofAdd.injective
  apply (rootCoordinates r).symm.injective
  apply Subtype.ext
  change ((rootCoordinates r).symm ((rootCoordinates r) ((root r).normalizerMonoidHom
    ⟨markingHom r g.val, _⟩ ((rootCoordinates r).symm (Multiplicative.ofAdd b))))).val = _
  rw [MulEquiv.symm_apply_apply]
  change markingHom r g.val * ((rootCoordinates r).symm (Multiplicative.ofAdd b)).val *
    (markingHom r g.val)⁻¹ = _
  rw [rootCoordinates_symm, rootCoordinates_symm, coreAction_apply,
    ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [upper_eq_transvection, upper_eq_transvection,
    triangular_conj_upper ((mem_rankOneBorel_iff _).mp g.property)]

include hBA in
theorem actorCore_irreducible : IsIrreducible (actorCore r A hAN) := by
  apply irreducible_of_transitive
  intro b c hb hc
  obtain ⟨g, hg⟩ := coreAction_transitive b c hb hc
  exact ⟨borelToActor r A hBA g, (actorCore_restriction r A hBA hAN g b).trans hg⟩

include hBA in
theorem actorCore_noncentral : ∃ g b, actorCore r A hAN g b ≠ b := by
  obtain ⟨g, b, hb⟩ := coreAction_noncentral
  exact ⟨borelToActor r A hBA g, b, fun he =>
    hb ((actorCore_restriction r A hBA hAN g b).symm.trans he)⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Subgroup Representation Representation.SL2FourNatural NoncentralChiefRefinement
open Representation.SL2FourNatural.BorelDualCore
variable (r : ChapterJ.L2FourAction) (A : Subgroup ChapterJ.S5)
  (hBA : borel r ≤ A) (hAN : A ≤ normalizer r)

include hBA in
theorem root_le_actor : root r ≤ A := by
  rw [← borel_twoCore]
  exact (pCoreIn_le 2 (borel r)).trans hBA

/-- The actual root is normal in each permitted actor. -/
def rootNode : NormalNode A :=
  ⟨(root r).subgroupOf A,
    (normal_subgroupOf_iff_le_normalizer (root_le_actor r A hBA)).mpr
      (hAN.trans (normalizer_le_root_normalizer r))⟩

/-- Forgetting the actor subtype retains the original marked root coordinates. -/
def actorCoreCoordinates : (rootNode r A hBA hAN).val ≃* Multiplicative F :=
  (subgroupOfEquivOfLe (root_le_actor r A hBA)).trans (rootCoordinates r)

theorem actorCoreCoordinates_equivariant (g : A) (x : (rootNode r A hBA hAN).val) :
    (actorCoreCoordinates r A hBA hAN (MulAut.conjNormal g x)).toAdd =
      actorCore r A hAN g (actorCoreCoordinates r A hBA hAN x).toAdd :=
  coordinateAction_equivariant (root r) (rootCoordinates r)
    ⟨g.val, (hAN.trans (normalizer_le_root_normalizer r)) g.property⟩
    ⟨x.val.val, x.property⟩

/-- Literal one-copy coordinates on the root section, specializing to both actual cores. -/
def coreSectionCoordinates : SectionCoordinates ⊥ (rootNode r A hBA hAN)
    (actorCore r A hAN) 1 :=
  singleCoordinates _ _ (actorCoreCoordinates r A hBA hAN)
    (actorCoreCoordinates_equivariant r A hBA hAN)

/-- The supplied coordinates feed the chief-interval API without a chiefness assumption. -/
theorem rootNode_covBy : (⊥ : NormalNode A) ⋖ rootNode r A hBA hAN := by
  let := actorCore_irreducible r A hBA hAN
  exact (coreSectionCoordinates r A hBA hAN).covBy bot_le (actorCore_noncentral r A hBA hAN)

/-- The Borel node is its intrinsic core, with the original subgroup embedding. -/
theorem rootNode_borel_eq_core :
    (rootNode r (borel r) le_rfl (borel r).le_normalizer).val = pCore 2 (borel r) := by
  change (root r).subgroupOf (borel r) = _
  rw [← borel_twoCore]
  exact (pCore 2 (borel r)).comap_map_eq_self_of_injective (borel r).subtype_injective

/-- The normalizer node is its intrinsic core, with the original subgroup embedding. -/
theorem rootNode_normalizer_eq_core :
    (rootNode r (normalizer r) (borel r).le_normalizer le_rfl).val =
      pCore 2 (normalizer r) := by
  change (root r).subgroupOf (normalizer r) = _
  rw [← normalizer_twoCore]
  exact (pCore 2 (normalizer r)).comap_map_eq_self_of_injective (normalizer r).subtype_injective

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
