module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.BorelRefinements.Marked
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.SourceFiltration
public import Theory.Representation.Quotient

/-!
# Borel coordinates on the literal source sections

Compatibility is stated using the original qH map and its actual images of
L₁ and L₁T. It contains no factor count or normalizer-equivariant marking.
The natural quotient map descends to the literal source U/V₁ section and
remains equivariant for conjugation by L₁T. The original duality embeds the
dual natural module in the literal Q_H/C_H(U) section. These maps prepare
the two natural contributions in 14.7.70 for chief refinement.

Construction of the compatible source marking and final five-factor assembly
remain with qt-14-07-rechoice-left-chief-factors. The earlier SectionCentralizer
input is 14.5.15(4), produced by qt-14-05. SourceDuality and the original
commutator identity come from 14.5.21(1–2), whose producer remains
qt-14-05-terminal-duality. No chief-count conclusion is asserted here.

Source: Aschbacher–Smith, combined manuscript, 14.7.70, p.1074/PDF p.1091.
-/

@[expose] public section
noncomputable section
open Subgroup NoncentralChiefRefinement Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Chapter12.Section08 Representation.SL2FourNatural
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

/-- The original qH restricted to the actual source group L₁T. -/
def sourceActorMap : B →* ChapterJ.S5 := d.qH.comp (Subgroup.inclusion group_le_H)

/-- The restricted homomorphism has the literal relative-subgroup image used by star notation. -/
theorem sourceActorMap_range :
    (sourceActorMap d).range = ((B).subgroupOf F.H).map d.qH := by
  ext g
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨Subgroup.inclusion group_le_H b, b.property, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h.val, hh⟩, rfl⟩

/-- The original qH/Borel compatibility still to be constructed by source assembly. -/
structure CompatibleBorel : Prop where
  left_image : ((F.Li L 1).subgroupOf F.H).map d.qH = borel d.naturalQuotient
  group_image : (sourceActorMap d).range = normalizer d.naturalQuotient

/-- The map to the actual symmetric normalizer; no new action is chosen. -/
def sourceNormalizerMap (h : CompatibleBorel d) : B →* normalizer d.naturalQuotient :=
  (sourceActorMap d).codRestrict _ (fun b => h.group_image ▸
    MonoidHom.mem_range.mpr ⟨b, rfl⟩)

theorem sourceNormalizerMap_surjective (h : CompatibleBorel d) :
    Function.Surjective (sourceNormalizerMap d h) := by
  intro n
  have hn : n.val ∈ (sourceActorMap d).range := h.group_image.symm ▸ n.property
  obtain ⟨b, hb⟩ := hn
  exact ⟨b, Subtype.ext hb⟩

/-- The source natural action is exactly the pullback of the marked normalizer action. -/
theorem source_action_eq (h : CompatibleBorel d) :
    (actorNatural d.naturalQuotient (normalizer d.naturalQuotient)).comp
      (sourceNormalizerMap d h) = d.naturalQuotient.action.comp (sourceActorMap d) := rfl

/-- The invariant natural line for the original L₁T actor. -/
def sourceLine (h : CompatibleBorel d) :
    Subrepresentation (d.naturalQuotient.action.comp (sourceActorMap d)) where
  toSubmodule := upperFixed
  apply_mem_toSubmodule b v hv := normalizer_preserves_line d.naturalQuotient
    (sourceNormalizerMap d h b) v hv

/-- Both irreducible actions survive pullback along the literal source map. -/
theorem sourceLine_irreducible (h : CompatibleBorel d) :
    IsIrreducible (sourceLine d h).toRepresentation := by
  change IsIrreducible (((actorLine d.naturalQuotient
    (normalizer d.naturalQuotient) le_rfl).toRepresentation).comp (sourceNormalizerMap d h))
  apply (irreducible_comp_surjective_iff _ (sourceNormalizerMap_surjective d h) _).mpr
  exact actorLine_irreducible d.naturalQuotient _ (borel d.naturalQuotient).le_normalizer le_rfl

theorem sourceQuotient_irreducible (h : CompatibleBorel d) :
    IsIrreducible (sourceLine d h).quotientRepresentation := by
  change IsIrreducible ((actorQuotient d.naturalQuotient
    (normalizer d.naturalQuotient) le_rfl).comp (sourceNormalizerMap d h))
  apply (irreducible_comp_surjective_iff _ (sourceNormalizerMap_surjective d h) _).mpr
  exact actorQuotient_irreducible d.naturalQuotient _ (borel d.naturalQuotient).le_normalizer le_rfl

theorem sourceLine_noncentral (h : CompatibleBorel d) :
    ∃ b v, (sourceLine d h).toRepresentation b v ≠ v := by
  obtain ⟨n, v, hv⟩ := actorLine_noncentral d.naturalQuotient (normalizer d.naturalQuotient)
    (borel d.naturalQuotient).le_normalizer le_rfl
  obtain ⟨b, hb⟩ := sourceNormalizerMap_surjective d h n
  refine ⟨b, v, ?_⟩
  change (actorLine d.naturalQuotient (normalizer d.naturalQuotient) le_rfl).toRepresentation
    (sourceNormalizerMap d h b) v ≠ v
  simpa only [hb] using hv

theorem sourceQuotient_noncentral (h : CompatibleBorel d) :
    ∃ b v, (sourceLine d h).quotientRepresentation b v ≠ v := by
  obtain ⟨n, v, hv⟩ := actorQuotient_noncentral d.naturalQuotient (normalizer d.naturalQuotient)
    (borel d.naturalQuotient).le_normalizer le_rfl
  obtain ⟨b, hb⟩ := sourceNormalizerMap_surjective d h n
  refine ⟨b, v, ?_⟩
  change actorQuotient d.naturalQuotient (normalizer d.naturalQuotient) le_rfl
    (sourceNormalizerMap d h b) v ≠ v
  simpa only [hb] using hv

/-- Forget the restriction to L₁T on an element of the original U node. -/
def sourceUInclusion : (sourceUNode d).val →* F.U where
  toFun v := ⟨v.val.val, v.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The original projection, before passing to the literal V₁ quotient. -/
def sourceNaturalCoordinates : (sourceUNode d).val →* Multiplicative SL2FourNatural.V :=
  d.projection.toLinearMap.toAddMonoidHom.toMultiplicative.comp
    (d.conjugationSection.coordinates.comp (sourceUInclusion d))

theorem sourceNaturalCoordinates_surjective (hc : d.SectionCentralizer) :
    Function.Surjective (sourceNaturalCoordinates d) := by
  intro v
  obtain ⟨w, hw⟩ := d.projection_onto v.toAdd
  obtain ⟨a, ha⟩ := d.conjugationSection.onto (Multiplicative.ofAdd w)
  obtain ⟨_, hUC, hCQ, hQB⟩ := source_filtration_containments d hc
  let a' : (sourceUNode d).val := ⟨⟨a.val, hQB (hCQ (hUC a.property))⟩, a.property⟩
  refine ⟨a', ?_⟩
  apply Multiplicative.toAdd.injective
  change d.projection (d.conjugationSection.coordinates a).toAdd = v.toAdd
  rw [ha]
  exact hw

/-- The denominator of the literal source section is killed by the original projection. -/
theorem point_le_natural_kernel :
    (sourcePointNode (F := F) (L := L)).val.subgroupOf (sourceUNode d).val ≤
      (sourceNaturalCoordinates d).ker := by
  intro a ha
  change sourceNaturalCoordinates d a = 1
  have hz := (d.conjugationSection.coordinates_eq_one_iff (sourceUInclusion d a)).mpr ha
  apply Multiplicative.toAdd.injective
  change d.projection (d.conjugationSection.coordinates (sourceUInclusion d a)).toAdd = 0
  rw [hz]
  exact map_zero d.projection

/-- The actual epimorphism U/V₁ onto the natural binary four-space. -/
def sourceNaturalMap :
    Section (sourcePointNode (F := F) (L := L)) (sourceUNode d) →*
      Multiplicative SL2FourNatural.V :=
  QuotientGroup.lift _ (sourceNaturalCoordinates d) (point_le_natural_kernel d)

theorem sourceNaturalMap_mk (v : (sourceUNode d).val) :
    sourceNaturalMap d (QuotientGroup.mk'
      ((sourcePointNode (F := F) (L := L)).val.subgroupOf (sourceUNode d).val) v) =
      Multiplicative.ofAdd (d.projection
        (d.conjugationSection.coordinates (sourceUInclusion d v)).toAdd) := rfl

theorem sourceNaturalMap_surjective (hc : d.SectionCentralizer) :
    Function.Surjective (sourceNaturalMap d) := by
  intro v
  obtain ⟨u, hu⟩ := sourceNaturalCoordinates_surjective d hc v
  exact ⟨QuotientGroup.mk' _ u, hu⟩

/-- Equivariance uses precisely sectionAction on the normal nodes in SourceFiltration. -/
theorem sourceNaturalMap_equivariant (b : B)
    (x : Section (sourcePointNode (F := F) (L := L)) (sourceUNode d)) :
    (sourceNaturalMap d (sectionAction _ _ b x)).toAdd =
      d.naturalQuotient.action (sourceActorMap d b) (sourceNaturalMap d x).toAdd := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective
    ((sourcePointNode (F := F) (L := L)).val.subgroupOf (sourceUNode d).val) x
  rw [sectionAction_mk, sourceNaturalMap_mk, sourceNaturalMap_mk]
  have he := d.conjugationSection.equivariant
    (Subgroup.inclusion group_le_H b) (sourceUInclusion d v)
  change d.projection _ = _
  rw [show (d.conjugationSection.coordinates
    (sourceUInclusion d (MulAut.conjNormal b v))).toAdd =
      d.action (Subgroup.inclusion group_le_H b)
        (d.conjugationSection.coordinates (sourceUInclusion d v)).toAdd from he]
  exact LinearMap.congr_fun (d.projection.isIntertwining' (Subgroup.inclusion group_le_H b)) _

variable {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- Forget the restriction to L₁T on an element of the original Q_H node. -/
def sourceQInclusion : (sourceQNode (F := F) (L := L)).val →* F.H.pCoreIn 2 where
  toFun q := ⟨q.val.val, q.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The original dual-section coordinates restricted to the literal core node. -/
def sourceQCoordinates (s : CriticalIntersections.SourceDuality F X Y) :
    (sourceQNode (F := F) (L := L)).val →* Multiplicative Y :=
  s.qSection.coordinates.comp (sourceQInclusion (F := F) (L := L))

theorem sourceQCoordinates_surjective (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y) :
    Function.Surjective (sourceQCoordinates (L := L) s) := by
  intro y
  obtain ⟨q, hq⟩ := s.qSection.onto y
  have hQB := (source_filtration_containments d hc).2.2.2
  exact ⟨⟨⟨q.val, hQB q.property⟩, q.property⟩, hq⟩

theorem sourceQCoordinates_kernel (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y) :
    (sourceQCoordinates (L := L) s).ker =
      (sourceCentralizerNode d).val.subgroupOf (sourceQNode (F := F) (L := L)).val := by
  ext q
  change s.qSection.coordinates (sourceQInclusion q) = 1 ↔ _
  rw [s.qSection.coordinates_eq_one_iff, q_centralizer_eq_h_centralizer d hc]
  rfl

/-- Genuine coordinates on Q_H/C_H(U), with the source centralizer denominator. -/
def sourceQEquiv (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y) :
    Section (sourceCentralizerNode d) (sourceQNode (F := F) (L := L)) ≃* Multiplicative Y :=
  (QuotientGroup.quotientMulEquivOfEq (sourceQCoordinates_kernel d hc s).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (sourceQCoordinates (L := L) s)
      (sourceQCoordinates_surjective d hc s))

theorem sourceQEquiv_mk (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y)
    (q : (sourceQNode (F := F) (L := L)).val) :
    sourceQEquiv d hc s (QuotientGroup.mk'
      ((sourceCentralizerNode d).val.subgroupOf (sourceQNode (F := F) (L := L)).val) q) =
      s.qSection.coordinates (sourceQInclusion q) := rfl

/-- The quotient coordinates retain the original dual-section conjugation action. -/
theorem sourceQEquiv_equivariant (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y) (b : B)
    (x : Section (sourceCentralizerNode d) (sourceQNode (F := F) (L := L))) :
    (sourceQEquiv d hc s (sectionAction _ _ b x)).toAdd =
      s.qAction (Subgroup.inclusion group_le_H b) (sourceQEquiv d hc s x).toAdd := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective
    ((sourceCentralizerNode d).val.subgroupOf (sourceQNode (F := F) (L := L)).val) x
  rw [sectionAction_mk, sourceQEquiv_mk, sourceQEquiv_mk]
  exact s.qSection.equivariant (Subgroup.inclusion group_le_H b) (sourceQInclusion q)

/-- The dual natural module embeds in the literal source Q_H/C_H(U) section.
The input is precisely the earlier duality and commutator identity, not a
chief count or a presumed equality C_U(Q_H)=V₁. -/
theorem exists_sourceDualEmbedding (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ∃ j : Multiplicative (Module.Dual (ZMod 2) SL2FourNatural.V) →*
        Section (sourceCentralizerNode d) (sourceQNode (F := F) (L := L)),
      Function.Injective j ∧
      ∀ (b : B) (a : Module.Dual (ZMod 2) SL2FourNatural.V),
        j (Multiplicative.ofAdd
          (Representation.dual (d.naturalQuotient.action.comp (sourceActorMap d)) b a)) =
          sectionAction _ _ b (j (Multiplicative.ofAdd a)) := by
  obtain ⟨j, hj, _⟩ := exists_dual_natural_embedding d hc s hcomm
  let f : Multiplicative (Module.Dual (ZMod 2) SL2FourNatural.V) →* Multiplicative Y :=
    j.toLinearMap.toAddMonoidHom.toMultiplicative
  let e := sourceQEquiv d hc s
  refine ⟨e.symm.toMonoidHom.comp f, ?_, ?_⟩
  · intro a b hab
    apply Multiplicative.toAdd.injective
    apply hj
    have he := congrArg e hab
    change e (e.symm (f a)) = e (e.symm (f b)) at he
    rw [e.apply_symm_apply, e.apply_symm_apply] at he
    exact congrArg Multiplicative.toAdd he
  · intro b a
    apply e.injective
    apply Multiplicative.toAdd.injective
    change (e (e.symm (f _))).toAdd = (e (sectionAction _ _ b (e.symm (f _)))).toAdd
    rw [e.apply_symm_apply, sourceQEquiv_equivariant, e.apply_symm_apply]
    exact LinearMap.congr_fun (j.isIntertwining' (Subgroup.inclusion group_le_H b)) a

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
