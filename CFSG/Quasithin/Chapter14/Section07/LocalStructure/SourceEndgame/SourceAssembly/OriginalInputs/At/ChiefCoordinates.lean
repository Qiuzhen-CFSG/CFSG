module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion.Maps
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion.Root
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Placement

/-!
# Literal chief coordinates at the fixed group

Restrict the original natural, dual and root maps to the three noncentral
intervals. Their kernels and equivariance retain the original L₁ actor.
Only the structural input at the original G,T is used. Earlier-source
construction and final discharge remain with qt-d-14775-source.
Source: Aschbacher–Smith 14.7.71–75, printed pp.1075–1078.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

private theorem upper_rank : Module.finrank (ZMod 2) SL2FourNatural.upperFixed = 2 := by
  have h := SL2FourNatural.card_upperFixed
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h
  exact Nat.pow_right_injective (by decide : 1 < 2) (h.trans (by decide : 4 = 2 ^ 2))

theorem source_seed_upper_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d) :
    (naturalSection d).imageSpace V = SL2FourNatural.upperFixed := by
  apply Submodule.eq_of_le_of_finrank_eq
  · obtain ⟨a, ha, t, ht, he⟩ := exists_upper_actor d c e.images mark e.image_order
    intro v hv
    obtain ⟨x, hx, rfl⟩ := ((naturalSection d).mem_imageSpace_iff _ _).mp hv
    have hc : (a:G) ∈ centralizer (V : Set G) := by
      rw [centralizer_seed_eq_Q_at d structural e.separation]
      exact S_le_Q_at d structural e.separation (critical_le_S c e.conjugate ha)
    have hfix : naturalAction d a (naturalMap d x).toAdd = (naturalMap d x).toAdd := by
      change naturalAction d a ((naturalSection d).coordinates x).toAdd = _
      rw [← (naturalSection d).equivariant a x]
      congr 2
      apply Subtype.ext
      exact (congrArg (fun z => z * (a:G)⁻¹) (hc x hx).symm).trans (by group)
    change d.naturalQuotient.action (d.qH a) (naturalMap d x).toAdd = _ at hfix
    rw [he] at hfix
    change d.naturalQuotient.action (d.naturalQuotient.marking (SL2FourNatural.upper t)) _ = _ at hfix
    rw [d.naturalQuotient.restriction, SL2FourNatural.upper_action] at hfix
    rw [SL2FourNatural.mem_upperFixed]
    have hh := congrFun hfix 0
    have hz : t * (naturalMap d x).toAdd 1 = 0 := add_left_cancel (show (naturalMap d x).toAdd 0 + t * (naturalMap d x).toAdd 1 = (naturalMap d x).toAdd 0 + 0 from by simpa using hh)
    exact (mul_eq_zero.mp hz).resolve_left ht
  · exact (seed_image_finrank d e.separation).trans upper_rank.symm

variable (m : F.Li L 1 →* borel d.naturalQuotient)
    (hm : ∀ l, (m l).val = d.qH (inclusion ((F.Li_le L 1).trans inf_le_right) l))

theorem firstCoordinates_kernel_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
    (hp : d.U₀ = F.Vi 1) (x : F.U) :
    firstCoordinates d x = 1 ↔ (x:G) ∈ V := by
  change SL2FourNatural.upperFixed.mkQ (naturalMap d x).toAdd = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    ← source_seed_upper_at d structural c e mark]
  exact natural_mem_seed_iff d hp x

variable (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)
    (b : QKDualCoordinates d)

def middleCoordinates_at : ↥(ChiefFactors.S F L ⊓ QK F) →* Multiplicative middleSpace where
  toFun x := Multiplicative.ofAdd ⟨(b.qSection.coordinates ⟨x,x.property.2⟩).toAdd, by
    have hC : (x:G) ∈ centralizer (V:Set G) :=
      (centralizer_seed_eq_Q_at d structural e.separation).symm ▸
        S_le_Q_at d structural e.separation x.property.1
    have hh := (mem_centralizer_iff_annihilator d b ⟨x,x.property.2⟩).mp hC
    simpa only [source_seed_upper_at d structural c e mark] using hh⟩
  map_one' := by apply Subtype.ext; exact congrArg Multiplicative.toAdd (map_one b.qSection.coordinates)
  map_mul' x y := by
    apply Subtype.ext
    change (b.qSection.coordinates (⟨x,x.property.2⟩ * ⟨y,y.property.2⟩)).toAdd =
      (b.qSection.coordinates ⟨x,x.property.2⟩).toAdd + (b.qSection.coordinates ⟨y,y.property.2⟩).toAdd
    exact congrArg Multiplicative.toAdd (map_mul b.qSection.coordinates _ _)

theorem middleCoordinates_surjective_at : Function.Surjective (middleCoordinates_at d structural c e mark b) := by
  intro v
  have hm : v.toAdd.val ∈ b.qSection.imageSpace (ChiefFactors.S F L ⊓ QK F) := by
    rw [source_intersection_image_at d structural c e mark b,
      intersection_image_eq_annihilator_at d structural e.separation b,
      source_seed_upper_at d structural c e mark]
    exact v.toAdd.property
  obtain ⟨q,hq,he⟩ := (b.qSection.mem_imageSpace_iff _ _).mp hm
  exact ⟨⟨q,hq⟩, Multiplicative.toAdd.injective (Subtype.ext he)⟩

theorem middleCoordinates_kernel_at (x : ↥(ChiefFactors.S F L ⊓ QK F)) :
    middleCoordinates_at d structural c e mark b x = 1 ↔ (x:G) ∈ ChiefFactors.S F L ⊓ C F := by
  constructor
  · intro h
    have hzero := congrArg (fun v : Multiplicative middleSpace => v.toAdd.val) h
    exact ⟨x.property.1, (b.qSection.coordinates_eq_one_iff ⟨x,x.property.2⟩).mp
      (Multiplicative.toAdd.injective hzero)⟩
  · intro h
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      ((b.qSection.coordinates_eq_one_iff ⟨x,x.property.2⟩).mpr h.2)

include hm in
theorem middleCoordinates_equivariant_at (l : F.Li L 1) (x : ↥(ChiefFactors.S F L ⊓ QK F)) :
    (middleCoordinates_at d structural c e mark b
      ⟨(l:G)*x*(l:G)⁻¹, (mem_normalizer_iff.mp (L_normalizes_S ((F.Li_le L 1 l.property).1)) x).mp x.property.1,
        (mem_normalizer_iff.mp (b.qSection.normalized ((F.Li_le L 1 l.property).2)) x).mp x.property.2⟩).toAdd =
      middleTarget d m l (middleCoordinates_at d structural c e mark b x).toAdd := by
  apply Subtype.ext
  change (b.qSection.coordinates _).toAdd =
    (d.naturalQuotient.action (m l).val⁻¹).dualMap (b.qSection.coordinates ⟨x,x.property.2⟩).toAdd
  apply LinearMap.ext
  intro v
  have hh := LinearMap.congr_fun
    (b.qSection.equivariant (inclusion ((F.Li_le L 1).trans inf_le_right) l) ⟨x,x.property.2⟩) v
  change _ = (b.qSection.coordinates ⟨x,x.property.2⟩).toAdd
    (d.naturalQuotient.action (d.qH (inclusion ((F.Li_le L 1).trans inf_le_right) l)⁻¹) v) at hh
  have hq : d.qH (inclusion ((F.Li_le L 1).trans inf_le_right) l)⁻¹ = (m l).val⁻¹ :=
    (d.qH.map_inv _).trans (congrArg Inv.inv (hm l).symm)
  exact hh.trans (congrArg (fun g : ChapterJ.S5 =>
    (b.qSection.coordinates ⟨x,x.property.2⟩).toAdd (d.naturalQuotient.action g v)) hq)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Representation.SL2FourNatural.BorelDualCore
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The original qH on L₁, with its exact marked Borel codomain. -/
def leftBorelMap_at (hb : CompatibleBorel d) : F.Li L 1 →* borel d.naturalQuotient :=
  (d.qH.comp (Subgroup.inclusion ((F.Li_le L 1).trans inf_le_right))).codRestrict _
    (fun l => hb.left_image ▸ Subgroup.mem_map.mpr
      ⟨Subgroup.inclusion ((F.Li_le L 1).trans inf_le_right) l, l.property, rfl⟩)

/-- Forgetting the codomain restriction retains the original qH map. -/
theorem leftBorelMap_val_at (hb : CompatibleBorel d) (l : F.Li L 1) :
    (leftBorelMap_at d hb l).val =
      d.qH (Subgroup.inclusion ((F.Li_le L 1).trans inf_le_right) l) := by rfl

theorem leftBorelMap_surjective_at (hb : CompatibleBorel d) :
    Function.Surjective (leftBorelMap_at d hb) := by
  intro b
  have hmem : b.val ∈ ((F.Li L 1).subgroupOf F.H).map d.qH :=
    hb.left_image.symm ▸ b.property
  obtain ⟨l, hl, he⟩ := hmem
  exact ⟨⟨l.val, hl⟩, Subtype.ext he⟩

/-- The root representation with the literal L₁ actor. -/
def rootRepresentation_at (hb : CompatibleBorel d) :
    Representation (ZMod 2) (F.Li L 1) SL2FourNatural.F :=
  (actorCore d.naturalQuotient (borel d.naturalQuotient)
    (borel d.naturalQuotient).le_normalizer).comp (leftBorelMap_at d hb)

theorem rootRepresentation_irreducible_at (hb : CompatibleBorel d) :
    IsIrreducible (rootRepresentation_at d hb) := by
  apply (irreducible_comp_surjective_iff _ (leftBorelMap_surjective_at d hb) _).mpr
  exact actorCore_irreducible d.naturalQuotient _ le_rfl
    (borel d.naturalQuotient).le_normalizer

theorem rootRepresentation_noncentral_at (hb : CompatibleBorel d) :
    ∃ l v, rootRepresentation_at d hb l v ≠ v := by
  obtain ⟨b, v, hv⟩ := actorCore_noncentral d.naturalQuotient
    (borel d.naturalQuotient) le_rfl (borel d.naturalQuotient).le_normalizer
  obtain ⟨l, hl⟩ := leftBorelMap_surjective_at d hb b
  refine ⟨l, v, ?_⟩
  change actorCore d.naturalQuotient (borel d.naturalQuotient)
    (borel d.naturalQuotient).le_normalizer (leftBorelMap_at d hb l) v ≠ v
  simpa only [hl] using hv

private theorem marked_star (A : Subgroup G) :
    (star F A).map d.model.toMonoidHom = (A.subgroupOf F.H).map d.qH := by
  rw [CriticalFusion.Source.star, map_map]
  rfl

variable (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
  (c : CriticalPath (L := L) F) (e : Earlier d c) (mark : UpperMarking d)

include structural c e mark in
/-- Both containments retain the original quotient map and the original S. -/
theorem root_image_at :
    ((SteinbergRecognition.S F L).subgroupOf F.H).map d.qH = root d.naturalQuotient := by
  apply le_antisymm
  · have hQ : ((Q T L).subgroupOf F.H).map d.qH = root d.naturalQuotient := by
      rw [← marked_star, e.images.image_eq, marked_star]
      exact mark
    exact (map_mono (subgroupOf_mono F.H (S_le_Q_at d structural e.separation))).trans_eq hQ
  · have h := map_mono (f := d.model.toMonoidHom)
      (star_twoCore_le_S_at d structural c e mark)
    rw [map_pCoreIn_of_injective 2 _ _ d.model.injective, marked_star, marked_star,
      (compatibleBorel_of_upperMarking_at d structural mark).left_image, borel_twoCore] at h
    exact h

include structural c e in
private theorem span_le_H : SteinbergRecognition.S F L ≤ F.H :=
  (S_le_Q_at d structural e.separation).trans (Q_le_H F)

/-- qH restricted to the actual span, before additive root coordinates. -/
def rootMap_at : SteinbergRecognition.S F L →* root d.naturalQuotient :=
  (d.qH.comp (Subgroup.inclusion (by exact span_le_H d structural c e))).codRestrict _
    (fun s => root_image_at d structural c e mark ▸ Subgroup.mem_map.mpr
      ⟨Subgroup.inclusion (by exact span_le_H d structural c e) s, s.property, rfl⟩)

theorem rootMap_surjective_at : Function.Surjective (rootMap_at d structural c e mark) := by
  intro r
  have hmem : r.val ∈ ((SteinbergRecognition.S F L).subgroupOf F.H).map d.qH :=
    (root_image_at d structural c e mark).symm ▸ r.property
  obtain ⟨s, hs, he⟩ := hmem
  exact ⟨⟨s.val, hs⟩, Subtype.ext he⟩

/-- Actual S/(S∩Q_H) coordinates, without assuming S lies in the actor. -/
def rootCoordinate_at : SteinbergRecognition.S F L →* Multiplicative SL2FourNatural.F :=
  (rootCoordinates d.naturalQuotient).toMonoidHom.comp (rootMap_at d structural c e mark)

theorem rootCoordinate_surjective_at :
    Function.Surjective (rootCoordinate_at d structural c e mark) :=
  (rootCoordinates d.naturalQuotient).surjective.comp (rootMap_surjective_at d structural c e mark)

theorem rootCoordinate_kernel_at (s : SteinbergRecognition.S F L) :
    rootCoordinate_at d structural c e mark s = 1 ↔ (s : G) ∈ F.H.pCoreIn 2 := by
  change rootCoordinates d.naturalQuotient (rootMap_at d structural c e mark s) = 1 ↔ _
  rw [map_eq_one_iff _ (rootCoordinates d.naturalQuotient).injective]
  change (⟨d.qH (Subgroup.inclusion (by exact span_le_H d structural c e) s), _⟩ :
    root d.naturalQuotient) = 1 ↔ _
  rw [Subtype.ext_iff]
  change Subgroup.inclusion (by exact span_le_H d structural c e) s ∈ d.qH.ker ↔ _
  rw [d.qH_ker]
  rfl

omit [Finite G] in
/-- The normalization needed to state the original L₁ conjugation action. -/
theorem left_normalizes_span_at : F.Li L 1 ≤ normalizer (SteinbergRecognition.S F L : Set G) :=
  ((F.Li_le L 1).trans inf_le_left).trans SteinbergRecognition.L_normalizes_S

/-- The root coordinates intertwine actual ambient conjugation, not a chosen action. -/
theorem rootCoordinate_equivariant_at (hb : CompatibleBorel d)
    (l : F.Li L 1) (s : SteinbergRecognition.S F L) :
    (rootCoordinate_at d structural c e mark
      ⟨(l : G) * s * (l : G)⁻¹,
        (mem_normalizer_iff.mp (left_normalizes_span_at (F := F) (L := L) l.property) s).mp
          s.property⟩).toAdd =
      rootRepresentation_at d hb l (rootCoordinate_at d structural c e mark s).toAdd := by
  have he := coordinateAction_equivariant (root d.naturalQuotient)
    (rootCoordinates d.naturalQuotient)
    (Subgroup.inclusion ((borel d.naturalQuotient).le_normalizer.trans
      (normalizer_le_root_normalizer d.naturalQuotient)) (leftBorelMap_at d hb l))
    (rootMap_at d structural c e mark s)
  change _ = (coordinateAction (root d.naturalQuotient) (rootCoordinates d.naturalQuotient)
    _ ((rootCoordinates d.naturalQuotient) (rootMap_at d structural c e mark s)).toAdd)
  rw [← he]
  apply congrArg Multiplicative.toAdd
  apply congrArg (rootCoordinates d.naturalQuotient)
  apply Subtype.ext
  rw [normalizerMonoidHom_apply_apply_coe]
  let lH : F.H := Subgroup.inclusion ((F.Li_le L 1).trans inf_le_right) l
  let sH : F.H := Subgroup.inclusion (by exact span_le_H d structural c e) s
  change d.qH (lH * sH * lH⁻¹) = d.qH lH * d.qH sH * (d.qH lH)⁻¹
  simp only [map_mul, map_inv]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion
