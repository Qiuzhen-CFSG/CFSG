module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry

/-!
# The original starred Sylow image in 14.7.73

The paragraph before 14.7.65 identifies O₂(L₁*) as a Sylow subgroup of K*.
The two-core containment from the proof of 14.7.71 and S = O₂(L) therefore
force S* to be that same Sylow, once S ≤ K is established. We transport
this equality through the original H-marking and its original natural
SL₂(4)-marking; no new quotient isomorphism is selected.

The Steinberg commutator argument must supply S ≤ K. This file does not
assert that containment or the completed marked-image construction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.1069, 1075–1076 (14.7.64, 14.7.71 and 14.7.73).
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Images
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The two-core in this preceding source statement is in L₁*, not a
residual and not O₂(L₁) projected without justification. -/
def EarlierSylow : Prop :=
  Chapter1.IsSylowIn 2 ((star F (F.Li L 1)).pCoreIn 2) (star F (K F))

/-- The literal starred containment (*) in the proof of 14.7.71. -/
def TwoCoreImage : Prop :=
  (star F (F.Li L 1)).pCoreIn 2 ≤ star F (S L F)

omit [Finite G] in
/-- Public characterization of the earlier starred Sylow premise.  The
implementation remains opaque so consumers depend only on this source
contract. -/
theorem earlierSylow_iff :
    EarlierSylow (L := L) (F := F) ↔
      Chapter1.IsSylowIn 2 ((star F (F.Li L 1)).pCoreIn 2) (star F (K F)) :=
  Iff.rfl

omit [Finite G] in
/-- Public characterization of the starred two-core placement premise. -/
theorem twoCoreImage_iff :
    TwoCoreImage (L := L) (F := F) ↔
      (star F (F.Li L 1)).pCoreIn 2 ≤ star F (S L F) :=
  Iff.rfl

/-- The existing qK and qH agree on every subgroup already placed in K. -/
theorem image_marking (A : Subgroup G) (hAK : A ≤ K F) :
    (((A.subgroupOf (K F)).map (qK d)).map (alternatingActor d.naturalQuotient)) =
      (A.subgroupOf F.H).map d.qH := by
  rw [map_map]
  ext a
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, K_le_H F k.property⟩, hk, qK_marking d k⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hAK hh⟩, hh, (qK_marking d ⟨h, hAK hh⟩).symm⟩

omit [Finite G] in
/-- Sylow maximality proves the equality of the original starred images. -/
theorem star_eq_twoCore (hS : S L F = L.pCoreIn 2)
    (hSK : S L F ≤ K F) (he : EarlierSylow (L := L) (F := F))
    (h71 : TwoCoreImage (L := L) (F := F)) :
    star F (S L F) = (star F (F.Li L 1)).pCoreIn 2 := by
  obtain ⟨_, _, hmax⟩ := Chapter1.isSylowIn_iff.mp he
  exact hmax _ (((hS.symm ▸ isPGroup_pCoreIn 2 L).comap_subtype).map (starMap F))
    h71 (map_mono (subgroupOf_mono F.H hSK))

/-- An actual Sylow of the specified SL₂(4), using precisely the existing qK.
The only missing group containment here is the preceding Steinberg step. -/
theorem exists_sylow_image (hS : S L F = L.pCoreIn 2)
    (hSK : S L F ≤ K F) (he : EarlierSylow (L := L) (F := F))
    (h71 : TwoCoreImage (L := L) (F := F)) :
    ∃ R : Sylow 2 SL2FourNatural.SL,
      ((S L F).subgroupOf (K F)).map (qK d) = (R : Subgroup _) := by
  have hstar : Chapter1.IsSylowIn 2 (star F (S L F)) (star F (K F)) := by
    rw [star_eq_twoCore hS hSK he h71]
    exact he
  have hm := (Chapter1.IsSylowIn.map_iff d.model.toMonoidHom d.model.injective).mpr hstar
  have hK : (star F (K F)).map d.model.toMonoidHom = alternatingGroup (Fin 5) := by
    rw [CriticalFusion.Source.star, map_map]
    exact d.K_image
  rw [hK] at hm
  have hA : (star F (S L F)).map d.model.toMonoidHom =
      (((S L F).subgroupOf (K F)).map (qK d)).map (alternatingActor d.naturalQuotient) := by
    rw [image_marking d _ hSK, CriticalFusion.Source.star, map_map]
    rfl
  rw [hA] at hm
  have hi : Function.Injective (alternatingActor d.naturalQuotient) :=
    Subtype.coe_injective.comp d.naturalQuotient.marking.injective
  have ht : (⊤ : Subgroup SL2FourNatural.SL).map (alternatingActor d.naturalQuotient) =
      alternatingGroup (Fin 5) := by
    rw [alternatingActor, ← map_map, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr d.naturalQuotient.marking.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  rw [← ht] at hm
  obtain ⟨hp, _, hmax⟩ := Chapter1.isSylowIn_iff.mp
    ((Chapter1.IsSylowIn.map_iff _ hi).mp hm)
  exact ⟨⟨_, hp, fun hB hAB => hmax _ hB hAB le_top⟩, rfl⟩

include d in
/-- The original-root Sylow preimage consumer, with its marked-image premise
now discharged by the two earlier source image statements. -/
theorem source_sylow_of_twoCoreImage (hS : S L F = L.pCoreIn 2)
    (hSK : S L F ≤ K F) (he : EarlierSylow (L := L) (F := F))
    (h71 : TwoCoreImage (L := L) (F := F)) :
    ∃ R : Sylow 2 (K F),
      (R : Subgroup (K F)).map (K F).subtype = S L F ⊔ (K F).pCoreIn 2 := by
  obtain ⟨R, hR⟩ := exists_sylow_image d hS hSK he h71
  exact source_sylow d hSK R hR

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Images
