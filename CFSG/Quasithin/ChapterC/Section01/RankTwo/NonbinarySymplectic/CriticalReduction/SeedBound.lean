module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.VertexAction
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowSeedCard

/-!
# Size of the literal fixed Sylow seed on the replacement

A Sylow two-subgroup of the actual vertex residual maps onto a full Sylow
of the natural symplectic actor. The replacement's proved cover therefore
bounds its literal fixed subgroup by q squared, retaining all fixed central
attachments. The coefficient field is compared with the original input field
by its proved degree, rather than specialized to four elements.

This supplies the fixed-seed size input to the nonbinary star argument.
Source: MS93 (3.2)(vi) and (3.4), pp.864 and 868.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

include h

/-- The full component Sylow fixes at most q² elements of the literal U layer,
including the kernel of its natural projection. -/
theorem Input.replacement_componentSylowSeed_card_le
    {a : Vertex d.radical} (ha : color d.radical a = false)
    (P : Sylow 2 (Ltilde d.radical a)) :
    Nat.card (U d.radical a ⊓ centralizer
      (((P : Subgroup (Ltilde d.radical a)).map (Ltilde d.radical a).subtype) :
        Set (FreeAmalgam d.radical)) : Subgroup (FreeAmalgam d.radical)) ≤ Nat.card F ^ 2 := by
  obtain ⟨E,hE,e,he,j,hj,hjU,f,hf,hact,_⟩ := h.replacement_initial_cover_at_vertex d ha
  let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) (QuotientGroup.mk' (pCore 2 d.overgroup))
    (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  let T := (P : Subgroup (Ltilde d.radical a)).map (Ltilde d.radical a).subtype
  let actorEquiv : (P : Subgroup (Ltilde d.radical a)) ≃* T :=
    (P : Subgroup (Ltilde d.radical a)).equivMapOfInjective
      (Ltilde d.radical a).subtype (Ltilde d.radical a).subtype_injective
  let π : T →* L (K := E.Carrier) :=
    (f.comp (P : Subgroup (Ltilde d.radical a)).subtype).comp actorEquiv.symm.toMonoidHom
  let := finite_stabilizer d.radical a
  let : Finite (Ltilde d.radical a) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer a)) (inclusion_injective _)
  let S := P.mapSurjective (f := f) hf
  have hπ : π.range = (S : Subgroup (L (K := E.Carrier))) := by
    change π.range = (P.mapSurjective (f := f) hf : Subgroup _)
    rw [Sylow.coe_mapSurjective,MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective actorEquiv.symm.toMonoidHom actorEquiv.symm.surjective,
      ← MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype]
  have hT (t : T) (v : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (π t) v)) =
        (t : FreeAmalgam d.radical) * j (Multiplicative.ofAdd v) * (t : FreeAmalgam d.radical)⁻¹ := by
    have hh := hact (actorEquiv.symm t) v
    have hval : ((actorEquiv.symm t : P) : FreeAmalgam d.radical) = (t : FreeAmalgam d.radical) :=
      congrArg Subtype.val (actorEquiv.apply_symm_apply t)
    exact hval ▸ hh
  have hbound := centralizer_embedded_cover_sylow_card_le (U d.radical a) T j hj hjU π S hπ
    (MovedSection.coverAction s e) hT (MovedSection.coverProjection s e) he
  have hcard : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  rw [hcard] at hbound
  exact hbound

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
