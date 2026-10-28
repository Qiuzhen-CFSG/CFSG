module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.AmbientLayer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SeedCentralizer
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SeedCentralizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.SeedTransport
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowSeedCard

/-!
# The original fixed Sylow seed at arbitrary nonbinary degree

The original natural cover, including its full fixed kernel, bounds the
actual fixed Sylow seed by q squared. The full ambient cover action then
puts its centralizer over the original symplectic component, even in the
presence of outer automorphisms. Both statements concern the original
radical and its original holomorph graph.

The internal import reuses the generic ambient-cover proof from the same
source family without exposing that proof or changing shared foundations.
Source: MS93 (3.2)(vi), (3.4), printed pp.864,868--869.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

/-- The original vertex centralizer of the actual fixed Sylow seed has inner
component action, with the full natural-cover kernel retained. -/
theorem componentSylowSeed_centralizer_le
    {a : Vertex R} (ha : color R a = false) (P : Sylow 2 (Ltilde R a)) :
    stabilizer R a ⊓ centralizer
      (componentSylowSeed R a P : Set (FreeAmalgam R)) ≤ Ltilde R a ⊔ Q R a := by
  exact seed_centralizer_from_ambient_cover K R
    h.component_image_structure.2.1 h.centralOmega_centralizer
    h.component_image_structure.2.2.2.2 h.nonbinary
    (h.ambient_initial_cover_at_vertex ha) P

/-- The full component Sylow fixes at most q² elements of the literal U layer,
including the kernel of its natural projection. -/
theorem componentSylowSeed_card_le
    {a : Vertex R} (ha : color R a = false)
    (P : Sylow 2 (Ltilde R a)) :
    Nat.card (U R a ⊓ centralizer
      (((P : Subgroup (Ltilde R a)).map (Ltilde R a).subtype) :
        Set (FreeAmalgam R)) : Subgroup (FreeAmalgam R)) ≤ Nat.card F ^ 2 := by
  obtain ⟨E,hE,e,he,j,hj,hjU,f,hf,hact,_⟩ := h.initial_cover_at_vertex ha
  let C := K.map (QuotientGroup.mk' (pCore 2 H))
  let : C.Normal := h.component_image_structure.2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) (QuotientGroup.mk' (pCore 2 H))
    (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C
  let T := (P : Subgroup (Ltilde R a)).map (Ltilde R a).subtype
  let actorEquiv : (P : Subgroup (Ltilde R a)) ≃* T :=
    (P : Subgroup (Ltilde R a)).equivMapOfInjective
      (Ltilde R a).subtype (Ltilde R a).subtype_injective
  let π : T →* L (K := E.Carrier) :=
    (f.comp (P : Subgroup (Ltilde R a)).subtype).comp actorEquiv.symm.toMonoidHom
  let := finite_stabilizer R a
  let : Finite (Ltilde R a) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer a)) (inclusion_injective _)
  let S := P.mapSurjective (f := f) hf
  have hπ : π.range = (S : Subgroup (L (K := E.Carrier))) := by
    change π.range = (P.mapSurjective (f := f) hf : Subgroup _)
    rw [Sylow.coe_mapSurjective,MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective actorEquiv.symm.toMonoidHom actorEquiv.symm.surjective,
      ← MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype]
  have hT (t : T) (v : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (π t) v)) =
        (t : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (t : FreeAmalgam R)⁻¹ := by
    have hh := hact (actorEquiv.symm t) v
    have hval : ((actorEquiv.symm t : P) : FreeAmalgam R) = (t : FreeAmalgam R) :=
      congrArg Subtype.val (actorEquiv.apply_symm_apply t)
    exact hval ▸ hh
  have hbound := centralizer_embedded_cover_sylow_card_le (U R a) T j hj hjU π S hπ
    (MovedSection.coverAction s e) hT (MovedSection.coverProjection s e) he
  have hcard : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  rw [hcard] at hbound
  exact hbound


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
