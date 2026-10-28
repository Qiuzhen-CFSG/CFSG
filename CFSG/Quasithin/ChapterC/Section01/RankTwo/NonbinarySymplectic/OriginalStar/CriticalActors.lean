module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.AmbientLayer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CriticalActors
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CriticalActors

/-!
# Critical actions on the original symplectic graph

The two full natural covers give a field-sized lower bound on each critical
image. The bound exceeds the field automorphism group, so the critical image
lies inside the opposite component modulo its entire two-core. The original
radical and original graph are retained throughout; no minimum replacement or
saturation is used.

The internal import reuses the generic critical-cover calculation within the
same source family, without changing its public boundary.
Source: MS93 (3.3)--(3.4), printed pp.867--868.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

/-- Both indices in a critical pair are at least q, without an innerness
assumption on either ambient quotient image. -/
theorem Input.original_critical_indices_ge_field
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R) :
    Nat.card F ≤ (Q R z).relIndex (Z R a) ∧
      Nat.card F ≤ (Q R a).relIndex (Z R z) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := (QuotientGroup.ker_mk' _).trans (h.centralOmega_centralizer).symm
  let C := K.map q
  let : C.Normal := (h.component_image_structure).2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _) hk) (K.map q)
  obtain ⟨Fe,hFe,ee,hee,je,hje,hjre,κe,hκe,hκeQ,hκeC,hκeL,hψe,hsemie,hconje,hproje,hkere⟩ :=
    h.ambient_initial_cover_at_vertex path.end_color
  obtain ⟨Fa,hFa,ea,hea,ja,hja,hjra,κa,hκa,hκaQ,hκaC,hκaL,hψa,hsemia,hconja,hproja,hkera⟩ :=
    h.ambient_initial_cover_at_vertex path.start_color
  have hFec : Nat.card Fe.Carrier = Nat.card F := by rw [Fe.card_eq,hFe,h.field_card]
  have hFac : Nat.card Fa.Carrier = Nat.card F := by rw [Fa.card_eq,hFa,h.field_card]
  have hAZ : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hZA : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  let δe : Z R a →* (H ⧸ pCore 2 H) := κe.comp (inclusion hAZ)
  let δa : Z R z →* (H ⧸ pCore 2 H) := κa.comp (inclusion hZA)
  have hδecard : Nat.card δe.range = (Q R z).relIndex (Z R a) :=
    quotient_image_card _ _ _ hAZ κe hκeQ
  have hδacard : Nat.card δa.range = (Q R a).relIndex (Z R z) :=
    quotient_image_card _ _ _ hZA κa hκaQ
  have hδek := restricted_kernel_of_mapped_centralizer (Z R a) (stabilizer R z)
    (Z R z) hAZ κe hκeC
  have hδak := restricted_kernel_of_mapped_centralizer (Z R z) (stabilizer R a)
    (Z R a) hZA κa hκaC
  have hδe : ∀ x : Z R a, ∀ v : s.space.toSubmodule,
      je (Multiplicative.ofAdd (s.space.toRepresentation (δe x) v)) =
        (x : FreeAmalgam R) * je (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹ :=
    fun x v => hconje (inclusion hAZ x) v
  have hδa : ∀ x : Z R z, ∀ v : s.space.toSubmodule,
      ja (Multiplicative.ofAdd (s.space.toRepresentation (δa x) v)) =
        (x : FreeAmalgam R) * ja (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹ :=
    fun x v => hconja (inclusion hZA x) v
  obtain ⟨πe,hπes,hπe,hπea⟩ := exists_equivariant_embedded_projection
    (U R z) (Z R a) (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_actor_normalizes_moving path)
    s.space.toRepresentation (MovedSection.ambientAction s ee) je hje hjre
    (MovedSection.coverProjection s ee).toLinearMap hee.1
    (MovedSection.coverProjection_ambient s ee) δe hδe
  obtain ⟨πa,hπas,hπa,hπaa⟩ := exists_equivariant_embedded_projection
    (U R a) (Z R z) (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path)
    s.space.toRepresentation (MovedSection.ambientAction s ea) ja hja hjra
    (MovedSection.coverProjection s ea).toLinearMap hea.1
    (MovedSection.coverProjection_ambient s ea) δa hδa
  have hedge := MSCentralOrbit.edgeCentralizerCondition R
    (h.radical.isPGroup) (h.radical.twoCore_le) (h.omegaOrbit_centralizer)
  obtain ⟨he4,ha4⟩ := critical_ambient_actor_orders_ge_fields
    path hb hedge πe hπes πa hπas
    (MovedSection.ambientAction s ee) hψe hsemie
    (MovedSection.ambientAction s ea) hψa hsemia
    δe δa hδek hδak hπea hπaa
  exact ⟨by simpa only [hFac,hδecard] using he4,
    by simpa only [hFec,hδacard] using ha4⟩

/-- Each critical endpoint seed has inner image at the opposite endpoint.
This does not assert that the whole vertex quotient is inner. -/
theorem Input.original_critical_image_inner
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R) :
    Z R a ≤ Ltilde R z ⊔ Q R z := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let : C.Normal := (h.component_image_structure).2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.centralOmega_centralizer).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.end_color
  have hFl : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  apply critical_actor_le_residual_core_of_cover path hb hFl s e he
    (h.component_image_structure).2.2.2.2 j hj hjr κ hκQ hκL hconj
  rw [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
    (show Nat.card E.Carrier = 2 ^ n by rw [E.card_eq,hE])]
  have hdeg : n < Nat.card F := by rw [h.field_card]; exact n.lt_two_pow_self
  exact hdeg.trans_le (h.original_critical_indices_ge_field path hb).1


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
