module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CriticalActors

/-!
# Reciprocal root images at every nonbinary field degree

The natural fixed quotient of an actor with displacement dimension d has
order q^d, while the actor has order at most q^(d²). Opposite critical
layers give reciprocal inequalities. If either critical index is below
q², both displacement dimensions are one and both indices are q.
The application constructs both inner actions from the literal replacement
quotients; it assumes neither field four nor an inner ambient quotient.

Source: MS93 (3.3), p.867, used in the star comparison (3.4).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.OneCohomology Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover

private theorem reciprocal_small_actor_card_field
    {F K : Type*} [Field F] [Finite F] [Field K] [Finite K]
    (hcard : Nat.card F = Nat.card K)
    (A : Subgroup (Sp F)) (B : Subgroup (Sp K))
    (hB : 1 < Nat.card B)
    (hAB : Nat.card (Vector F ⧸ TwoLocalCover.fixedSpace A) ≤ Nat.card B)
    (hBA : Nat.card (Vector K ⧸ TwoLocalCover.fixedSpace B) ≤ Nat.card A)
    (hsmall : Nat.card A < Nat.card F ^ 2) :
    Nat.card A = Nat.card F ∧ Nat.card B = Nat.card F ∧
      Module.finrank F (displacementSpace A) = 1 ∧
      Module.finrank K (displacementSpace B) = 1 := by
  have hAc := card_actor_le_displacement_dimension A
  have hBc := card_actor_le_displacement_dimension B
  rw [fixed_quotient_card] at hAB hBA
  rw [←hcard] at hBA hBc
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hdB : Module.finrank K (displacementSpace B) ≤ 1 := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by omega : 0 < Nat.card F)
      (show 2 ≤ Module.finrank K (displacementSpace B) by omega)
    omega
  have hdB' : Module.finrank K (displacementSpace B) = 1 := by
    by_contra hn
    have hz : Module.finrank K (displacementSpace B) = 0 := by omega
    simp only [hz, zero_pow (by decide : 2 ≠ 0), pow_zero] at hBc
    omega
  simp only [hdB', one_pow, pow_one] at hBc hBA
  have hdA : Module.finrank F (displacementSpace A) ≤ 1 := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by omega : 0 < Nat.card F)
      (show 2 ≤ Module.finrank F (displacementSpace A) by omega)
    have hs : Nat.card F < Nat.card F ^ 2 := by nlinarith
    omega
  have hdA' : Module.finrank F (displacementSpace A) = 1 := by
    by_contra hn
    have hz : Module.finrank F (displacementSpace A) = 0 := by omega
    simp only [hz, zero_pow (by decide : 2 ≠ 0), pow_zero] at hAc
    omega
  simp only [hdA', one_pow, pow_one] at hAc hAB
  exact ⟨by omega, by omega, hdA', hdB'⟩

section Graph
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}
  {geometry : Geometry R} {a e : Vertex R}
  {F : Type*} [Field F] [Finite F]

theorem critical_small_inner_actor_card_field_of_fields
    {K : Type*} [Field K] [Finite K]
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    (hC : EdgeCentralizerCondition R) (hcard : Nat.card F = Nat.card K)
    (πe : U R e →* Multiplicative (Vector F)) (hpe : Function.Surjective πe)
    (πa : U R a →* Multiplicative (Vector K)) (hpa : Function.Surjective πa)
    (α : Z R a →* Sp F) (β : Z R e →* Sp K)
    (hαker : α.ker = (centralizer (Z R e : Set (FreeAmalgam R))).subgroupOf (Z R a))
    (hβker : β.ker = (centralizer (Z R a : Set (FreeAmalgam R))).subgroupOf (Z R e))
    (hα : ∀ (z : Z R a) (u : U R e),
      πe ⟨z.val*u.val*z.val⁻¹,
        (mem_normalizer_iff.mp (critical_actor_normalizes_moving path z.property) u.val).mp u.property⟩ =
          Multiplicative.ofAdd (α z • (πe u).toAdd))
    (hβ : ∀ (z : Z R e) (u : U R a),
      πa ⟨z.val*u.val*z.val⁻¹,
        (mem_normalizer_iff.mp (critical_reverse_actor_normalizes_moving path z.property) u.val).mp u.property⟩ =
          Multiplicative.ofAdd (β z • (πa u).toAdd))
    (hsmall : Nat.card α.range < Nat.card F ^ 2) :
    Nat.card α.range=Nat.card F ∧ Nat.card β.range=Nat.card F ∧
      Module.finrank F (displacementSpace α.range)=1 ∧
      Module.finrank K (displacementSpace β.range)=1 := by
  let := finite_Z R a
  let := finite_Z R e
  let : Finite (U R e) := Finite.of_injective (inclusion (U_le_Z e)) (inclusion_injective _)
  let : Finite (U R a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  have hia : (centralizer (Z R e : Set (FreeAmalgam R))).relIndex (Z R a) =
      Nat.card α.range := by
    change ((centralizer (Z R e : Set (FreeAmalgam R))).subgroupOf (Z R a)).index = _
    rw [←hαker,index_ker]
  have hie : (centralizer (Z R a : Set (FreeAmalgam R))).relIndex (Z R e) =
      Nat.card β.range := by
    change ((centralizer (Z R a : Set (FreeAmalgam R))).subgroupOf (Z R e)).index = _
    rw [←hβker,index_ker]
  have hB : 1 < Nat.card β.range := by
    have hp : 0 < Nat.card β.range := Nat.card_pos
    have hn : Nat.card β.range ≠ 1 := by
      intro he
      have hz := relIndex_eq_one.mp (hie.trans he)
      have hc := commutator_eq_bot_iff_le_centralizer.mpr hz
      rw [commutator_comm] at hc
      exact critical_noncommutation R geometry hC a path.start_color
        (by rwa [geometry.distance_constant a path.start_color]) path.critical hc
    omega
  have hAB : Nat.card (Vector F ⧸ TwoLocalCover.fixedSpace α.range) ≤ Nat.card β.range := by
    have h := fixed_quotient_card_le_centralizer_index (U R e) (Z R a)
      (critical_actor_normalizes_moving path) πe hpe α hα
    apply h.trans
    rw [←hie]
    exact relIndex_le_of_le_right (U_le_Z e) index_ne_zero_of_finite
  have hBA : Nat.card (Vector K ⧸ TwoLocalCover.fixedSpace β.range) ≤ Nat.card α.range := by
    have h := fixed_quotient_card_le_centralizer_index (U R a) (Z R e)
      (critical_reverse_actor_normalizes_moving path) πa hpa β hβ
    apply h.trans
    rw [←hia]
    exact relIndex_le_of_le_right (U_le_Z a) index_ne_zero_of_finite
  exact reciprocal_small_actor_card_field hcard α.range β.range hB hAB hBA hsmall

end Graph

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Reciprocal critical indices below q² are both q on the actual replacement. -/
theorem Input.replacement_small_critical_indices_eq_field
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F ^ 2) :
    (Q d.radical z).relIndex (Z d.radical a) = Nat.card F ∧
      (Q d.radical a).relIndex (Z d.radical z) = Nat.card F := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let hk := (QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _) hk) ((K.subgroupOf d.overgroup).map q)
  obtain ⟨Fe,hFe,ee,hee,je,hje,hjre,κe,hκe,hκeQ,hκeC,hκeL,hψe,hsemie,hconje,hproje,hkere⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d path.end_color
  obtain ⟨Fa,hFa,ea,hea,ja,hja,hjra,κa,hκa,hκaQ,hκaC,hκaL,hψa,hsemia,hconja,hproja,hkera⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d path.start_color
  have hFec : Nat.card Fe.Carrier = Nat.card F := by rw [Fe.card_eq,hFe,h.field_card]
  have hFac : Nat.card Fa.Carrier = Nat.card F := by rw [Fa.card_eq,hFa,h.field_card]
  have hAZ : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hZA : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  let δe : Z d.radical a →* (d.overgroup ⧸ pCore 2 d.overgroup) := κe.comp (inclusion hAZ)
  let δa : Z d.radical z →* (d.overgroup ⧸ pCore 2 d.overgroup) := κa.comp (inclusion hZA)
  have hδecard : Nat.card δe.range = (Q d.radical z).relIndex (Z d.radical a) :=
    quotient_image_card _ _ _ hAZ κe hκeQ
  have hδacard : Nat.card δa.range = (Q d.radical a).relIndex (Z d.radical z) :=
    quotient_image_card _ _ _ hZA κa hκaQ
  have hδek := restricted_kernel_of_mapped_centralizer (Z d.radical a) (stabilizer d.radical z)
    (Z d.radical z) hAZ κe hκeC
  have hδak := restricted_kernel_of_mapped_centralizer (Z d.radical z) (stabilizer d.radical a)
    (Z d.radical a) hZA κa hκaC
  have hδe : ∀ x : Z d.radical a, ∀ v : s.space.toSubmodule,
      je (Multiplicative.ofAdd (s.space.toRepresentation (δe x) v)) =
        (x : FreeAmalgam d.radical) * je (Multiplicative.ofAdd v) * (x : FreeAmalgam d.radical)⁻¹ :=
    fun x v => hconje (inclusion hAZ x) v
  have hδa : ∀ x : Z d.radical z, ∀ v : s.space.toSubmodule,
      ja (Multiplicative.ofAdd (s.space.toRepresentation (δa x) v)) =
        (x : FreeAmalgam d.radical) * ja (Multiplicative.ofAdd v) * (x : FreeAmalgam d.radical)⁻¹ :=
    fun x v => hconja (inclusion hZA x) v
  obtain ⟨πe,hπes,hπe,hπea⟩ := exists_equivariant_embedded_projection
    (U d.radical z) (Z d.radical a) (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_actor_normalizes_moving path)
    s.space.toRepresentation (MovedSection.ambientAction s ee) je hje hjre
    (MovedSection.coverProjection s ee).toLinearMap hee.1
    (MovedSection.coverProjection_ambient s ee) δe hδe
  obtain ⟨πa,hπas,hπa,hπaa⟩ := exists_equivariant_embedded_projection
    (U d.radical a) (Z d.radical z) (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path)
    s.space.toRepresentation (MovedSection.ambientAction s ea) ja hja hjra
    (MovedSection.coverProjection s ea).toLinearMap hea.1
    (MovedSection.coverProjection_ambient s ea) δa hδa
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  have hcent := (h.replacement_component_image_structure d).2.2.2.2
  have hFlarge : 2 < Nat.card F := by
    rw [h.field_card]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hdeg : n < Nat.card F := by rw [h.field_card]; exact n.lt_two_pow_self
  have hindices := h.replacement_critical_indices_ge_field d path hb
  have hAutE : Nat.card (Fe.Carrier ≃+* Fe.Carrier) = n :=
    FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
      (show Nat.card Fe.Carrier = 2 ^ n by rw [Fe.card_eq,hFe])
  have hAutA : Nat.card (Fa.Carrier ≃+* Fa.Carrier) = n :=
    FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
      (show Nat.card Fa.Carrier = 2 ^ n by rw [Fa.card_eq,hFa])
  let rev : CriticalPath d.radical geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry hedge a path.start_color
        (by rwa [geometry.distance_constant a path.start_color]) z path.end_color path.critical }
  obtain ⟨βe,hβec,hβem,hβe⟩ := critical_inner_model_actor_of_ringAut_card_lt path hb
    (by omega : 2 < Nat.card Fe.Carrier) s ee hee hcent je hje hjre δe hδe (by omega)
  obtain ⟨βa,hβac,hβam,hβa⟩ := critical_inner_model_actor_of_ringAut_card_lt rev hb
    (by omega : 2 < Nat.card Fa.Carrier) s ea hea hcent ja hja hjra δa hδa (by omega)
  let αe : Z d.radical a →* Theory.SpecificGroups.SymplecticFour.Sp Fe.Carrier :=
    (commutator (Theory.SpecificGroups.SymplecticFour.Sp Fe.Carrier)).subtype.comp βe
  let αa : Z d.radical z →* Theory.SpecificGroups.SymplecticFour.Sp Fa.Carrier :=
    (commutator (Theory.SpecificGroups.SymplecticFour.Sp Fa.Carrier)).subtype.comp βa
  have hαek : αe.ker=δe.ker := inner_model_kernel_eq s ee δe βe hβem
  have hαak : αa.ker=δa.ker := inner_model_kernel_eq s ea δa βa hβam
  have hαec : Nat.card αe.range=Nat.card δe.range := by rw [←index_ker,←index_ker,hαek]
  have hαac : Nat.card αa.range=Nat.card δa.range := by rw [←index_ker,←index_ker,hαak]
  have hacte : ∀ (x : Z d.radical a) (u : U d.radical z),
      πe ⟨x.val*u.val*x.val⁻¹,
        (mem_normalizer_iff.mp (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_actor_normalizes_moving path x.property)
          u.val).mp u.property⟩ = Multiplicative.ofAdd (αe x • (πe u).toAdd) := by
    intro x u
    rw [hπea,ambient_marking_inner_apply s ee δe βe hβem]
    rfl
  have hacta : ∀ (x : Z d.radical z) (u : U d.radical a),
      πa ⟨x.val*u.val*x.val⁻¹,
        (mem_normalizer_iff.mp (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path x.property)
          u.val).mp u.property⟩ = Multiplicative.ofAdd (αa x • (πa u).toAdd) := by
    intro x u
    rw [hπaa,ambient_marking_inner_apply s ea δa βa hβam]
    rfl
  have hh := critical_small_inner_actor_card_field_of_fields
    path hb hedge (hFec.trans hFac.symm) πe hπes πa hπas αe αa
    (hαek.trans hδek) (hαak.trans hδak) hacte hacta (by rwa [hαec,hδecard,hFec])
  exact ⟨by rw [←hδecard,←hαec]; exact hh.1.trans hFec,
    by rw [←hδacard,←hαac]; exact hh.2.1.trans hFec⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
