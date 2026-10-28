module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.VertexAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.ReciprocalCoordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.SmallActor
public import Theory.Representation.ConjugationFixedQuotient
public import Theory.Representation.SemilinearFixedIndex.General
public import Theory.Representation.SymplecticNaturalNormalizer.QuadraticOuter.General

/-!
# Critical images for every nonbinary symplectic degree

The two literal natural covers at opposite critical endpoints force both
critical indices to be at least the coefficient field size. Quadraticity
and the degree bound on outer semilinear groups then put such images inside
the symplectic component. Quotient kernels and conjugation are retained.

Source: MS93 (3.3)--(3.4), pp.867--868, on the replacement of Section 7.
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
section Abstract
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}
  {geometry : Geometry R} {a z e : Vertex R}
private theorem image_ne_bot_of_kernel_centralizer
    {G D : Type*} [Group G] [Group D] (A B : Subgroup G)
    (α : A →* D) (hk : α.ker = (centralizer (B : Set G)).subgroupOf A)
    (hn : ⁅A,B⁆ ≠ ⊥) : α.range ≠ ⊥ := by
  intro he
  apply hn
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro a ha
  have hx : α ⟨a,ha⟩ ∈ α.range := ⟨⟨a,ha⟩,rfl⟩
  rw [he] at hx
  have hm : (⟨a,ha⟩ : A) ∈ α.ker := hx
  rw [hk] at hm
  exact hm

theorem critical_ambient_actor_orders_ge_fields
    {F K D E : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    [Field K] [Finite K] [Algebra (ZMod 2) K] [Group D] [Group E]
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    (hC : EdgeCentralizerCondition R)
    (πe : U R e →* Multiplicative (Vector F)) (hpe : Function.Surjective πe)
    (πa : U R a →* Multiplicative (Vector K)) (hpa : Function.Surjective πa)
    (ρe : Representation (ZMod 2) D (Vector F)) (hfaithE : Function.Injective ρe)
    (hsemiE : ∀ d : D, ∃ σ : F ≃+* F, ∀ c v, ρe d (c • v)=σ c • ρe d v)
    (ρa : Representation (ZMod 2) E (Vector K)) (hfaithA : Function.Injective ρa)
    (hsemiA : ∀ d : E, ∃ σ : K ≃+* K, ∀ c v, ρa d (c • v)=σ c • ρa d v)
    (α : Z R a →* D) (β : Z R e →* E)
    (hαker : α.ker = (centralizer (Z R e : Set (FreeAmalgam R))).subgroupOf (Z R a))
    (hβker : β.ker = (centralizer (Z R a : Set (FreeAmalgam R))).subgroupOf (Z R e))
    (hα : ∀ (z : Z R a) (u : U R e),
      πe ⟨z.val*u.val*z.val⁻¹,
        (mem_normalizer_iff.mp (critical_actor_normalizes_moving path z.property) u.val).mp u.property⟩ =
          Multiplicative.ofAdd (ρe (α z) (πe u).toAdd))
    (hβ : ∀ (z : Z R e) (u : U R a),
      πa ⟨z.val*u.val*z.val⁻¹,
        (mem_normalizer_iff.mp (critical_reverse_actor_normalizes_moving path z.property) u.val).mp u.property⟩ =
          Multiplicative.ofAdd (ρa (β z) (πa u).toAdd)) :
    Nat.card K ≤ Nat.card α.range ∧ Nat.card F ≤ Nat.card β.range := by
  let := finite_Z R a
  let := finite_Z R e
  let : Finite (U R e) := Finite.of_injective (inclusion (U_le_Z e)) (inclusion_injective _)
  let : Finite (U R a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  have hn := critical_noncommutation R geometry hC a path.start_color
    (by rwa [geometry.distance_constant a path.start_color]) path.critical
  have hA := image_ne_bot_of_kernel_centralizer (Z R a) (Z R e) α hαker hn
  have hB := image_ne_bot_of_kernel_centralizer (Z R e) (Z R a) β hβker
    (by rwa [commutator_comm])
  have hia : (centralizer (Z R e : Set (FreeAmalgam R))).relIndex (Z R a) =
      Nat.card α.range := by
    change ((centralizer (Z R e : Set (FreeAmalgam R))).subgroupOf (Z R a)).index = _
    rw [←hαker,index_ker]
  have hie : (centralizer (Z R a : Set (FreeAmalgam R))).relIndex (Z R e) =
      Nat.card β.range := by
    change ((centralizer (Z R a : Set (FreeAmalgam R))).subgroupOf (Z R e)).index = _
    rw [←hβker,index_ker]
  constructor
  · apply (field_card_le_fixed_quotient_card_of_semilinear (F := K) ρa
      (by simp [Theory.SpecificGroups.SymplecticFour.Vector]) hfaithA hsemiA β.range hB).trans
    apply (Representation.fixed_quotient_card_le_centralizer_index (U R a) (Z R e)
      (critical_reverse_actor_normalizes_moving path) πa hpa ρa β hβ).trans
    rw [←hia]
    exact relIndex_le_of_le_right (U_le_Z a) index_ne_zero_of_finite
  · apply (field_card_le_fixed_quotient_card_of_semilinear (F := F) ρe
      (by simp [Theory.SpecificGroups.SymplecticFour.Vector]) hfaithE hsemiE α.range hA).trans
    apply (Representation.fixed_quotient_card_le_centralizer_index (U R e) (Z R a)
      (critical_actor_normalizes_moving path) πe hpe ρe α hα).trans
    rw [←hie]
    exact relIndex_le_of_le_right (U_le_Z e) index_ne_zero_of_finite
end Abstract
section Model
variable {M J V : Type*} [Group M] [Group J] [AddCommGroup V] [Module (ZMod 2) V]
  {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
  {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
  {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
theorem critical_inner_model_actor_of_ringAut_card_lt (path : CriticalPath R geometry a z)
    (hb : 0 < geometry.b R) (hF : 2 < Nat.card F)
    (s : MovedSection ρ B) (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R z) (δ : Z R a →* J)
    (hδ : ∀ x : Z R a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹)
    (hlarge : Nat.card (F ≃+* F) < Nat.card δ.range) :
    ∃ β : Z R a →* L (K := F),
      Nat.card β.range = Nat.card δ.range ∧
      (∀ x, (e.groupEquiv.symm (β x) : J) = δ x) ∧
      (∀ x : Z R a, ∀ v : s.space.toSubmodule,
        j (Multiplicative.ofAdd (MovedSection.coverAction s e (β x) v)) =
          (x : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹) := by
  have hcard : 2 < Nat.card F := by omega
  let d : L (K := F) ≃* Sp F :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hcard)).trans
      Subgroup.topEquiv
  have hfaith := MovedSection.ambientAction_faithful s e binaryNatural_injective hcent
  have hinner : δ.range ≤ B :=
    SymplecticNaturalNormalizer.le_component_of_quadratic_ringAut_card_lt hF B
      (hcent ▸ bot_le) (e.groupEquiv.trans d) (MovedSection.ambientAction s e) hfaith
      (fun b v => MovedSection.ambientAction_component s e b v)
      δ.range (critical_ambient_quadratic path hb s e hp j hj hjr δ hδ) hlarge
  let β := e.groupEquiv.toMonoidHom.comp (δ.codRestrict B (fun x => hinner ⟨x,rfl⟩))
  have he (x) : (e.groupEquiv.symm (β x) : J) = δ x := by
    change (e.groupEquiv.symm (e.groupEquiv ⟨δ x,_⟩) : J) = δ x
    rw [e.groupEquiv.symm_apply_apply]
  have hk : β.ker = δ.ker := by
    ext x
    change e.groupEquiv ⟨δ x,_⟩ = 1 ↔ δ x = 1
    rw [e.groupEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
  refine ⟨β,?_,he,?_⟩
  · rw [←Nat.card_congr (QuotientGroup.quotientKerEquivRange β).toEquiv,
      ←Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv, hk]
  · intro x v
    change j (Multiplicative.ofAdd (s.space.toRepresentation (e.groupEquiv.symm (β x)) v)) = _
    rw [he]
    exact hδ x v

/-- Pull the inner model image back through the literal vertex quotient. -/
private theorem critical_actor_le_residual_core_of_cover
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hF : 2 < Nat.card F) (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R)
    (hj : Function.Injective j) (hjr : j.range = U R z)
    (κ : stabilizer R z →* J)
    (hκQ : κ.ker.map (stabilizer R z).subtype = Q R z)
    (hκL : ((Ltilde R z).subgroupOf (stabilizer R z)).map κ = B)
    (hconj : ∀ (g : stabilizer R z) (v : s.space.toSubmodule),
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ g) v)) =
        (g : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (g : FreeAmalgam R)⁻¹)
    (hlarge : Nat.card (F ≃+* F) < (Q R z).relIndex (Z R a)) :
    Z R a ≤ Ltilde R z ⊔ Q R z := by
  have hAZ : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ := κ.comp (inclusion hAZ)
  have hδc : Nat.card δ.range = (Q R z).relIndex (Z R a) :=
    quotient_image_card _ _ _ hAZ κ hκQ
  obtain ⟨β,_,hβmark,_⟩ := critical_inner_model_actor_of_ringAut_card_lt path hb hF s e hp
    hcent j hj hjr δ (fun x v => hconj (inclusion hAZ x) v) (by rwa [hδc])
  have himage : ((Z R a).subgroupOf (stabilizer R z)).map κ ≤
      ((Ltilde R z).subgroupOf (stabilizer R z)).map κ := by
    rw [hκL]
    rintro _ ⟨x,hx,rfl⟩
    have hmem := (e.groupEquiv.symm (β ⟨x.val,hx⟩)).property
    rwa [hβmark] at hmem
  have hle := map_mono (f := (stabilizer R z).subtype) (map_le_map_iff.mp himage)
  rwa [Subgroup.map_sup,hκQ,map_subgroupOf_eq_of_le hAZ,
    map_subgroupOf_eq_of_le (Ltilde_le_stabilizer z)] at hle

end Model
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

include h

/-- Both indices in a critical pair are at least q, without an innerness
assumption on either ambient quotient image. -/
theorem Input.replacement_critical_indices_ge_field
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical) :
    Nat.card F ≤ (Q d.radical z).relIndex (Z d.radical a) ∧
      Nat.card F ≤ (Q d.radical a).relIndex (Z d.radical z) := by
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
  obtain ⟨he4,ha4⟩ := critical_ambient_actor_orders_ge_fields
    path hb hedge πe hπes πa hπas
    (MovedSection.ambientAction s ee) hψe hsemie
    (MovedSection.ambientAction s ea) hψa hsemia
    δe δa hδek hδak hπea hπaa
  exact ⟨by simpa only [hFac,hδecard] using he4,
    by simpa only [hFec,hδacard] using ha4⟩

/-- Each critical endpoint seed has inner image at the opposite endpoint.
This does not assert that the whole vertex quotient is inner. -/
theorem Input.replacement_critical_image_inner
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical) :
    Z d.radical a ≤ Ltilde d.radical z ⊔ Q d.radical z := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d path.end_color
  have hFl : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  apply critical_actor_le_residual_core_of_cover path hb hFl s e he
    (h.replacement_component_image_structure d).2.2.2.2 j hj hjr κ hκQ hκL hconj
  rw [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
    (show Nat.card E.Carrier = 2 ^ n by rw [E.card_eq,hE])]
  have hdeg : n < Nat.card F := by rw [h.field_card]; exact n.lt_two_pow_self
  exact hdeg.trans_le (h.replacement_critical_indices_ge_field d path hb).1

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
