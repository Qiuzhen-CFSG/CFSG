module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.Graph
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.ReciprocalCoordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.AmbientSmallActor
public import Theory.Representation.SemilinearFixedIndex.General
public import Theory.Representation.SymplecticNaturalNormalizer.QuadraticOuter.General

/-!
# Critical natural actors over the original nonbinary field

Reciprocal semilinear actions give critical image orders at least q = 2^n.
An outer quadratic image has order at most the field automorphism group,
which has order n < q. Thus both critical images are inner. Their actual
natural projections retain the full component-fixed kernel and the literal
quotient index. If one index is below q squared, reciprocal fixed-space
bounds identify both images as roots of order q with one-dimensional
natural displacement.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3) and the opening symplectic branch of (3.6), pp.867, 870--871.
These comparisons hold before the field restriction in (3.7).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource
section Reciprocal
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}
  {geometry : Geometry R} {a e : Vertex R}
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

private theorem critical_ambient_actor_orders_ge_field
    {F K D E : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    [Field K] [Finite K] [Algebra (ZMod 2) K] [Group D] [Group E]
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    (hC : EdgeCentralizerCondition R) (hFK : Nat.card F = Nat.card K)
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
    Nat.card F ≤ Nat.card α.range ∧ Nat.card F ≤ Nat.card β.range := by
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
  · apply (hFK.trans_le (field_card_le_fixed_quotient_card_of_semilinear ρa (by simp [Theory.SpecificGroups.SymplecticFour.Vector]) hfaithA hsemiA β.range hB)).trans
    apply (Representation.fixed_quotient_card_le_centralizer_index (U R a) (Z R e)
      (critical_reverse_actor_normalizes_moving path) πa hpa ρa β hβ).trans
    rw [←hia]
    exact relIndex_le_of_le_right (U_le_Z a) index_ne_zero_of_finite
  · apply (field_card_le_fixed_quotient_card_of_semilinear ρe (by simp [Theory.SpecificGroups.SymplecticFour.Vector]) hfaithE hsemiE α.range hA).trans
    apply (Representation.fixed_quotient_card_le_centralizer_index (U R e) (Z R a)
      (critical_actor_normalizes_moving path) πe hpe ρe α hα).trans
    rw [←hie]
    exact relIndex_le_of_le_right (U_le_Z e) index_ne_zero_of_finite

end Reciprocal

section Inner
variable {M J V : Type*} [Group M] [Group J] [AddCommGroup V] [Module (ZMod 2) V]
  {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
  {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
  {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
/-- A critical quadratic actor whose order exceeds the field automorphism
order is inner, with its original quotient marking and cover action. -/
theorem critical_inner_model_actor_of_field_bound (path : CriticalPath R geometry a z)
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


end Inner

private theorem embedded_projection_kernel
    {G W V : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup V] [Module (ZMod 2) V]
    (U C : Subgroup G) (j : Multiplicative W →* G) (hjr : j.range = U)
    (p : W →ₗ[ZMod 2] V) (π : U →* Multiplicative V)
    (hπ : ∀ w : W, π ⟨j (Multiplicative.ofAdd w),by rw [←hjr]; exact ⟨_,rfl⟩⟩ =
      Multiplicative.ofAdd (p w))
    (hk : ∀ w : W, p w = 0 ↔ j (Multiplicative.ofAdd w) ∈ C) :
    π.ker.map U.subtype = U ⊓ C := by
  have hπmul (w : Multiplicative W) (hw : j w ∈ U) :
      π ⟨j w,hw⟩ = Multiplicative.ofAdd (p w.toAdd) := hπ w.toAdd
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    refine ⟨u.property,?_⟩
    have hur : u.val ∈ j.range := hjr.symm ▸ u.property
    obtain ⟨w,hw⟩ := hur
    have he : u = ⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩ := Subtype.ext hw.symm
    change π u = 1 at hu
    rw [he,hπmul] at hu
    change (u : G) ∈ C
    rw [←hw]
    exact (hk w.toAdd).mp (congrArg Multiplicative.toAdd hu)
  · rintro ⟨hx,hc⟩
    have hxr : x ∈ j.range := hjr.symm ▸ hx
    obtain ⟨w,rfl⟩ := hxr
    refine ⟨⟨j w,hx⟩,?_,rfl⟩
    change π ⟨j w,hx⟩ = 1
    rw [hπmul]
    exact congrArg Multiplicative.ofAdd ((hk w.toAdd).mpr hc)

/-- The actual critical action on the opposite natural quotient. Its field
has the original degree, and its kernel is the literal critical centralizer. -/
structure CriticalNaturalAction {M : Type*} [Group M]
    (T : Subgroup M) (a z : Vertex T) (n : ℕ) where
  field : BinaryField
  degree : field.degree = n
  normalized : Z T a ≤ normalizer (U T z : Set (FreeAmalgam T))
  projection : U T z →* Multiplicative (Vector field.Carrier)
  onto : Function.Surjective projection
  actor : Z T a →* Sp field.Carrier
  kernel : actor.ker = (centralizer (Z T z : Set (FreeAmalgam T))).subgroupOf (Z T a)
  index : Nat.card actor.range = (Q T z).relIndex (Z T a)
  lower_bound : 2^n ≤ Nat.card actor.range
  projection_kernel : projection.ker.map (U T z).subtype =
    U T z ⊓ centralizer (Ltilde T z : Set (FreeAmalgam T))
  conjugation : ∀ (x : Z T a) (u : U T z),
    projection ⟨x.val*u.val*x.val⁻¹,
      (mem_normalizer_iff.mp (normalized x.property) u.val).mp u.property⟩ =
        Multiplicative.ofAdd (actor x • (projection u).toAdd)
  quadratic : ∀ x ∈ actor.range, ∀ y ∈ actor.range, ∀ v : Vector field.Carrier,
    x • (y • v-v) = y • v-v

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R) {g : Geometry d.radical}
  {a z : Vertex d.radical}

include h

/-- Both critical images are inner at the original nonbinary degree.
The reciprocal field-size lower bound exceeds the outer quadratic bound n. -/
theorem replacement_critical_natural_actions
    (path : CriticalPath d.radical g a z) (hb : 0 < g.b d.radical) :
    Nonempty (CriticalNaturalAction d.radical a z n ×
      CriticalNaturalAction d.radical z a n) := by
  let C := replacementComponent d
  let : C.Normal := replacementComponent_normal h d
  let s := replacementMovedSection h d
  have hC : centralizer (C : Set (d.overgroup ⧸ pCore 2 d.overgroup)) = ⊥ :=
    (replacement_component_image_structure h d).2.2.2.2
  obtain ⟨⟨Fe,hFe,ee,hee,je,hje,hjre,κe,hκe,hκeQ,hκeC,hκeL,hψe,hsemie,hconje,hproje,hkere⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.end_color
  obtain ⟨⟨Fa,hFa,ea,hea,ja,hja,hjra,κa,hκa,hκaQ,hκaC,hκaL,hψa,hsemia,hconja,hproja,hkera⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.start_color
  have hFec : Nat.card Fe.Carrier = 2^n := by rw [Fe.card_eq,hFe]
  have hFac : Nat.card Fa.Carrier = 2^n := by rw [Fa.card_eq,hFa]
  have hAZ : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  have hZA : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
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
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  obtain ⟨he4,ha4⟩ := critical_ambient_actor_orders_ge_field
    path hb hedge (hFec.trans hFac.symm) πe hπes πa hπas
    (MovedSection.ambientAction s ee) hψe hsemie
    (MovedSection.ambientAction s ea) hψa hsemia
    δe δa hδek hδak hπea hπaa
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rwa [g.distance_constant a path.start_color]) z path.end_color path.critical }
  obtain ⟨βe,hβec,hβem,hβe⟩ := critical_inner_model_actor_of_field_bound path hb (by rw [hFec]; exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)) s ee hee hC
    je hje hjre δe hδe (by rw [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hFec]; exact (show n < 2^n from Nat.lt_two_pow_self).trans_le (hFec ▸ he4))
  obtain ⟨βa,hβac,hβam,hβa⟩ := critical_inner_model_actor_of_field_bound rev hb (by rw [hFac]; exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)) s ea hea hC
    ja hja hjra δa hδa (by rw [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hFac]; exact (show n < 2^n from Nat.lt_two_pow_self).trans_le (hFec ▸ ha4))
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
  have hqe := critical_embedded_natural_actor_quadratic path hb
    (MovedSection.coverAction s ee) (MovedSection.coverProjection s ee) hee
    je hje hjre βe hβe
  have hqa := critical_embedded_natural_actor_quadratic rev hb
    (MovedSection.coverAction s ea) (MovedSection.coverProjection s ea) hea
    ja hja hjra βa hβa
  refine ⟨⟨⟨Fe,hFe,critical_actor_normalizes_moving path,πe,hπes,αe,
    hαek.trans hδek,hαec.trans hδecard,?_,?_,hacte,?_⟩,
    ⟨Fa,hFa,critical_reverse_actor_normalizes_moving path,πa,hπas,αa,
    hαak.trans hδak,hαac.trans hδacard,?_,?_,hacta,?_⟩⟩⟩
  · rw [hαec]
    exact hFec ▸ he4
  · exact embedded_projection_kernel _ _ je hjre
      (MovedSection.coverProjection s ee).toLinearMap πe hπe hkere
  · rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ v
    exact hqe (βe x) ⟨x,rfl⟩ (βe y) ⟨y,rfl⟩ v
  · rw [hαac]
    exact hFec ▸ ha4
  · exact embedded_projection_kernel _ _ ja hjra
      (MovedSection.coverProjection s ea).toLinearMap πa hπa hkera
  · rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ v
    exact hqa (βa x) ⟨x,rfl⟩ (βa y) ⟨y,rfl⟩ v

section Small
variable {E F : Type*} [Field E] [Finite E] [Field F] [Finite F]

omit h in
private theorem reciprocal_small_actors
    (hEF : Nat.card E = Nat.card F) (A : Subgroup (Sp E)) (B : Subgroup (Sp F))
    (hB : 1 < Nat.card B)
    (hAB : Nat.card (Vector E ⧸ TwoLocalCover.fixedSpace A) ≤ Nat.card B)
    (hBA : Nat.card (Vector F ⧸ TwoLocalCover.fixedSpace B) ≤ Nat.card A)
    (hsmall : Nat.card A < Nat.card E ^ 2) :
    Nat.card A = Nat.card E ∧ Nat.card B = Nat.card E ∧
      Module.finrank E (displacementSpace A) = 1 ∧
      Module.finrank F (displacementSpace B) = 1 := by
  have hq : 1 < Nat.card E := Finite.one_lt_card
  have hAc := card_actor_le_displacement_dimension A
  have hBc := card_actor_le_displacement_dimension B
  rw [fixed_quotient_card] at hAB hBA
  rw [←hEF] at hBA hBc
  have hdB : Module.finrank F (displacementSpace B) < 2 :=
    (Nat.pow_lt_pow_iff_right hq).mp (hBA.trans_lt hsmall)
  have hdB' : Module.finrank F (displacementSpace B) = 1 := by
    have hn : Module.finrank F (displacementSpace B) ≠ 0 := by
      intro hz
      simp only [hz,zero_pow (by decide : 2 ≠ 0),pow_zero] at hBc
      omega
    omega
  simp only [hdB',one_pow,pow_one] at hBc hBA
  have hdA : Module.finrank E (displacementSpace A) ≤ 1 := by
    apply (Nat.pow_le_pow_iff_right hq).mp
    simpa only [pow_one] using hAB.trans hBc
  have hdA' : Module.finrank E (displacementSpace A) = 1 := by
    have hn : Module.finrank E (displacementSpace A) ≠ 0 := by
      intro hz
      simp only [hz,zero_pow (by decide : 2 ≠ 0),pow_zero] at hAc
      omega
    omega
  simp only [hdA',one_pow,pow_one] at hAc hAB
  exact ⟨le_antisymm hAc hBA,le_antisymm hBc hAB,hdA',hdB'⟩

end Small

/-- If one critical index is below q squared, both images are full roots
of order q, at the original field degree. No field-four comparison is used. -/
theorem replacement_critical_root_actions_of_small
    (path : CriticalPath d.radical g a z) (hb : 0 < g.b d.radical)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < (2^n)^2) :
    ∃ e : CriticalNaturalAction d.radical a z n,
      ∃ f : CriticalNaturalAction d.radical z a n,
        (Q d.radical z).relIndex (Z d.radical a) = 2^n ∧
        (Q d.radical a).relIndex (Z d.radical z) = 2^n ∧
        Module.finrank e.field.Carrier (displacementSpace e.actor.range) = 1 ∧
        Module.finrank f.field.Carrier (displacementSpace f.actor.range) = 1 := by
  obtain ⟨e,f⟩ := replacement_critical_natural_actions h d path hb
  let := finite_Z d.radical a
  let := finite_Z d.radical z
  let : Finite (U d.radical a) :=
    Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  let : Finite (U d.radical z) :=
    Finite.of_injective (inclusion (U_le_Z z)) (inclusion_injective _)
  have hecard : Nat.card e.field.Carrier = 2^n := by rw [e.field.card_eq,e.degree]
  have hfcard : Nat.card f.field.Carrier = 2^n := by rw [f.field.card_eq,f.degree]
  have hia : (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical a) = Nat.card e.actor.range := by
    change ((centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).subgroupOf
      (Z d.radical a)).index = _
    rw [←e.kernel,index_ker]
  have hiz : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z) = Nat.card f.actor.range := by
    change ((centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).subgroupOf
      (Z d.radical z)).index = _
    rw [←f.kernel,index_ker]
  have hB : 1 < Nat.card f.actor.range :=
    (lt_of_lt_of_le (by decide : 1 < 2^2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)).trans_le f.lower_bound
  have hAB : Nat.card (Vector e.field.Carrier ⧸ TwoLocalCover.fixedSpace e.actor.range) ≤
      Nat.card f.actor.range := by
    apply (Theory.SpecificGroups.SymplecticFour.fixed_quotient_card_le_centralizer_index
      (U d.radical z) (Z d.radical a) e.normalized e.projection e.onto e.actor e.conjugation).trans
    rw [←hiz]
    exact relIndex_le_of_le_right (U_le_Z z) index_ne_zero_of_finite
  have hBA : Nat.card (Vector f.field.Carrier ⧸ TwoLocalCover.fixedSpace f.actor.range) ≤
      Nat.card e.actor.range := by
    apply (Theory.SpecificGroups.SymplecticFour.fixed_quotient_card_le_centralizer_index
      (U d.radical a) (Z d.radical z) f.normalized f.projection f.onto f.actor f.conjugation).trans
    rw [←hia]
    exact relIndex_le_of_le_right (U_le_Z a) index_ne_zero_of_finite
  obtain ⟨he,hf,hde,hdf⟩ := reciprocal_small_actors (hecard.trans hfcard.symm)
    e.actor.range f.actor.range hB hAB hBA (by rwa [e.index,hecard])
  exact ⟨e,f,e.index.symm.trans (he.trans hecard),
    f.index.symm.trans (hf.trans hecard),hde,hdf⟩

/-- The numerical critical-index consequence for the original replacement. -/
theorem replacement_critical_indices_eq_field_of_small
    (path : CriticalPath d.radical g a z) (hb : 0 < g.b d.radical)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < (2^n)^2) :
    (Q d.radical z).relIndex (Z d.radical a) = 2^n ∧
      (Q d.radical a).relIndex (Z d.radical z) = 2^n := by
  obtain ⟨e,f,he,hf,_,_⟩ := replacement_critical_root_actions_of_small h d path hb hsmall
  exact ⟨he,hf⟩

/-- Reciprocal critical indices have the original field size as a lower bound. -/
theorem replacement_critical_indices_ge_field
    (path : CriticalPath d.radical g a z) (hb : 0 < g.b d.radical) :
    2^n ≤ (Q d.radical z).relIndex (Z d.radical a) ∧
      2^n ≤ (Q d.radical a).relIndex (Z d.radical z) := by
  obtain ⟨e,f⟩ := replacement_critical_natural_actions h d path hb
  exact ⟨e.index ▸ e.lower_bound,f.index ▸ f.lower_bound⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
