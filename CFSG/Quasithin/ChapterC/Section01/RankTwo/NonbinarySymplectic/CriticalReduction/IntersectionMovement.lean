module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EscapeComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StarRadius
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.StarLower

/-!
# Movement of the critical intersection at nonbinary degree

The reciprocal field-sized indices identify the critical actor with a full
root group. A seed escaping its join with the start layer must move the
actual endpoint intersection: otherwise its action agrees with a root
element modulo the exact vertex centralizer. The semilinear fixed-index
bound on the root hyperplane then gives movement of index at least q.
Central attachments are retained throughout the cover and intersection.

Source: MS93 (3.4), symplectic comparison, p.868.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.OneCohomology Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
section Model
variable {H : Type*} [Group H] [Finite H] {R : Subgroup H}
  {geometry : Geometry R} {a z : Vertex R}
  {F W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W]

theorem critical_root_coordinates_of_reciprocal_index_field
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hCa : C R a = Q R a) (hF : 2 < Nat.card F)
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R z) (β : Z R a →* L (K := F))
    (hβ : ∀ x : Z R a, ∀ w : W,
      j (Multiplicative.ofAdd (σ (β x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹)
    (hcard : Nat.card β.range = Nat.card F) (hindex : (Q R a).relIndex (Z R z) = Nat.card F) :
    Module.finrank F (displacementSpace (β.range.map (commutator (Sp F)).subtype)) = 1 ∧
    (∀ x ∈ β.range.map (commutator (Sp F)).subtype,
      ∀ y ∈ β.range.map (commutator (Sp F)).subtype,
        ∀ v : Vector F, x • (y • v-v)=y • v-v) := by
  let α : Z R a →* Sp F := (commutator (Sp F)).subtype.comp β
  have hαrange : α.range = β.range.map (commutator (Sp F)).subtype :=
    MonoidHom.range_comp _ _
  have hαcard : Nat.card α.range = Nat.card F := by
    rw [hαrange]
    exact (Nat.card_congr (β.range.equivMapOfInjective _
      (commutator (Sp F)).subtype_injective).toEquiv).symm.trans hcard
  have hza : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  have hidx : (centralizer (Z R a : Set (FreeAmalgam R))).relIndex (Z R z) = Nat.card F := by
    rw [←hCa] at hindex
    have he : (C R a).subgroupOf (Z R z) =
        (centralizer (Z R a : Set (FreeAmalgam R))).subgroupOf (Z R z) := by
      ext x
      exact ⟨fun hx => hx.2,fun hx => ⟨hza x.property,hx⟩⟩
    change ((C R a).subgroupOf (Z R z)).index = Nat.card F at hindex
    change ((centralizer (Z R a : Set (FreeAmalgam R))).subgroupOf (Z R z)).index = Nat.card F
    rwa [he] at hindex
  obtain ⟨π,hπ,_,hπact⟩ := exists_equivariant_embedded_projection
    (U R z) (Z R a) (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_actor_normalizes_moving path)
    σ (binaryNatural (K := F)) j hj hjr p.toLinearMap hp.1
    (fun g w => LinearMap.congr_fun (p.isIntertwining' g) w) β hβ
  let := finite_Z R z
  let : Finite (U R z) := Finite.of_injective (inclusion (U_le_Z z)) (inclusion_injective _)
  have hbound : Nat.card (Vector F ⧸ TwoLocalCover.fixedSpace α.range) ≤ Nat.card F := by
    have hh := fixed_quotient_card_le_centralizer_index (U R z) (Z R a)
      (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_actor_normalizes_moving path)
      π hπ α hπact
    exact hh.trans ((relIndex_le_of_le_right (U_le_Z z) index_ne_zero_of_finite).trans hidx.le)
  rw [fixed_quotient_card] at hbound
  have hd : Module.finrank F (displacementSpace α.range) ≤ 1 := by
    by_contra hn
    have htwo : 2 ≤ Module.finrank F (displacementSpace α.range) := by omega
    have hpow := Nat.pow_le_pow_right (by omega : 0 < Nat.card F) htwo
    nlinarith
  have hpositive := card_actor_le_displacement_dimension α.range
  rw [hαcard] at hpositive
  have heq : Module.finrank F (displacementSpace α.range) = 1 := by
    by_contra hn
    have hz : Module.finrank F (displacementSpace α.range) = 0 := by omega
    simp only [hz, zero_pow (by decide : 2 ≠ 0), pow_zero] at hpositive
    omega
  refine ⟨hαrange ▸ heq,?_⟩
  have hquad := CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_embedded_natural_actor_quadratic
    path hb σ p hp j hj hjr β hβ
  intro x hx y hy v
  obtain ⟨x,hx,rfl⟩ := hx
  obtain ⟨y,hy,rfl⟩ := hy
  exact hquad x hx y hy v

variable {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]

/-- The existing inner critical actor is a field-sized root on the given
cover; its literal marking, cover action and quadraticity are retained. -/
theorem critical_inner_root_actor_of_field
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hCa : C R a = Q R a) (hF : 2 < Nat.card F)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R z) (δ : Z R a →* J)
    (hδ : ∀ x : Z R a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹)
    (hδcard : Nat.card δ.range = Nat.card F) (hindex : (Q R a).relIndex (Z R z) = Nat.card F)
    (hAut : Nat.card (F ≃+* F) < Nat.card F) :
    ∃ β : Z R a →* L (K := F),
      Nat.card β.range = Nat.card F ∧
      (∀ x, (e.groupEquiv.symm (β x) : J) = δ x) ∧
      (∀ x : Z R a, ∀ v : s.space.toSubmodule,
        j (Multiplicative.ofAdd (MovedSection.coverAction s e (β x) v)) =
          (x : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹) ∧
      Module.finrank F (displacementSpace (β.range.map (commutator (Sp F)).subtype)) = 1 ∧
      (∀ x ∈ β.range.map (commutator (Sp F)).subtype,
        ∀ y ∈ β.range.map (commutator (Sp F)).subtype,
          ∀ v : Vector F, x • (y • v-v)=y • v-v) := by
  obtain ⟨β,hβcard,hβmark,hβ⟩ := critical_inner_model_actor_of_ringAut_card_lt path hb hF
    s e hp hcent j hj hjr δ hδ (by omega)
  have hcard : Nat.card β.range = Nat.card F := hβcard.trans hδcard
  obtain ⟨hd,hq⟩ := critical_root_coordinates_of_reciprocal_index_field path hb hCa hF
    (MovedSection.coverAction s e) (MovedSection.coverProjection s e) hp j hj hjr β hβ hcard hindex
  exact ⟨β,hcard,hβmark,hβ,hd,hq⟩

variable [FiniteDimensional (ZMod 2) V]

theorem field_card_le_critical_intersection_centralizer_index
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hCa : C R a = Q R a) (hF : 2 < Nat.card F)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hsemi : ∀ g : J, ∃ τ : F ≃+* F, ∀ c v,
      MovedSection.ambientAction s e g (c • v) = τ c • MovedSection.ambientAction s e g v)
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R z)
    (κ : stabilizer R z →* J)
    (hκC : κ.ker.map (stabilizer R z).subtype = C R z)
    (hκ : ∀ x : stabilizer R z, ∀ w : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹)
    (β : Z R a →* L (K := F))
    (hAZ : Z R a ≤ stabilizer R z)
    (hβmark : ∀ x : Z R a, (e.groupEquiv.symm (β x) : J)=κ (inclusion hAZ x))
    (hβ : ∀ x : Z R a, ∀ w : s.space.toSubmodule,
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹)
    (hd : Module.finrank F (displacementSpace (β.range.map (commutator (Sp F)).subtype))=1)
    (hc : Nat.card β.range=Nat.card F)
    (Y : Subgroup (FreeAmalgam R)) (hYZ : Y ≤ stabilizer R z)
    (hmove : ¬ Y ≤ centralizer ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _)) :
    Nat.card F ≤ (centralizer (Y : Set (FreeAmalgam R))).relIndex (Z R z ⊓ Q R a) := by
  let ψ := MovedSection.ambientAction s e
  let σ := MovedSection.coverAction s e
  let p := MovedSection.coverProjection s e
  let δ : Y →* J := κ.comp (inclusion hYZ)
  let P := TwoLocalCover.fixedSpace (β.range.map (commutator (Sp F)).subtype)
  let W := OneCohomology.fixed (σ.comp β.range.subtype)
  let D := (BinaryOffender.fixedSpace ψ δ.range).comap (P.restrictScalars (ZMod 2)).subtype
  have hWP (w : s.space.toSubmodule) : w ∈ W ↔ p w ∈ P := by
    change w ∈ OneCohomology.fixed (σ.comp β.range.subtype) ↔ p w ∈ P
    rw [cover_fixed_preimage p hp]
    constructor
    · intro hw g hg
      obtain ⟨t,ht,rfl⟩ := hg
      exact hw ⟨t,ht⟩
    · intro hw t
      exact hw t.val.val (mem_map_of_mem _ t.property)
  let pP : W →ₗ[ZMod 2] P := (p.toLinearMap.comp W.subtype).codRestrict
    (P.restrictScalars (ZMod 2)) (fun w => (hWP w.val).mp w.property)
  have hpP : Function.Surjective pP := by
    intro v
    obtain ⟨w,hw⟩ := hp.1 v.val
    refine ⟨⟨w,(hWP w).mpr (hw ▸ v.property)⟩,?_⟩
    exact Subtype.ext hw
  let jW : Multiplicative W →* FreeAmalgam R :=
    j.comp W.subtype.toAddMonoidHom.toMultiplicative
  have hZA : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  have hWE : jW.range ≤ Z R z ⊓ Q R a := by
    rintro _ ⟨w,rfl⟩
    have hU : jW w ∈ U R z := by
      rw [←hjr]
      exact ⟨Multiplicative.ofAdd w.toAdd.val,rfl⟩
    refine ⟨U_le_Z z hU,?_⟩
    rw [←hCa]
    refine ⟨hZA (U_le_Z z hU),?_⟩
    intro x hx
    have he := w.toAdd.property (⟨β ⟨x,hx⟩,⟨⟨x,hx⟩,rfl⟩⟩ : β.range)
    change σ (β ⟨x,hx⟩) w.toAdd.val=w.toAdd.val at he
    have hh := hβ ⟨x,hx⟩ w.toAdd.val
    rw [he] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
  have hcentral (w : W)
      (hw : jW (Multiplicative.ofAdd w) ∈ centralizer (Y : Set (FreeAmalgam R))) :
      pP w ∈ D := by
    rintro ⟨g,⟨y,rfl⟩⟩
    change ψ (κ (inclusion hYZ y)) (p w.val) = p w.val
    rw [←MovedSection.coverProjection_ambient s e]
    apply congrArg p
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hκ]
    have he := hw y.val y.property
    change y.val * j (Multiplicative.ofAdd w.val) =
      j (Multiplicative.ofAdd w.val) * y.val at he
    change y.val * j (Multiplicative.ofAdd w.val) * y.val⁻¹ = _
    rw [he,mul_inv_cancel_right]
  have hdim : 2 ≤ Module.finrank F P := by
    have hdim' : Module.finrank F (TwoLocalCover.fixedSpace
        (β.range.map (commutator (Sp F)).subtype)) = 3 := by
      rw [←orthogonal_displacementSpace,
        LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate,hd]
      simp [Theory.SpecificGroups.SymplecticFour.Vector]
    exact hdim'.ge.trans' (by decide : 2 ≤ 3)
  obtain ⟨y,v,hv⟩ := critical_hyperplane_moved_of_intersection_moved path hb hCa
    (by omega) s e hcent κ hκC β hAZ hβmark hd hc Y hYZ hmove
  have hlo : Nat.card F ≤ Nat.card (P ⧸ D) :=
    field_card_le_submodule_fixed_quotient_card_of_semilinear ψ δ.range P hdim
      (fun g _ => hsemi g) ⟨δ y,⟨y,rfl⟩,v,hv⟩
  let := finite_Z R z
  let : Finite (Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let : Finite W := Module.finite_of_finite (ZMod 2)
  exact hlo.trans (quotient_card_le_centralizer_index_of_projection
    (Z R z ⊓ Q R a) Y jW hWE pP hpP D hcentral)

end Model
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Every endpoint actor containing an escaping seed has fixed index at least q
on the full critical intersection. All natural-action and root premises are constructed. -/
theorem Input.replacement_seed_actor_centralizer_index_ge_field
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical)
    (Y : Subgroup (FreeAmalgam d.radical))
    (hYZ : Y ≤ stabilizer d.radical z) (hYQ : Y ≤ Q d.radical a)
    (hn : ¬ Z d.radical z ≤ normalizer ((Y ⊔ Z d.radical a :
      Subgroup (FreeAmalgam d.radical)) : Set _))
    (D : Subgroup (FreeAmalgam d.radical)) (hYD : Y ≤ D) (hDZ : D ≤ stabilizer d.radical z) :
    Nat.card F ≤ (centralizer (D : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z ⊓ Q d.radical a) := by
  obtain ⟨hz,ha⟩ := h.replacement_critical_indices_eq_field_of_seed_escape d path hb Y hYZ hYQ hn
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d path.end_color
  have hFc : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hFl : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hAut : Nat.card (E.Carrier ≃+* E.Carrier) < Nat.card E.Carrier := by
    rw [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
      (show Nat.card E.Carrier = 2 ^ n by rw [E.card_eq,hE]),E.card_eq,hE]
    exact n.lt_two_pow_self
  have hAZ : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ := κ.comp (inclusion hAZ)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (quotient_image_card _ _ _ hAZ κ hκQ).trans (hz.trans hFc.symm)
  have hδ : ∀ x : Z d.radical a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam d.radical) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam d.radical)⁻¹ :=
    fun x v => hconj (inclusion hAZ x) v
  have hCa := C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hcent := (h.replacement_component_image_structure d).2.2.2.2
  obtain ⟨β,hβcard,hβmark,hβ,hd,hquad⟩ := critical_inner_root_actor_of_field path hb hCa hFl
    s e he hcent j hj hjr δ hδ hδcard (ha.trans hFc.symm) hAut
  have hmove : ¬ Y ≤ centralizer ((Z d.radical z ⊓ Q d.radical a :
      Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hfix
    exact critical_escape_of_seed_join_nonnormalization path Y hn
      (critical_seed_displacement_le_of_fixed_intersection path hb hCa hFl
        s e he hcent j hj hjr κ hκC hconj β hAZ hβmark hβ hd hβcard Y hYZ hfix)
  rw [←hFc]
  exact field_card_le_critical_intersection_centralizer_index path hb hCa hFl
    s e he hsemi hcent j hj hjr κ hκC hconj β hAZ hβmark hβ hd hβcard
    D hDZ (fun hfix => hmove (hYD.trans hfix))

/-- The same estimate for a literal full-Sylow seed inside the constructed
source star. The radius theorem supplies its containment in the start core. -/
theorem Input.replacement_sourceStar_seed_index_ge_field
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    {z : Vertex d.radical} (path : CriticalPath d.radical geometry (alpha d.radical) z)
    (Y : Subgroup d.radical) (P₀ : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P₀)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical)))
    (u : Vertex d.radical) (P : Sylow 2 (Ltilde d.radical u))
    (hseed : componentSylowSeed d.radical u P ≤ sourceStarAlpha d.radical Y)
    (hUZ : Z d.radical u ≤ stabilizer d.radical z)
    (hescape : ¬ Z d.radical z ≤ normalizer
      ((componentSylowSeed d.radical u P ⊔ Z d.radical (alpha d.radical) :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    Nat.card F ≤ (centralizer (Z d.radical u : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z ⊓ Q d.radical (alpha d.radical)) := by
  have hU : componentSylowSeed d.radical u P ≤ Z d.radical u :=
    inf_le_left.trans (U_le_Z u)
  exact h.replacement_seed_actor_centralizer_index_ge_field d path hb
    (componentSylowSeed d.radical u P) (hU.trans hUZ)
    (hseed.trans (h.replacement_sourceStarAlpha_le_own_core d geometry hb Y P₀ hY hn))
    hescape (Z d.radical u) hU hUZ

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
