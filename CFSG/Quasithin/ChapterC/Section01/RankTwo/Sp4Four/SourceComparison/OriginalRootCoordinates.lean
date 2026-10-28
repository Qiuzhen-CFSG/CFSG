module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.XMovement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.CriticalIndex

/-!
# Original critical-root coordinates and movement of the full X-layer

The reciprocal index four bounds the fixed-space quotient of any given
critical natural cover by four. Symplectic orthogonality and the actor order
therefore force a one-dimensional displacement space over the field of four
elements. The critical geometry also supplies quadraticity. These conclusions
retain the original cover, its embedding, and the exact inner actor marking.

The source consumer constructs this root from the original small-index branch
and applies it to the whole X-layer. No decomposition of X or splitting of its
central attachment is assumed. This supplies the movement premise for the
four-conjugate saturation proof of X = U C_X(L).

Source: Meierfrankenfeld--Stellmacher (1993), (3.3), printed p.867.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource Representation.SymplecticFourOrthogonalCover MSCentralOrbit Theory.GroupTheory
variable {H : Type*} [Group H] [Finite H] {R : Subgroup H}
  {geometry : Geometry R} {a z : Vertex R}
  {F W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The literal reciprocal seed index forces a root line for the given cover. -/
theorem critical_root_coordinates_of_reciprocal_index_four
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hCa : C R a = Q R a) (hF : Nat.card F = 4)
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R z) (β : Z R a →* L (K := F))
    (hβ : ∀ x : Z R a, ∀ w : W,
      j (Multiplicative.ofAdd (σ (β x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹)
    (hcard : Nat.card β.range = 4) (hindex : (Q R a).relIndex (Z R z) = 4) :
    Module.finrank F (displacementSpace (β.range.map (commutator (Sp F)).subtype)) = 1 ∧
    (∀ x ∈ β.range.map (commutator (Sp F)).subtype,
      ∀ y ∈ β.range.map (commutator (Sp F)).subtype,
        ∀ v : Vector F, x • (y • v-v)=y • v-v) := by
  let α : Z R a →* Sp F := (commutator (Sp F)).subtype.comp β
  have hαrange : α.range = β.range.map (commutator (Sp F)).subtype :=
    MonoidHom.range_comp _ _
  have hαcard : Nat.card α.range = 4 := by
    rw [hαrange]
    exact (Nat.card_congr (β.range.equivMapOfInjective _
      (commutator (Sp F)).subtype_injective).toEquiv).symm.trans hcard
  have hza : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  have hidx : (centralizer (Z R a : Set (FreeAmalgam R))).relIndex (Z R z) = 4 := by
    rw [←hCa] at hindex
    have he : (C R a).subgroupOf (Z R z) =
        (centralizer (Z R a : Set (FreeAmalgam R))).subgroupOf (Z R z) := by
      ext x
      exact ⟨fun hx => hx.2,fun hx => ⟨hza x.property,hx⟩⟩
    change ((C R a).subgroupOf (Z R z)).index = 4 at hindex
    change ((centralizer (Z R a : Set (FreeAmalgam R))).subgroupOf (Z R z)).index = 4
    rwa [he] at hindex
  obtain ⟨π,hπ,_,hπact⟩ := exists_equivariant_embedded_projection
    (U R z) (Z R a) (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_actor_normalizes_moving path)
    σ (binaryNatural (K := F)) j hj hjr p.toLinearMap hp.1
    (fun g w => LinearMap.congr_fun (p.isIntertwining' g) w) β hβ
  let := finite_Z R z
  let : Finite (U R z) := Finite.of_injective (inclusion (U_le_Z z)) (inclusion_injective _)
  have hbound : Nat.card (Vector F ⧸ TwoLocalCover.fixedSpace α.range) ≤ 4 := by
    have hh := fixed_quotient_card_le_centralizer_index (U R z) (Z R a)
      (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_actor_normalizes_moving path)
      π hπ α hπact
    exact hh.trans ((relIndex_le_of_le_right (U_le_Z z) index_ne_zero_of_finite).trans hidx.le)
  rw [fixed_quotient_card,hF] at hbound
  have hd : Module.finrank F (displacementSpace α.range) ≤ 1 := by
    by_contra hn
    have htwo : 2 ≤ Module.finrank F (displacementSpace α.range) := by omega
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 4) htwo
    omega
  have hpositive := card_actor_le_displacement_dimension α.range
  rw [hF,hαcard] at hpositive
  have heq : Module.finrank F (displacementSpace α.range) = 1 := by
    interval_cases hh : Module.finrank F (displacementSpace α.range) <;> simp_all
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
theorem critical_inner_root_actor
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hCa : C R a = Q R a) (hF : Nat.card F = 4)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R z) (δ : Z R a →* J)
    (hδ : ∀ x : Z R a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹)
    (hδcard : Nat.card δ.range = 4) (hindex : (Q R a).relIndex (Z R z) = 4) :
    ∃ β : Z R a →* L (K := F),
      Nat.card β.range = 4 ∧
      (∀ x, (e.groupEquiv.symm (β x) : J) = δ x) ∧
      (∀ x : Z R a, ∀ v : s.space.toSubmodule,
        j (Multiplicative.ofAdd (MovedSection.coverAction s e (β x) v)) =
          (x : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹) ∧
      Module.finrank F (displacementSpace (β.range.map (commutator (Sp F)).subtype)) = 1 ∧
      (∀ x ∈ β.range.map (commutator (Sp F)).subtype,
        ∀ y ∈ β.range.map (commutator (Sp F)).subtype,
          ∀ v : Vector F, x • (y • v-v)=y • v-v) := by
  obtain ⟨β,hβcard,hβmark,hβ⟩ := critical_inner_model_actor path hb hF
    s e hp hcent j hj hjr δ hδ (by omega)
  have hcard : Nat.card β.range = 4 := hβcard.trans hδcard
  obtain ⟨hd,hq⟩ := critical_root_coordinates_of_reciprocal_index_four path hb hCa hF
    (MovedSection.coverAction s e) (MovedSection.coverProjection s e) hp j hj hjr β hβ hcard hindex
  exact ⟨β,hcard,hβmark,hβ,hd,hq⟩

variable [Finite J]

/-- The original small-index source branch bounds movement of the whole
X-layer by four. Both root coordinates and its inner marking are constructed;
no decomposition or fixed supplement of X is assumed. -/
theorem original_small_critical_X_movement_le_four
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hsmall : (Q R z).relIndex (Z R a) < 16) :
    (centralizer (Z R z : Set (FreeAmalgam R))).relIndex (X R a) ≤ 4 := by
  obtain ⟨he,ha⟩ := original_small_critical_indices_eq_four R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb hsmall
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (MSCentralOrbit.centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,hecov,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hconj,hproj,hker⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore
      hc hC hsq path.end_color
  have hFcard : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  have hAZ : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ : Z R a →* J := κ.comp (inclusion hAZ)
  have hδcard : Nat.card δ.range = 4 :=
    (quotient_image_card _ _ _ hAZ κ hκQ).trans he
  have hδ : ∀ x : Z R a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹ :=
    fun x v => hconj (inclusion hAZ x) v
  have hCa := MSCentralOrbit.C_eq_Q R hp hQR hfaith a path.start_color
  obtain ⟨β,hβcard,hβmark,hβ,hd,hquad⟩ := critical_inner_root_actor path hb hCa hFcard
    s e hecov hC j hj hjr δ hδ hδcard ha
  have hh := critical_X_movement_bound_of_vertex_coordinates path hb
    (MSCentralOrbit.edgeCentralizerCondition R hp hQR hfaith) hCa (by omega : 2 < Nat.card F.Carrier)
    s e hecov hC j hj hjr κ hκC hconj β hβ hd
  rwa [hFcard] at hh

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
