module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.ReciprocalActors

/-!
# Marked critical roots at the original field degree

When the reciprocal critical indices equal the field order, the displacement
space in any specified natural cover is a line. The inner actor keeps the
original quotient marking and the whole central kernel. The argument uses the
field order at the original degree and makes no field-four assumption.

This is the root-coordinate calculation of MS93 (3.3), printed p.867, used
by the whole-X and secondary-kernel calculations for (3.6), pp.870--871.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
section Root
variable {H : Type*} [Group H] [Finite H] {R : Subgroup H}
  {geometry : Geometry R} {a z : Vertex R}
  {F W : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W]
private theorem root_coordinates_of_field_index
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hCa : C R a = Q R a) (σ : Representation (ZMod 2) (L (K := F)) W)
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
    apply (Nat.pow_le_pow_iff_right (Finite.one_lt_card : 1 < Nat.card F)).mp
    simpa only [pow_one] using hbound
  have hpositive := card_actor_le_displacement_dimension α.range
  rw [hαcard] at hpositive
  have heq : Module.finrank F (displacementSpace α.range) = 1 := by
    have hn : Module.finrank F (displacementSpace α.range) ≠ 0 := by
      intro hz
      simp only [hz, zero_pow (by decide : 2 ≠ 0), pow_zero] at hpositive
      exact (not_le_of_gt (Finite.one_lt_card : 1 < Nat.card F)) hpositive
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
theorem inner_root_actor_of_field_index
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hCa : C R a = Q R a) {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R z) (δ : Z R a →* J)
    (hδ : ∀ x : Z R a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹)
    (hδcard : Nat.card δ.range = Nat.card F) (hindex : (Q R a).relIndex (Z R z) = Nat.card F) :
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
  have hcardF : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hn)
  obtain ⟨β,hβcard,hβmark,hβ⟩ := critical_inner_model_actor_of_field_bound path hb hcardF
    s e hp hcent j hj hjr δ hδ (by
      rw [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hF,hδcard,hF]
      exact Nat.lt_two_pow_self)
  have hcard : Nat.card β.range = Nat.card F := hβcard.trans hδcard
  obtain ⟨hd,hq⟩ := root_coordinates_of_field_index path hb hCa
    (MovedSection.coverAction s e) (MovedSection.coverProjection s e) hp j hj hjr β hβ hcard hindex
  exact ⟨β,hcard,hβmark,hβ,hd,hq⟩

end Root

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
