module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallImages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.LargeDisplacement

/-!
# Critical root indices from an escaping Sylow seed

When the critical endpoint fails to normalize the seed joined with the
start layer, it moves outside the critical commutator. If the critical
image had order at least q², its quadratic natural displacement would be
a self-orthogonal plane. Centralizing its lifts puts the auxiliary actor
inside the component. The resulting orthogonal refinement bounds the
critical image by 2q, contradicting q > 2. Reciprocal comparison then
makes both actual critical indices equal q.

Source: MS93 (3.3), p.867, and the symplectic branch of (3.4), p.868.
The escaping-seed premise is retained for the star-selection argument.
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
variable {M J V F : Type*} [Group M] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V]
  {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
  {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

theorem critical_large_actor_excluded_of_escape
    [FiniteDimensional (ZMod 2) V]
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R)) (hYZ : Y ≤ stabilizer R z)
    (hF : 2 < Nat.card F)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R)
    (hj : Function.Injective j) (hjr : j.range = U R z)
    (κ : stabilizer R z →* J)
    (hk : κ.ker.map (stabilizer R z).subtype = C R z)
    (hB : ((Ltilde R z).subgroupOf (stabilizer R z)).map κ = B)
    (hconj : ∀ (g : stabilizer R z) (v : s.space.toSubmodule),
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ g) v)) =
        (g : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(g : FreeAmalgam R)⁻¹)
    (β : Z R a →* L (K := F))
    (hβ : ∀ x : Z R a,
      (e.groupEquiv.symm (β x) : J) = κ ⟨x,Z_le_stabilizer_of_dist_le a
        (geometry.exists_critical a path.start_color) path.critical.1.le x.property⟩)
    (hker : ∀ w : s.space.toSubmodule, MovedSection.coverProjection s e w=0 ↔
      j (Multiplicative.ofAdd w) ∈ centralizer (Ltilde R z : Set (FreeAmalgam R)))
    (hc : Y ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set _))
    (hbad : ¬ ⁅Z R z,Y⁆ ≤ ⁅Z R a,Z R z⁆)
    (hlarge : Nat.card F ^ 2 ≤ Nat.card β.range) : False := by
  have hgap : 2 * Nat.card F < Nat.card F ^ 2 := by nlinarith
  have hbig : Nat.card F < Nat.card β.range := by nlinarith
  let α : Z R a →* Sp F := (commutator (Sp F)).subtype.comp β
  let p := MovedSection.coverProjection s e
  let σ := MovedSection.coverAction s e
  have hβact (x : Z R a) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (β x) w)) =
        (x : FreeAmalgam R)*j (Multiplicative.ofAdd w)*(x : FreeAmalgam R)⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation (e.groupEquiv.symm (β x)) w)) = _
    rw [hβ]
    exact hconj _ w
  have hcard : Nat.card α.range=Nat.card β.range := by
    have he : α.range = β.range.map (commutator (Sp F)).subtype := MonoidHom.range_comp _ _
    rw [he]
    exact Nat.card_congr (Subgroup.equivMapOfInjective β.range _ Subtype.val_injective).toEquiv.symm
  obtain ⟨π,hπ⟩ := exists_embedded_projection (U R z) j hj hjr p.toLinearMap
  have hα (x : Z R a) (w : s.space.toSubmodule) : p (σ (β x) w)=α x • p w :=
    LinearMap.congr_fun (p.isIntertwining' (β x)) w
  obtain ⟨hP,_,hcover⟩ :=
    CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_displacement_plane_and_cover
      path hb σ j hj hjr β hβact p.toLinearMap hp.1 α hα π hπ (by omega)
  have hfix (x : Z R a) (v : Vector F) (hv : v ∈ displacementSpace α.range) :
      MovedSection.ambientAction s e
        (κ ⟨x,Z_le_stabilizer_of_dist_le a
          (geometry.exists_critical a path.start_color) path.critical.1.le x.property⟩) v=v := by
    rw [←hβ, MovedSection.ambientAction_component,e.groupEquiv.apply_symm_apply]
    have hv' : v ∈ TwoLocalCover.fixedSpace α.range := by
      rw [←orthogonal_displacementSpace,hP]
      exact hv
    exact hv' (α x) ⟨x,rfl⟩
  obtain ⟨hinner,hcomm⟩ := critical_inner_plane_actors path Y hYZ s e (by omega) hcent
    j hj hjr κ hk hB hconj π hπ (displacementSpace α.range) hP hcover hfix hc
  have hbound := critical_large_actor_card_le_of_critical_escape
    path hb Y σ p hp j hj hjr β hβact hker hinner hcomm hc hbad (by omega)
  nlinarith


end Model
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- An actual escaping actor excludes the large critical image on the replacement. -/
theorem Input.replacement_critical_index_lt_square_of_escape
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical)
    (Y : Subgroup (FreeAmalgam d.radical))
    (hYZ : Y ≤ stabilizer d.radical z)
    (hcentral : Y ≤ centralizer ((⁅Z d.radical a,Z d.radical z⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _))
    (hbad : ¬ ⁅Z d.radical z,Y⁆ ≤ ⁅Z d.radical a,Z d.radical z⁆) :
    (Q d.radical z).relIndex (Z d.radical a) < Nat.card F ^ 2 := by
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
  have hAZ : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ := κ.comp (inclusion hAZ)
  have hcard : Nat.card δ.range = (Q d.radical z).relIndex (Z d.radical a) :=
    quotient_image_card _ _ _ hAZ κ hκQ
  have hδ : ∀ x : Z d.radical a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam d.radical) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam d.radical)⁻¹ :=
    fun x v => hconj (inclusion hAZ x) v
  have hAut : Nat.card (E.Carrier ≃+* E.Carrier) < Nat.card δ.range := by
    rw [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
      (show Nat.card E.Carrier = 2 ^ n by rw [E.card_eq,hE]),hcard]
    have hdeg : n < Nat.card F := by rw [h.field_card]; exact n.lt_two_pow_self
    exact hdeg.trans_le (h.replacement_critical_indices_ge_field d path hb).1
  have hcent := (h.replacement_component_image_structure d).2.2.2.2
  obtain ⟨β,hβcard,hβmark,hβ⟩ := critical_inner_model_actor_of_ringAut_card_lt
    path hb hFl s e he hcent j hj hjr δ hδ hAut
  apply Nat.lt_of_not_ge
  intro hlarge
  exact critical_large_actor_excluded_of_escape path hb Y hYZ hFl s e he hcent
    j hj hjr κ hκC hκL hconj β hβmark hker hcentral hbad
    (by rwa [hβcard,hcard,hFc])

/-- Seed-join escape forces both literal critical indices to equal the field size. -/
theorem Input.replacement_critical_indices_eq_field_of_seed_escape
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical)
    (Y : Subgroup (FreeAmalgam d.radical))
    (hYZ : Y ≤ stabilizer d.radical z) (hYQ : Y ≤ Q d.radical a)
    (hn : ¬ Z d.radical z ≤ normalizer ((Y ⊔ Z d.radical a :
      Subgroup (FreeAmalgam d.radical)) : Set _)) :
    (Q d.radical z).relIndex (Z d.radical a) = Nat.card F ∧
      (Q d.radical a).relIndex (Z d.radical z) = Nat.card F := by
  have hcentral : Y ≤ centralizer ((⁅Z d.radical a,Z d.radical z⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _) :=
    (hYQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a path.start_color)))).trans
      (centralizer_le (critical_commutator_le_start_seed path))
  exact h.replacement_small_critical_indices_eq_field d path hb
    (h.replacement_critical_index_lt_square_of_escape d path hb Y hYZ hcentral
      (critical_escape_of_seed_join_nonnormalization path Y hn))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
