module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.NaturalGeneration.TransportInput
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.RelativeClosure

/-!
# Natural-plane coordinates on the actual opposite local closure

The first marked parabolic fixes the selected vector, so the coordinate image
of its raw closure stays cyclic. Adjoining Z contributes zero. Taking the
opposite local closure then gives exactly the literal opposite-parabolic orbit
span: one inclusion follows from invariance, and the other lifts each model
actor through the actual untilded local residual.

Composing this restriction with the supplied plane coordinates constructs a
natural rank-one factor with its exact intrinsic N-kernel and ambient
conjugation action. The matrix construction of the plane coordinates remains
an explicit, independent input; this is the conditional transport used by the
source assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.7), printed pp.847--848, and its application on p.883.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.NaturalGeneration
open RankOnePairing RankOnePairing.Incidence
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof
variable {G : Type*} [Group G]
variable {π : G →* SL} {flag : SL} {i : Bool} {H N Z : Subgroup G} {x : G}

private theorem closure_coordinate_bound (n : NaturalFactor π ⊤ H N)
    (P X : Subgroup G) (T : Subgroup VectorGroup)
    (hX : X ≤ (T.comap n.coordinates).map H.subtype)
    (hT : ∀ p ∈ P, ∀ v ∈ T, vectorAction (n.marking (π p)) v ∈ T) :
    localGenerated P X ≤ (T.comap n.coordinates).map H.subtype := by
  apply (localGenerated_le_conjugates P X).trans
  apply iSup_le
  intro p y hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨w, hw, rfl⟩ := hX hz
  let w' : H := ⟨(p : G) * (w : G) * (p : G)⁻¹,
    (mem_normalizer_iff.mp (n.normalized (mem_top _)) _).mp w.property⟩
  refine ⟨w', ?_, rfl⟩
  change n.coordinates w' ∈ T
  have he : n.coordinates w' = vectorAction (n.marking (π p)) (n.coordinates w) :=
    n.action p (mem_top _) w w' rfl
  rw [he]
  exact hT p p.property _ hw

private theorem orbitSpan_invariant (σ : MulAut SL) (flag : SL) (i : Bool)
    (v : VectorGroup) (g : modelParabolic flag (!i)) :
    ∀ w ∈ oppositeSpan σ flag i v, vectorAction (σ g) w ∈ oppositeSpan σ flag i v := by
  change oppositeSpan σ flag i v ≤
    (oppositeSpan σ flag i v).comap (vectorAction (σ g)).toMonoidHom
  apply (closure_le _).mpr
  rintro _ ⟨a, rfl⟩
  change vectorAction (σ g) (vectorAction (σ a) v) ∈ oppositeSpan σ flag i v
  rw [← action_mul, ← map_mul]
  exact subset_closure ⟨g * a, rfl⟩

namespace NaturalSeedData
variable (d : NaturalSeedData π flag i H N Z x)

private theorem kernel_le_parabolic (j : Bool) : π.ker ≤ parabolic π flag j := by
  intro g hg
  change π g ∈ modelParabolic flag j
  rw [MonoidHom.mem_ker.mp hg]
  exact one_mem _

include d in
private theorem first_le_group : localGenerated (parabolic π flag i) (zpowers x) ≤ H :=
  localGenerated_le_of_normalizes _ _ H (le_top.trans d.natural.normalized)
    (zpowers_le.mpr d.element_mem)

private theorem seed_le_group : d.seed ≤ H :=
  sup_le (d.z_le_fixed.trans d.fixed_le_group) d.first_le_group

private theorem seed_le_kernel : d.seed ≤ π.ker :=
  sup_le d.z_le_kernel (localGenerated_le_of_normalizes _ _ π.ker
    (le_top.trans le_normalizer_of_normal) (zpowers_le.mpr d.element_kernel))

private theorem element_mem_seed : x ∈ d.seed :=
  (le_sup_right : localGenerated (parabolic π flag i) (zpowers x) ≤ d.seed)
    (le_localGenerated _ _
    ((zpowers_le.mpr d.element_kernel).trans (kernel_le_parabolic i))
    (mem_zpowers x))

private theorem seed_coordinate_bound :
    d.seed ≤ ((zpowers d.vector).comap d.natural.coordinates).map H.subtype := by
  apply sup_le
  · intro z hz
    refine ⟨⟨z, d.fixed_le_group (d.z_le_fixed hz)⟩, ?_, rfl⟩
    have hk : (⟨z, d.fixed_le_group (d.z_le_fixed hz)⟩ : H) ∈ d.natural.coordinates.ker := by
      rw [d.natural.kernel]
      exact d.z_le_fixed hz
    change d.natural.coordinates _ ∈ zpowers d.vector
    rw [MonoidHom.mem_ker.mp hk]
    exact one_mem _
  · apply closure_coordinate_bound d.natural
    · intro y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      refine ⟨⟨x, d.element_mem⟩ ^ k, ?_, rfl⟩
      change d.natural.coordinates (⟨x, d.element_mem⟩ ^ k) ∈ zpowers d.vector
      rw [map_zpow]
      exact zpow_mem (mem_zpowers d.vector) k
    · intro p hp v hv
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
      rw [map_zpow]
      have he : vectorAction (d.natural.marking (π p)) d.vector = d.vector := d.fixed _ hp
      rw [he]
      exact zpow_mem (mem_zpowers d.vector) k

private theorem vector_mem_span : d.vector ∈ oppositeSpan d.natural.marking flag i d.vector := by
  have h : vectorAction (d.natural.marking (1 : SL)) d.vector ∈
      oppositeSpan d.natural.marking flag i d.vector := subset_closure ⟨1, rfl⟩
  simpa only [map_one, action_one] using h

/-- The actual opposite local closure lies in the natural coordinate carrier. -/
theorem local_le_group : localGenerated (parabolic π flag (!i)) d.seed ≤ H :=
  localGenerated_le_of_normalizes _ _ H (le_top.trans d.natural.normalized) d.seed_le_group

/-- Restrict the given natural coordinates to the literal opposite local closure. -/
def localCoordinates : localGenerated (parabolic π flag (!i)) d.seed →* VectorGroup :=
  d.natural.coordinates.comp (inclusion d.local_le_group)

private theorem local_coordinate_bound :
    localGenerated (parabolic π flag (!i)) d.seed ≤
      ((oppositeSpan d.natural.marking flag i d.vector).comap d.natural.coordinates).map H.subtype := by
  apply closure_coordinate_bound d.natural
  · exact d.seed_coordinate_bound.trans
      (map_mono (comap_mono (zpowers_le.mpr d.vector_mem_span)))
  · intro p hp
    exact orbitSpan_invariant _ _ _ _ ⟨π p, hp⟩

/-- The coordinate image is precisely the full opposite-parabolic orbit span. -/
theorem localCoordinates_range : d.localCoordinates.range =
    oppositeSpan d.natural.marking flag i d.vector := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz, he⟩ := d.local_coordinate_bound y.property
    have he' : z = inclusion d.local_le_group y := Subtype.ext he
    change d.natural.coordinates z ∈ oppositeSpan d.natural.marking flag i d.vector at hz
    rw [he'] at hz
    exact hz
  · apply (closure_le _).mpr
    rintro _ ⟨a, rfl⟩
    obtain ⟨p, hp, he⟩ := (show (a : SL) ∈
        (localResidual (parabolic π flag (!i))).map π from
      (d.residual_image (!i)).symm ▸ a.property)
    have hpP : p ∈ parabolic π flag (!i) := map_subtype_le _ hp
    have hxY : x ∈ localGenerated (parabolic π flag (!i)) d.seed :=
      le_localGenerated _ _ (d.seed_le_kernel.trans (kernel_le_parabolic (!i))) d.element_mem_seed
    let y : localGenerated (parabolic π flag (!i)) d.seed :=
      ⟨p * x * p⁻¹, (mem_normalizer_iff.mp
        (localGenerated_normalized _ _ hpP) _).mp hxY⟩
    refine ⟨y, ?_⟩
    have ha := d.natural.action p (mem_top _) ⟨x, d.element_mem⟩
      (inclusion d.local_le_group y) rfl
    change d.localCoordinates y = vectorAction (d.natural.marking a) d.vector
    rw [he] at ha
    exact ha

/-- Restriction preserves the exact intrinsic kernel on the opposite local closure. -/
theorem localCoordinates_kernel : d.localCoordinates.ker =
    N.subgroupOf (localGenerated (parabolic π flag (!i)) d.seed) := by
  ext y
  change inclusion d.local_le_group y ∈ d.natural.coordinates.ker ↔ (y : G) ∈ N
  rw [d.natural.kernel]
  rfl

/-- Explicit natural-plane coordinates give the actual untilded local actor
and the natural rank-one factor on the opposite local closure. -/
theorem rankOneFactor_nonempty
    (c : PlaneCoordinates d.natural.marking flag i d.vector) :
    Nonempty (RankOneFactor (localResidual (parabolic π flag (!i)))
      (localGenerated (parabolic π flag (!i)) d.seed) N) := by
  let P := parabolic π flag (!i)
  let K := localResidual P
  let Y := localGenerated P d.seed
  let T := oppositeSpan d.natural.marking flag i d.vector
  have hKP : K ≤ P := map_subtype_le _
  let actor : K →* modelParabolic flag (!i) :=
    (π.comp K.subtype).codRestrict _ (fun l => hKP l.property)
  have actor_surjective : Function.Surjective actor := by
    intro a
    obtain ⟨l, hl, he⟩ := (show (a : SL) ∈ K.map π from
      (d.residual_image (!i)).symm ▸ a.property)
    exact ⟨⟨l, hl⟩, Subtype.ext he⟩
  have hT : ∀ y : Y, d.localCoordinates y ∈ T := by
    intro y
    change d.localCoordinates y ∈ oppositeSpan d.natural.marking flag i d.vector
    rw [← d.localCoordinates_range]
    exact ⟨y, rfl⟩
  let plane : Y →* T := d.localCoordinates.codRestrict T hT
  have plane_surjective : Function.Surjective plane := by
    intro v
    obtain ⟨y, hy⟩ := (show (v : VectorGroup) ∈ d.localCoordinates.range from
      d.localCoordinates_range.symm ▸ v.property)
    exact ⟨y, Subtype.ext hy⟩
  refine ⟨{
    projection := c.projection.comp actor
    surjective := c.surjective.comp actor_surjective
    coordinates := c.coordinates.toMonoidHom.comp plane
    coordinates_surjective := c.coordinates.surjective.comp plane_surjective
    kernel := ?_
    normalized := hKP.trans (localGenerated_normalized P d.seed)
    action := ?_ }⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ c.coordinates.injective,
      MonoidHom.ker_codRestrict, d.localCoordinates_kernel]
  · intro l u v hv
    apply c.action (actor l) (plane u) (plane v)
    exact d.natural.action l (mem_top _) (inclusion d.local_le_group u)
      (inclusion d.local_le_group v) hv

end NaturalSeedData
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.NaturalGeneration
