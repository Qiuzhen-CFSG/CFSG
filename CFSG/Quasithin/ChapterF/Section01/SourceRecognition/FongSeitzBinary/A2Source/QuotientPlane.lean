module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TriangleGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneValence
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.NaturalCore
public import Theory.Combinatorics.TranslationPlane.Coordinates

/-!
# One-field affine incidence coordinates on the same source quotient

For the marked quotient of a genuine locally rank-one source triple, the
m=3 BN geometry and the two original natural actions construct a projective
plane on its two full parabolic coset fibers. The quotient map is a local
covering; it transports original neighborhood fixation, and overlap
faithfulness proves movement of nontrivial core elements. Conjugacy in the
original natural actor makes the whole centerfree core an elation group.
It acts regularly on the q² affine points.

Coordinates use that original core and exactly d.q, retaining the original
actor and its supplied SL₂ quotient map. Its marked fixed field line gives
the base pencil; actor transitivity gives every direction, and translations
give every affine line. No isomorphism between the two local fields, local
perfectness, mixed root relation or model recognition is assumed.

The natural-action, centerfree and m=3 premises are earlier source inputs.
This establishes the affine-incidence bridge for a quotient of that source
carrier. Transport through an independently marked amalgam, the projective
model identification, six compatible roots and the final recognition
comparison remain subsequent obligations; this module does not assert them.

Source: DGS, Groups and Graphs, 10.5 and Theorem D, printed pp.156,224.
-/

@[expose] public noncomputable section
open Subgroup Configuration
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace QuotientPlane
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable (d : MarkedQuotient P) (h : LocallyRankOneTriple P B)

/-- The quotient map is a covering on the original, ordered coset fibers. -/
theorem cover : CoverData (family P) (TriangleGeometry.family d) d.q where
  surjective := QuotientGroup.mk'_surjective _
  map_eq i := by cases i <;> exact d.parabolic_image _
  injective i := by
    cases i
    · change Function.Injective (fun a : P 0 => d.q a)
      intro a b hab
      exact (d.endpointEquiv 0).injective (Subtype.ext
        ((d.endpointEquiv_apply 0 a).trans (hab.trans (d.endpointEquiv_apply 0 b).symm)))
    · change Function.Injective (fun a : P 1 => d.q a)
      intro a b hab
      exact (d.endpointEquiv 1).injective (Subtype.ext
        ((d.endpointEquiv_apply 1 a).trans (hab.trans (d.endpointEquiv_apply 1 b).symm)))
  map_inf := d.borel_image.trans d.standard_intersection.symm

include h in
/-- The original generating pair maps to the same two whole parabolics. -/
theorem generate : TriangleGeometry.family d false ⊔ TriangleGeometry.family d true = ⊤ := by
  change d.tits.standardParabolic {d.simple 0} ⊔ d.tits.standardParabolic {d.simple 1} = ⊤
  rw [← d.parabolic_image 0, ← d.parabolic_image 1, ← Subgroup.map_sup, h.generate,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

include h in
/-- Original overlap faithfulness implies faithfulness on the quotient vertices. -/
theorem faithful : FaithfulSMul (G ⧸ d.D) (Vertex (TriangleGeometry.family d)) := by
  apply faithfulSMul_iff.mpr
  intro g hg
  have hk : g ∈ (MulAction.toPermHom (G ⧸ d.D) (Vertex (TriangleGeometry.family d))).ker :=
    Equiv.Perm.ext hg
  rw [global_kernel] at hk
  change g ∈ (d.tits.standardParabolic {d.simple 0} ⊓ d.tits.standardParabolic {d.simple 1}).normalCore at hk
  rw [d.standard_intersection,d.borel_core_eq_bot h.generate (by
    rw [h.intersection]
    exact h.faithful _ inferInstance B.normalCore_le)] at hk
  exact hk

variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
variable
  (c₀ : BOneActionData (family P) (base (family P) false) (base (family P) true) k₀ W₀)
  (c₁ : BOneActionData (family P) (base (family P) true) (base (family P) false) k₁ W₁)
  (hn₀ : B ≤ normalizer (c₀.actor : Set G)) (hn₁ : B ≤ normalizer (c₁.actor : Set G))
  (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))

include h c₀ c₁ hn₀ hn₁ E₀ in
/-- Local bijectivity transports the natural-action valence to the actual quotient. -/
theorem neighbor_card (v : Vertex (TriangleGeometry.family d)) :
    Nat.card ((graph (TriangleGeometry.family d)).neighborSet v) = Nat.card k₁ + 1 := by
  obtain ⟨w,rfl⟩ := (cover d).vertex_surjective v
  have hc := Nat.card_congr (Equiv.ofBijective ((cover d).hom.mapNeighborSet w)
    ((cover d).neighbor_bijective w))
  change Nat.card ((graph (family P)).neighborSet w) =
    Nat.card ((graph (TriangleGeometry.family d)).neighborSet ((cover d).vertex w)) at hc
  rw [←hc,neighbor_card_of_actions h c₀ c₁ hn₀ hn₁ E₀,
    paired_field_orders_eq h c₀ c₁ E₀]

variable (hm : RootCoordinates.rotationOrder d = 3)

/-- The plane is built from the original natural actions and the same m=3 quotient.
No diameter, geodesic or valence hypothesis remains. -/
@[instance_reducible] def plane :
    ProjectivePlane (Point (TriangleGeometry.family d)) (Line (TriangleGeometry.family d)) :=
  projectivePlaneOfGeometry (TriangleGeometry.family d) (generate d h)
    (TriangleGeometry.uniqueGeodesicsBelow d hm) (TriangleGeometry.diameter_le_three d hm)
    (Nat.card k₁) Finite.one_lt_card (neighbor_card d h c₀ c₁ hn₀ hn₁ E₀)

/-- The literal infinity line in the quotient, in the original endpoint order. -/
def axis : Line (TriangleGeometry.family d) := ⟨base (TriangleGeometry.family d) true,rfl⟩

/-- The adjacent literal point, without exchanging the original endpoint marks. -/
def centerPoint : Point (TriangleGeometry.family d) := ⟨base (TriangleGeometry.family d) false,rfl⟩

/-- The plane order is the field of the chosen original natural core. -/
theorem plane_order :
    let := plane d h c₀ c₁ hn₀ hn₁ E₀ hm
    ProjectivePlane.order (Point (TriangleGeometry.family d)) (Line (TriangleGeometry.family d)) = Nat.card k₁ := by
  let := plane d h c₀ c₁ hn₀ hn₁ E₀ hm
  have hc : pointCount (Point (TriangleGeometry.family d)) (axis d) = Nat.card k₁ + 1 :=
    (Nat.card_congr (pointsOnLineEquivNeighbors (TriangleGeometry.family d) (axis d))).trans
      (neighbor_card d h c₀ c₁ hn₀ hn₁ E₀ (axis d).val)
  rw [ProjectivePlane.pointCount_eq] at hc
  omega

local instance pointAction : MulAction G (Point (TriangleGeometry.family d)) :=
  MulAction.compHom _ d.q
local instance lineAction : MulAction G (Line (TriangleGeometry.family d)) :=
  MulAction.compHom _ d.q
local instance collineationAction :
    IsCollineationAction G (Point (TriangleGeometry.family d)) (Line (TriangleGeometry.family d)) where
  smul_mem_smul_iff g p l := IsCollineationAction.smul_mem_smul_iff (d.q g) p l

include h in
private theorem fixes_neighbor_image (i : Bool) (z : G)
    (hz : z ∈ Q (family P) (base (family P) i))
    (v : Vertex (TriangleGeometry.family d))
    (hv : (graph (TriangleGeometry.family d)).Adj (base (TriangleGeometry.family d) i) v) :
    d.q z • v = v := by
  have hv' : (graph (TriangleGeometry.family d)).Adj ((cover d).hom (base (family P) i)) v := by
    change (graph (TriangleGeometry.family d)).Adj ((cover d).vertex (base (family P) i)) v
    rwa [(cover d).vertex_base]
  obtain ⟨w,hw⟩ := (cover d).neighbor_base_surjective i ⟨v,hv'⟩
  have hzw : z • w.val = w.val := (source_Z_Q_U h _).2 hz w.val
    ((mem_ball_one _ _ _).mpr (Or.inl w.property))
  have he := congrArg (cover d).vertex hzw
  rw [(cover d).vertex_smul] at he
  have hw' : (cover d).vertex w.val = v := congrArg Subtype.val hw
  rwa [hw'] at he

include h in
/-- The source intersection gives elations in the quotient plane, including movement.
The acting element is the original element, acting through the same quotient map. -/
theorem intersection_isElation (z : G)
    (hz : z ∈ Q (family P) (base (family P) true) ⊓ Q (family P) (base (family P) false))
    (hne : z ≠ 1) : IsElation z (centerPoint d) (axis d) := by
  refine ⟨⟨Bool.false_ne_true,CosetGeometry.incident_base _ _ _⟩,?_,?_,?_⟩
  · intro p hp
    apply Subtype.ext
    exact fixes_neighbor_image d h true z hz.1 p.val hp.symm
  · intro l hl
    apply Subtype.ext
    exact fixes_neighbor_image d h false z hz.2 l.val hl
  · have hzP : z ∈ family P true := by
      have hz' := Q_le_stabilizer (family P) (base (family P) true) hz.1
      simpa only [stabilizer, base, CosetGeometry.stabilizer_base] using hz'
    have hqne : d.q z ≠ 1 := by
      intro he
      have hh := (cover d).injective true (a₁ := ⟨z,hzP⟩) (a₂ := 1) (he.trans d.q.map_one.symm)
      exact hne (congrArg Subtype.val hh)
    have hmove : ∃ v : Vertex (TriangleGeometry.family d), d.q z • v ≠ v := by
      by_contra! hf
      exact hqne (faithfulSMul_iff.mp (faithful d h) _ hf)
    obtain ⟨⟨i,q⟩,hi⟩ := hmove
    cases i
    · exact Or.inl ⟨⟨⟨false,q⟩,rfl⟩,fun he => hi (congrArg Subtype.val he)⟩
    · exact Or.inr ⟨⟨⟨true,q⟩,rfl⟩,fun he => hi (congrArg Subtype.val he)⟩

/-- The original core fixes the quotient's original line vertex. -/
theorem core_fixes_axis (a : Q (family P) (base (family P) true)) :
    (a : G) • axis d = axis d := by
  apply Subtype.ext
  change d.q (a : G) • base (TriangleGeometry.family d) true = base (TriangleGeometry.family d) true
  have he := congrArg (cover d).vertex (Q_le_stabilizer (family P) (base (family P) true) a.property)
  simpa only [(cover d).vertex_smul,(cover d).vertex_base] using he

/-- The original actor fixes the quotient infinity line through d.q. -/
theorem actor_fixes_axis (a : c₁.actor) : (a : G) • axis d = axis d := by
  apply Subtype.ext
  change d.q (a : G) • base (TriangleGeometry.family d) true = base (TriangleGeometry.family d) true
  have hh := congrArg (cover d).vertex (c₁.actor_le a.property)
  simpa only [(cover d).vertex_smul,(cover d).vertex_base] using hh

include h hn₁ in
/-- Every infinity point is reached by the original actor, acting through the literal quotient. -/
theorem actor_transitive_on_axis (p : Point (TriangleGeometry.family d)) (hp : p ∈ axis d) :
    ∃ a : c₁.actor, (a : G) • centerPoint d = p := by
  have hp' : (graph (TriangleGeometry.family d)).Adj ((cover d).hom (base (family P) true)) p.val := by
    change (graph (TriangleGeometry.family d)).Adj ((cover d).vertex (base (family P) true)) p.val
    rw [(cover d).vertex_base]
    exact hp.symm
  obtain ⟨w,hw⟩ := (cover d).neighbor_base_surjective true ⟨p.val,hp'⟩
  obtain ⟨a,ha⟩ := base_actor_neighbor_transitive h true c₁ hn₁ w.val w.property
  refine ⟨a,Subtype.ext ?_⟩
  have he := congrArg (cover d).vertex ha
  rw [(cover d).vertex_smul,(cover d).vertex_base] at he
  exact he.trans (congrArg Subtype.val hw)

variable (hcenter : centerIn c₁.actor = ⊥)

include h c₀ c₁ E₁ hcenter in
/-- Every nonidentity element of the original natural core acts as an elation
of the quotient plane. This uses no perfectness or simplicity premise. -/
theorem core_isElation (x : Q (family P) (base (family P) true)) (hx : x ≠ 1) :
    ∃ C : Point (TriangleGeometry.family d), IsElation (x : G) C (axis d) := by
  have hcores := paired_cores_eq_centers_of_actions h c₀ c₁
  let I := Q (family P) (base (family P) true) ⊓ Q (family P) (base (family P) false)
  have hI : I ≠ ⊥ := by
    intro he
    have hc := core_intersection_card c₁ h hcores.2 hcenter E₁
    change Nat.card I = Nat.card k₁ at hc
    rw [he,Subgroup.card_bot] at hc
    exact (Finite.one_lt_card (α := k₁)).ne hc
  obtain ⟨z,hz,hz1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI)
  change z ≠ 1 at hz1
  let zQ : Q (family P) (base (family P) true) := ⟨z,hz.1⟩
  have hzQ : zQ ≠ 1 := fun he => hz1 (congrArg Subtype.val he)
  obtain ⟨a,ha⟩ := core_nonidentity_conjugate c₁ h hcores.2 hcenter E₁ zQ x hzQ hx
  have he := (intersection_isElation d h z hz hz1).conjugate (a : G)
  have haxis : (a : G) • axis d = axis d := by
    apply Subtype.ext
    change d.q (a : G) • base (TriangleGeometry.family d) true = base (TriangleGeometry.family d) true
    have hh := congrArg (cover d).vertex (c₁.actor_le a.property)
    simpa only [(cover d).vertex_smul,(cover d).vertex_base] using hh
  rw [show (a : G) * z * (a : G)⁻¹ = (x : G) from ha, haxis] at he
  exact ⟨(a : G) • centerPoint d,he⟩

/-- The original core, in the same single field, parametrizes every affine
point of the actual quotient plane. -/
def affineChart (o : {p : Point (TriangleGeometry.family d) // p ∉ axis d}) :
    (Fin 2 → k₁) ≃ {p : Point (TriangleGeometry.family d) // p ∉ axis d} := by
  let := plane d h c₀ c₁ hn₀ hn₁ E₀ hm
  have hcore := (paired_cores_eq_centers_of_actions h c₀ c₁).2
  exact translationChart (Q (family P) (base (family P) true)) (axis d)
    (core_fixes_axis d) o (core_isElation d h c₀ c₁ E₁ hcenter)
    (by rw [plane_order d h c₀ c₁ hn₀ hn₁ E₀ hm,core_card_of_natural c₁ h hcore E₁,
            hcenter,Subgroup.card_bot,mul_one])
    (coreCoordinates c₁ h hcore hcenter E₁)

/-- Literal evaluation through d.q; no ambient completion has been identified
with the finite quotient. -/
theorem affineChart_apply (o : {p : Point (TriangleGeometry.family d) // p ∉ axis d}) (t : Fin 2 → k₁) :
    (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o t).val =
      d.q ((coreCoordinates c₁ h (paired_cores_eq_centers_of_actions h c₀ c₁).2 hcenter E₁).symm
        (.ofAdd t) : G) • o.val := rfl

/-- Translation is addition in the one field, under the literal quotient action. -/
theorem affineChart_add (o : {p : Point (TriangleGeometry.family d) // p ∉ axis d})
    (a : Q (family P) (base (family P) true)) (t : Fin 2 → k₁) :
    (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
      ((coreCoordinates c₁ h (paired_cores_eq_centers_of_actions h c₀ c₁).2 hcenter E₁ a).toAdd + t)).val =
      d.q (a : G) • (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o t).val := by
  let := plane d h c₀ c₁ hn₀ hn₁ E₀ hm
  exact translationChart_add _ _ _ _ _ _ _ a t

section Coordinates
variable (o : {p : Point (TriangleGeometry.family d) // p ∉ axis d})
include h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter

/-- Evaluation as an action of the original source carrier. -/
theorem affineChart_source (t : Fin 2 → k₁) :
    (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o t).val =
      ((coreCoordinates c₁ h (paired_cores_eq_centers_of_actions h c₀ c₁).2 hcenter E₁).symm
        (.ofAdd t) : G) • o.val := rfl

/-- The affine points of a line in the marked pencil are exactly one orbit of the
actual adjacent-core intersection. -/
theorem core_orbit_mem_line_iff (m : Line (TriangleGeometry.family d))
    (hCm : centerPoint d ∈ m) (hom : o.val ∈ m)
    (x : Q (family P) (base (family P) true)) :
    (x : G) • o.val ∈ m ↔ (x : G) ∈ Q (family P) (base (family P) false) := by
  let := plane d h c₀ c₁ hn₀ hn₁ E₀ hm
  let A := Q (family P) (base (family P) true)
  let I := A ⊓ Q (family P) (base (family P) false)
  have hfix (z : I) : (z : G) • m = m := by
    apply Subtype.ext
    exact fixes_neighbor_image d h false z z.property.2 m.val hCm
  let f : I → {p : Point (TriangleGeometry.family d) // p ∈ m ∧ p ∉ axis d} := fun z =>
    ⟨(z : G) • o.val,
      (hfix z) ▸ (IsCollineationAction.smul_mem_smul_iff (z : G) o.val m).mpr hom,
      (affineOrbit A (axis d) (core_fixes_axis d) o ⟨z,z.property.1⟩).property⟩
  have hfree {a b : A} (he : (a : G) • o.val = (b : G) • o.val) : a = b :=
    affineOrbit_injective A (axis d) (core_fixes_axis d) o
      (core_isElation d h c₀ c₁ E₁ hcenter) (Subtype.ext he)
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    have he' : (⟨a,a.property.1⟩ : A) = (⟨b,b.property.1⟩ : A) :=
      hfree (congrArg (fun p => p.val) he)
    exact congrArg (fun z : A => (z : G)) he'
  have hml : m ≠ axis d := fun he => o.property (he ▸ hom)
  have hCl : centerPoint d ∈ axis d :=
    ⟨Bool.false_ne_true, Subgroup.CosetGeometry.incident_base _ false true⟩
  have hcard : Nat.card I = Nat.card {p : Point (TriangleGeometry.family d) // p ∈ m ∧ p ∉ axis d} := by
    rw [card_line_off_axis (axis d) m (centerPoint d) hCl hCm hml, plane_order d h c₀ c₁ hn₀ hn₁ E₀ hm]
    exact core_intersection_card c₁ h (paired_cores_eq_centers_of_actions h c₀ c₁).2 hcenter E₁
  have honto := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj,hcard⟩).2
  constructor
  · intro hx
    obtain ⟨z,hz⟩ := honto ⟨(x : G) • o.val, hx,
      (affineOrbit A (axis d) (core_fixes_axis d) o x).property⟩
    have he : (⟨z,z.property.1⟩ : A) = x := hfree (congrArg Subtype.val hz)
    exact (congrArg Subtype.val he) ▸ z.property.2
  · intro hx
    have he := hfix (⟨x,x.property,hx⟩ : I)
    exact he ▸ (IsCollineationAction.smul_mem_smul_iff (x : G) o.val m).mpr hom

/-- Incidence in the marked pencil is exactly the fixed-line equation over the one chosen field. -/
theorem affineChart_mem_line_iff (m : Line (TriangleGeometry.family d))
    (hCm : centerPoint d ∈ m) (hom : o.val ∈ m) (t : Fin 2 → k₁) :
    (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o t).val ∈ m ↔
      ∀ s ∈ (c₁.imageSylow : Subgroup SL(2,k₁)), Matrix.mulVec s.val t = t := by
  rw [affineChart_source,
    core_orbit_mem_line_iff d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o m hCm hom,
    coreCoordinates_mem_neighbor_iff c₁ h (paired_cores_eq_centers_of_actions h c₀ c₁).2 hcenter E₁]
  simp only [MulEquiv.apply_symm_apply]
  rfl

/-- Transport an affine origin by the actual local actor. -/
def actorAffineOrigin (a : c₁.actor) : {p : Point (TriangleGeometry.family d) // p ∉ axis d} :=
  ⟨(a : G) • o.val, by
    intro hp
    have haxis : (a : G) • axis d = axis d := actor_fixes_axis d c₁ a
    exact o.property ((IsCollineationAction.smul_mem_smul_iff (a : G) o.val
      (axis d)).mp (haxis.symm ▸ hp))⟩

/-- The same marked quotient matrices act linearly when the affine origin is transported. -/
theorem affineChart_actor (a : c₁.actor) (t : Fin 2 → k₁) :
    (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter (actorAffineOrigin d c₁ o a)
      (Matrix.mulVec (c₁.quotient a).val t)).val =
      (a : G) • (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o t).val := by
  let φ := coreCoordinates c₁ h (paired_cores_eq_centers_of_actions h c₀ c₁).2 hcenter E₁
  let x := φ.symm (.ofAdd t)
  obtain ⟨y,hy,hφ⟩ := coreCoordinates_conjugate c₁ h (paired_cores_eq_centers_of_actions h c₀ c₁).2 hcenter E₁ a x
  have hφ' : φ y = .ofAdd (Matrix.mulVec (c₁.quotient a).val t) := by
    apply Multiplicative.toAdd.injective
    simpa only [x, φ, MulEquiv.apply_symm_apply, toAdd_ofAdd] using hφ
  have he : φ.symm (.ofAdd (Matrix.mulVec (c₁.quotient a).val t)) = y :=
    (congrArg φ.symm hφ').symm.trans (φ.symm_apply_apply y)
  change (φ.symm (.ofAdd (Matrix.mulVec (c₁.quotient a).val t)) : G) • ((a : G) • o.val) =
    (a : G) • ((x : G) • o.val)
  rw [he,hy]
  simp only [mul_smul,inv_smul_smul]

/-- Every actor-transported pencil uses the transported fixed line over this same field. -/
theorem affineChart_mem_actor_line_iff (a : c₁.actor) (m : Line (TriangleGeometry.family d))
    (hCm : (a : G) • centerPoint d ∈ m) (hom : o.val ∈ m) (t : Fin 2 → k₁) :
    (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
      (Matrix.mulVec (c₁.quotient a).val t)).val ∈ m ↔
      ∀ s ∈ (c₁.imageSylow : Subgroup SL(2,k₁)), Matrix.mulVec s.val t = t := by
  let o' := actorAffineOrigin d c₁ o a⁻¹
  have ho' : actorAffineOrigin d c₁ o' a = o := Subtype.ext (smul_inv_smul (a : G) o.val)
  have hCm' : centerPoint d ∈ (a : G)⁻¹ • m := by
    simpa only [inv_smul_smul] using
      (IsCollineationAction.smul_mem_smul_iff (a : G)⁻¹ ((a : G) • centerPoint d) m).mpr hCm
  have hom' : o'.val ∈ (a : G)⁻¹ • m :=
    (IsCollineationAction.smul_mem_smul_iff (a : G)⁻¹ o.val m).mpr hom
  rw [← ho',affineChart_actor]
  have hi := IsCollineationAction.smul_mem_smul_iff (a : G)
    (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o' t).val ((a : G)⁻¹ • m)
  rw [smul_inv_smul] at hi
  exact hi.trans (affineChart_mem_line_iff d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o' _ hCm' hom' t)

/-- Every line through the affine origin has a direction obtained from this one
Sylow fixed line by the original marked actor, without comparing two fields. -/
theorem affineChart_all_directions
    (m : Line (TriangleGeometry.family d)) (hom : o.val ∈ m) :
    ∃ a : c₁.actor, ∀ t : Fin 2 → k₁,
      (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
        (Matrix.mulVec (c₁.quotient a).val t)).val ∈ m ↔
      ∀ s ∈ (c₁.imageSylow : Subgroup SL(2,k₁)), Matrix.mulVec s.val t = t := by
  let := plane d h c₀ c₁ hn₀ hn₁ E₀ hm
  have hml : m ≠ axis d := fun he => o.property (he ▸ hom)
  let C : Point (TriangleGeometry.family d) := HasPoints.mkPoint hml
  have hCm : C ∈ m := (HasPoints.mkPoint_ax hml).1
  have hCl : C ∈ axis d := (HasPoints.mkPoint_ax hml).2
  obtain ⟨a,haC⟩ := actor_transitive_on_axis d h c₁ hn₁ C hCl
  exact ⟨a,fun t => affineChart_mem_actor_line_iff d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
    a m (haC.symm ▸ hCm) hom t⟩

/-- Changing the affine origin is translation by its coordinates in the same chart. -/
theorem affineChart_change_origin (b t : Fin 2 → k₁) :
    (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter
      (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o b) t).val =
      (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o (t + b)).val := by
  let φ := coreCoordinates c₁ h (paired_cores_eq_centers_of_actions h c₀ c₁).2 hcenter E₁
  change (φ.symm (.ofAdd t) : G) • ((φ.symm (.ofAdd b) : G) • o.val) =
    (φ.symm (.ofAdd t * .ofAdd b) : G) • o.val
  rw [map_mul, Subgroup.coe_mul, mul_smul]

/-- All affine lines, not just the marked pencil, are cosets of the transported
fixed line in the single field chart. -/
theorem affineChart_all_affine_lines
    (m : Line (TriangleGeometry.family d)) (hml : m ≠ axis d) :
    ∃ b : Fin 2 → k₁, ∃ a : c₁.actor, ∀ t : Fin 2 → k₁,
      (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
        (Matrix.mulVec (c₁.quotient a).val t + b)).val ∈ m ↔
      ∀ s ∈ (c₁.imageSylow : Subgroup SL(2,k₁)), Matrix.mulVec s.val t = t := by
  let := plane d h c₀ c₁ hn₀ hn₁ E₀ hm
  let C : Point (TriangleGeometry.family d) := HasPoints.mkPoint hml
  have hCm : C ∈ m := (HasPoints.mkPoint_ax hml).1
  have hCl : C ∈ axis d := (HasPoints.mkPoint_ax hml).2
  have hpos : 0 < Nat.card {p : Point (TriangleGeometry.family d) // p ∈ m ∧ p ∉ axis d} := by
    rw [card_line_off_axis (axis d) m C hCl hCm hml, plane_order d h c₀ c₁ hn₀ hn₁ E₀ hm]
    exact Nat.card_pos
  obtain ⟨p⟩ := (Nat.card_pos_iff.mp hpos).1
  let p' : {p : Point (TriangleGeometry.family d) // p ∉ axis d} := ⟨p,p.property.2⟩
  let b := (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).symm p'
  have hb : affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o b = p' :=
    Equiv.apply_symm_apply _ _
  obtain ⟨a,ha⟩ := affineChart_all_directions d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter p' m p.property.1
  refine ⟨b,a,?_⟩
  intro t
  rw [← affineChart_change_origin, hb]
  exact ha t

/-- The incidence equations are ordinary affine field lines: one nonzero field
vector parametrizes the fixed direction, and the same source actors give all directions. -/
theorem affineChart_field_lines :
    ∃ v₀ : Fin 2 → k₁, v₀ ≠ 0 ∧ ∀ m : Line (TriangleGeometry.family d), m ≠ axis d →
      ∃ b : Fin 2 → k₁, ∃ a : c₁.actor, ∀ t : Fin 2 → k₁,
        (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
          (Matrix.mulVec (c₁.quotient a).val t + b)).val ∈ m ↔
          ∃ r : k₁, t = r • v₀ := by
  obtain ⟨v₀,hv₀,hv⟩ := exists_neighbor_fixed_line c₁ h (paired_cores_eq_centers_of_actions h c₀ c₁).2 hcenter E₁
  refine ⟨v₀,hv₀,?_⟩
  intro m hml
  obtain ⟨b,a,ha⟩ := affineChart_all_affine_lines d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o m hml
  exact ⟨b,a,fun t => (ha t).trans (hv t)⟩

/-- Every actual affine line has the ordinary field-line equation in the one chart. -/
theorem affineChart_line_equation
    (m : Line (TriangleGeometry.family d)) (hml : m ≠ axis d) :
    ∃ b e : Fin 2 → k₁, e ≠ 0 ∧ ∀ t : Fin 2 → k₁,
      (affineChart d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o t).val ∈ m ↔
        ∃ r : k₁, t = b + r • e := by
  obtain ⟨v₀,hv₀,hv⟩ := affineChart_field_lines d h c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
  obtain ⟨b,a,ha⟩ := hv m hml
  let A := c₁.quotient a
  let d := Matrix.mulVec A.val v₀
  have hd : d ≠ 0 := by
    intro hd
    apply hv₀
    have hh := congrArg (fun t : Fin 2 → k₁ => A⁻¹ • t) hd
    change A⁻¹ • (A • v₀) = A⁻¹ • (0 : Fin 2 → k₁) at hh
    simpa only [inv_smul_smul, smul_zero] using hh
  refine ⟨b,d,hd,?_⟩
  intro t
  let u : Fin 2 → k₁ := A⁻¹ • (t-b)
  have hu : Matrix.mulVec A.val u = t-b := smul_inv_smul A (t-b)
  have hut : Matrix.mulVec A.val u + b = t := (congrArg (· + b) hu).trans (sub_add_cancel t b)
  rw [← hut,ha]
  constructor
  · rintro ⟨r,hr⟩
    exact ⟨r,by rw [hr, Matrix.mulVec_smul]; exact add_comm _ _⟩
  · rintro ⟨r,hr⟩
    refine ⟨r,?_⟩
    apply (MulAction.injective A)
    change Matrix.mulVec A.val u = Matrix.mulVec A.val (r • v₀)
    rw [Matrix.mulVec_smul]
    exact add_right_cancel (hr.trans (add_comm b (r • d)))

end Coordinates

end QuotientPlane
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
