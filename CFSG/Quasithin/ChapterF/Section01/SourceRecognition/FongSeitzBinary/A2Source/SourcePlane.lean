module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.NaturalCore
public import Theory.Combinatorics.TranslationPlane.Coordinates
public import Theory.GroupAction.RankTwoCosetGeometry.ProjectivePlane
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneNeighbors

/-!
# One-field affine incidence coordinates from the actual source core

The intersection of adjacent source cores fixes the axis and center pencil.
Faithfulness supplies movement, so its nonidentity elements are elations.
Natural-core conjugacy makes every nonidentity element of the axis core an
elation. The elation fixed-point theorem and the source core order give a
regular action on affine points and hence one field chart.

The adjacent-core intersection acts regularly on an affine pencil line.
The same marked actor transports this fixed line to all directions, and
changing the origin gives every affine line as a field-line coset. All
formulas retain the original actions and the one original quotient matrix.

The plane instance and its order are explicit intermediate geometry inputs;
TriangleCoordinates constructs them from short-path geometry. Transporting
that geometry and the natural actor to the finite m=3 quotient, and the
six-root recognition, remain obligations of this A2 family.
Source: DGS, Groups and Graphs, 10.5 and Theorem D, printed pp.156,224.
-/

@[expose] public noncomputable section
open Subgroup Configuration
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]
  {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local instance : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- The literal line vertex, used as the line at infinity. -/
def sourceAxis (P : Fin 2 → Subgroup G) : Line (family P) :=
  ⟨base (family P) true,rfl⟩

/-- Its adjacent original point vertex. -/
def sourceCenter (P : Fin 2 → Subgroup G) : Point (family P) :=
  ⟨base (family P) false,rfl⟩

variable (h : LocallyRankOneTriple P B)
  (c : BOneActionData (family P) (base (family P) true) (base (family P) false) k W)
  (hcore : Q (family P) (base (family P) true) = Z (family P) (base (family P) true))
  (hcenter : centerIn c.actor = ⊥)
  (E : W ≃ₗ[ZMod 2] (Fin 2 → k))

include h in
omit [Finite G] in
/-- Membership in both actual cores supplies a genuine elation, including movement. -/
theorem intersection_isElation (z : G)
    (hz : z ∈ Q (family P) (base (family P) true) ⊓
      Q (family P) (base (family P) false)) (hne : z ≠ 1) :
    IsElation z (sourceCenter P) (sourceAxis P) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact ⟨Bool.false_ne_true, Subgroup.CosetGeometry.incident_base _ false true⟩
  · intro p hp
    apply Subtype.ext
    exact (source_Z_Q_U h _).2 hz.1 p.val
      ((mem_ball_one _ _ _).mpr (Or.inl hp.symm))
  · intro m hm
    apply Subtype.ext
    exact (source_Z_Q_U h _).2 hz.2 m.val
      ((mem_ball_one _ _ _).mpr (Or.inl hm))
  · have hmove : ∃ t : Vertex (family P), z • t ≠ t := by
      by_contra! hf
      exact hne (faithfulSMul_iff.mp (faithful_graph h) z hf)
    obtain ⟨⟨i,q⟩,ht⟩ := hmove
    cases i
    · exact Or.inl ⟨⟨⟨false,q⟩,rfl⟩,fun he => ht (congrArg Subtype.val he)⟩
    · exact Or.inr ⟨⟨⟨true,q⟩,rfl⟩,fun he => ht (congrArg Subtype.val he)⟩

include h c hcore hcenter E in
omit [Finite G] in
/-- Every nonidentity element of the one natural core is an elation on the same axis. -/
theorem core_isElation (x : Q (family P) (base (family P) true)) (hx : x ≠ 1) :
    ∃ C : Point (family P), IsElation (x : G) C (sourceAxis P) := by
  let I := Q (family P) (base (family P) true) ⊓ Q (family P) (base (family P) false)
  have hI : I ≠ ⊥ := by
    intro he
    have hc := core_intersection_card c h hcore hcenter E
    change Nat.card I = Nat.card k at hc
    rw [he, Subgroup.card_bot] at hc
    exact (Finite.one_lt_card (α := k)).ne hc
  obtain ⟨z,hz,hz1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI)
  change z ≠ 1 at hz1
  let zQ : Q (family P) (base (family P) true) := ⟨z,hz.1⟩
  have hzQ : zQ ≠ 1 := fun he => hz1 (congrArg Subtype.val he)
  obtain ⟨a,ha⟩ := core_nonidentity_conjugate c h hcore hcenter E zQ x hzQ hx
  have he := (intersection_isElation h z hz hz1).conjugate (a : G)
  have haxis : (a : G) • sourceAxis P = sourceAxis P :=
    Subtype.ext (c.actor_le a.property)
  rw [show (a : G) * z * (a : G)⁻¹ = (x : G) from ha, haxis] at he
  exact ⟨(a : G) • sourceCenter P,he⟩

omit [Finite G] in
/-- The core fixes its actual line vertex. -/
theorem core_fixes_axis (a : Q (family P) (base (family P) true)) :
    (a : G) • sourceAxis P = sourceAxis P :=
  Subtype.ext (Q_le_stabilizer _ _ a.property)

variable [ProjectivePlane (Point (family P)) (Line (family P))]
  (horder : ProjectivePlane.order (Point (family P)) (Line (family P)) = Nat.card k)
  (o : {p : Point (family P) // p ∉ sourceAxis P})

/-- The actual natural core acts regularly on all affine points; no perfect local factor is used. -/
def sourceAffineChart : (Fin 2 → k) ≃ {p : Point (family P) // p ∉ sourceAxis P} :=
  translationChart (Q (family P) (base (family P) true)) (sourceAxis P)
    core_fixes_axis o (core_isElation h c hcore hcenter E)
    (by
      rw [horder, core_card_of_natural c h hcore E, hcenter, Subgroup.card_bot, mul_one])
    (coreCoordinates c h hcore hcenter E)

/-- The chart uses the original action and the single chosen core parametrization. -/
theorem sourceAffineChart_apply (t : Fin 2 → k) :
    (sourceAffineChart h c hcore hcenter E horder o t).val =
      ((coreCoordinates c h hcore hcenter E).symm (.ofAdd t) : G) • o.val := rfl

/-- The original core acts by literal vector addition in these coordinates. -/
theorem sourceAffineChart_add (a : Q (family P) (base (family P) true)) (t : Fin 2 → k) :
    (sourceAffineChart h c hcore hcenter E horder o
      ((coreCoordinates c h hcore hcenter E a).toAdd + t)).val =
      (a : G) • (sourceAffineChart h c hcore hcenter E horder o t).val :=
  translationChart_add _ _ _ _ _ _ _ a t

include h c hcore hcenter E horder in
/-- The affine points of a line in the marked pencil are exactly one orbit of the
actual adjacent-core intersection. -/
theorem core_orbit_mem_line_iff (m : Line (family P))
    (hCm : sourceCenter P ∈ m) (hom : o.val ∈ m)
    (x : Q (family P) (base (family P) true)) :
    (x : G) • o.val ∈ m ↔ (x : G) ∈ Q (family P) (base (family P) false) := by
  let A := Q (family P) (base (family P) true)
  let I := A ⊓ Q (family P) (base (family P) false)
  have hfix (z : I) : (z : G) • m = m := by
    apply Subtype.ext
    exact (source_Z_Q_U h _).2 z.property.2 m.val
      ((mem_ball_one _ _ _).mpr (Or.inl hCm))
  let f : I → {p : Point (family P) // p ∈ m ∧ p ∉ sourceAxis P} := fun z =>
    ⟨(z : G) • o.val,
      (hfix z) ▸ (IsCollineationAction.smul_mem_smul_iff (z : G) o.val m).mpr hom,
      (affineOrbit A (sourceAxis P) core_fixes_axis o ⟨z,z.property.1⟩).property⟩
  have hfree {a b : A} (he : (a : G) • o.val = (b : G) • o.val) : a = b :=
    affineOrbit_injective A (sourceAxis P) core_fixes_axis o
      (core_isElation h c hcore hcenter E) (Subtype.ext he)
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    have he' : (⟨a,a.property.1⟩ : A) = (⟨b,b.property.1⟩ : A) :=
      hfree (congrArg (fun p => p.val) he)
    exact congrArg (fun z : A => (z : G)) he'
  have hml : m ≠ sourceAxis P := fun he => o.property (he ▸ hom)
  have hCl : sourceCenter P ∈ sourceAxis P :=
    ⟨Bool.false_ne_true, Subgroup.CosetGeometry.incident_base _ false true⟩
  have hcard : Nat.card I = Nat.card {p : Point (family P) // p ∈ m ∧ p ∉ sourceAxis P} := by
    rw [card_line_off_axis (sourceAxis P) m (sourceCenter P) hCl hCm hml, horder]
    exact core_intersection_card c h hcore hcenter E
  have honto := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj,hcard⟩).2
  constructor
  · intro hx
    obtain ⟨z,hz⟩ := honto ⟨(x : G) • o.val, hx,
      (affineOrbit A (sourceAxis P) core_fixes_axis o x).property⟩
    have he : (⟨z,z.property.1⟩ : A) = x := hfree (congrArg Subtype.val hz)
    exact (congrArg Subtype.val he) ▸ z.property.2
  · intro hx
    have he := hfix (⟨x,x.property,hx⟩ : I)
    exact he ▸ (IsCollineationAction.smul_mem_smul_iff (x : G) o.val m).mpr hom

/-- Incidence in the marked pencil is exactly the fixed-line equation over the one chosen field. -/
theorem sourceAffineChart_mem_line_iff (m : Line (family P))
    (hCm : sourceCenter P ∈ m) (hom : o.val ∈ m) (t : Fin 2 → k) :
    (sourceAffineChart h c hcore hcenter E horder o t).val ∈ m ↔
      ∀ s ∈ (c.imageSylow : Subgroup SL(2,k)), Matrix.mulVec s.val t = t := by
  rw [sourceAffineChart_apply,
    core_orbit_mem_line_iff h c hcore hcenter E horder o m hCm hom,
    coreCoordinates_mem_neighbor_iff c h hcore hcenter E]
  simp only [MulEquiv.apply_symm_apply]
  rfl

/-- Transport an affine origin by the actual local actor. -/
def actorAffineOrigin (a : c.actor) : {p : Point (family P) // p ∉ sourceAxis P} :=
  ⟨(a : G) • o.val, by
    intro hp
    have haxis : (a : G) • sourceAxis P = sourceAxis P := Subtype.ext (c.actor_le a.property)
    exact o.property ((IsCollineationAction.smul_mem_smul_iff (a : G) o.val
      (sourceAxis P)).mp (haxis.symm ▸ hp))⟩

/-- The same marked quotient matrices act linearly when the affine origin is transported. -/
theorem sourceAffineChart_actor (a : c.actor) (t : Fin 2 → k) :
    (sourceAffineChart h c hcore hcenter E horder (actorAffineOrigin c o a)
      (Matrix.mulVec (c.quotient a).val t)).val =
      (a : G) • (sourceAffineChart h c hcore hcenter E horder o t).val := by
  let φ := coreCoordinates c h hcore hcenter E
  let x := φ.symm (.ofAdd t)
  obtain ⟨y,hy,hφ⟩ := coreCoordinates_conjugate c h hcore hcenter E a x
  have hφ' : φ y = .ofAdd (Matrix.mulVec (c.quotient a).val t) := by
    apply Multiplicative.toAdd.injective
    simpa only [x, φ, MulEquiv.apply_symm_apply, toAdd_ofAdd] using hφ
  have he : φ.symm (.ofAdd (Matrix.mulVec (c.quotient a).val t)) = y :=
    (congrArg φ.symm hφ').symm.trans (φ.symm_apply_apply y)
  change (φ.symm (.ofAdd (Matrix.mulVec (c.quotient a).val t)) : G) • ((a : G) • o.val) =
    (a : G) • ((x : G) • o.val)
  rw [he,hy]
  simp only [mul_smul,inv_smul_smul]

/-- Every actor-transported pencil uses the transported fixed line over this same field. -/
theorem sourceAffineChart_mem_actor_line_iff (a : c.actor) (m : Line (family P))
    (hCm : (a : G) • sourceCenter P ∈ m) (hom : o.val ∈ m) (t : Fin 2 → k) :
    (sourceAffineChart h c hcore hcenter E horder o
      (Matrix.mulVec (c.quotient a).val t)).val ∈ m ↔
      ∀ s ∈ (c.imageSylow : Subgroup SL(2,k)), Matrix.mulVec s.val t = t := by
  let o' := actorAffineOrigin c o a⁻¹
  have ho' : actorAffineOrigin c o' a = o := Subtype.ext (smul_inv_smul (a : G) o.val)
  have hCm' : sourceCenter P ∈ (a : G)⁻¹ • m := by
    simpa only [inv_smul_smul] using
      (IsCollineationAction.smul_mem_smul_iff (a : G)⁻¹ ((a : G) • sourceCenter P) m).mpr hCm
  have hom' : o'.val ∈ (a : G)⁻¹ • m :=
    (IsCollineationAction.smul_mem_smul_iff (a : G)⁻¹ o.val m).mpr hom
  rw [← ho',sourceAffineChart_actor]
  have hi := IsCollineationAction.smul_mem_smul_iff (a : G)
    (sourceAffineChart h c hcore hcenter E horder o' t).val ((a : G)⁻¹ • m)
  rw [smul_inv_smul] at hi
  exact hi.trans (sourceAffineChart_mem_line_iff h c hcore hcenter E horder o' _ hCm' hom' t)

/-- Every line through the affine origin has a direction obtained from this one
Sylow fixed line by the original marked actor, without comparing two fields. -/
theorem sourceAffineChart_all_directions
    (hn : B ≤ normalizer (c.actor : Set G)) (m : Line (family P)) (hom : o.val ∈ m) :
    ∃ a : c.actor, ∀ t : Fin 2 → k,
      (sourceAffineChart h c hcore hcenter E horder o
        (Matrix.mulVec (c.quotient a).val t)).val ∈ m ↔
      ∀ s ∈ (c.imageSylow : Subgroup SL(2,k)), Matrix.mulVec s.val t = t := by
  have hml : m ≠ sourceAxis P := fun he => o.property (he ▸ hom)
  let C : Point (family P) := HasPoints.mkPoint hml
  have hCm : C ∈ m := (HasPoints.mkPoint_ax hml).1
  have hCl : C ∈ sourceAxis P := (HasPoints.mkPoint_ax hml).2
  obtain ⟨a,ha⟩ := base_actor_neighbor_transitive h true c hn C.val hCl.symm
  have haC : (a : G) • sourceCenter P = C := Subtype.ext ha
  exact ⟨a,fun t => sourceAffineChart_mem_actor_line_iff h c hcore hcenter E horder o
    a m (haC.symm ▸ hCm) hom t⟩

/-- Changing the affine origin is translation by its coordinates in the same chart. -/
theorem sourceAffineChart_change_origin (b t : Fin 2 → k) :
    (sourceAffineChart h c hcore hcenter E horder
      (sourceAffineChart h c hcore hcenter E horder o b) t).val =
      (sourceAffineChart h c hcore hcenter E horder o (t + b)).val := by
  let φ := coreCoordinates c h hcore hcenter E
  change (φ.symm (.ofAdd t) : G) • ((φ.symm (.ofAdd b) : G) • o.val) =
    (φ.symm (.ofAdd t * .ofAdd b) : G) • o.val
  rw [map_mul, Subgroup.coe_mul, mul_smul]

/-- All affine lines, not just the marked pencil, are cosets of the transported
fixed line in the single field chart. -/
theorem sourceAffineChart_all_affine_lines
    (hn : B ≤ normalizer (c.actor : Set G)) (m : Line (family P)) (hml : m ≠ sourceAxis P) :
    ∃ b : Fin 2 → k, ∃ a : c.actor, ∀ t : Fin 2 → k,
      (sourceAffineChart h c hcore hcenter E horder o
        (Matrix.mulVec (c.quotient a).val t + b)).val ∈ m ↔
      ∀ s ∈ (c.imageSylow : Subgroup SL(2,k)), Matrix.mulVec s.val t = t := by
  let C : Point (family P) := HasPoints.mkPoint hml
  have hCm : C ∈ m := (HasPoints.mkPoint_ax hml).1
  have hCl : C ∈ sourceAxis P := (HasPoints.mkPoint_ax hml).2
  have hpos : 0 < Nat.card {p : Point (family P) // p ∈ m ∧ p ∉ sourceAxis P} := by
    rw [card_line_off_axis (sourceAxis P) m C hCl hCm hml, horder]
    exact Nat.card_pos
  obtain ⟨p⟩ := (Nat.card_pos_iff.mp hpos).1
  let p' : {p : Point (family P) // p ∉ sourceAxis P} := ⟨p,p.property.2⟩
  let b := (sourceAffineChart h c hcore hcenter E horder o).symm p'
  have hb : sourceAffineChart h c hcore hcenter E horder o b = p' :=
    Equiv.apply_symm_apply _ _
  obtain ⟨a,ha⟩ := sourceAffineChart_all_directions h c hcore hcenter E horder p' hn m p.property.1
  refine ⟨b,a,?_⟩
  intro t
  rw [← sourceAffineChart_change_origin, hb]
  exact ha t

/-- The incidence equations are ordinary affine field lines: one nonzero field
vector parametrizes the fixed direction, and the same source actors give all directions. -/
theorem sourceAffineChart_field_lines
    (hn : B ≤ normalizer (c.actor : Set G)) :
    ∃ v₀ : Fin 2 → k, v₀ ≠ 0 ∧ ∀ m : Line (family P), m ≠ sourceAxis P →
      ∃ b : Fin 2 → k, ∃ a : c.actor, ∀ t : Fin 2 → k,
        (sourceAffineChart h c hcore hcenter E horder o
          (Matrix.mulVec (c.quotient a).val t + b)).val ∈ m ↔
          ∃ r : k, t = r • v₀ := by
  obtain ⟨v₀,hv₀,hv⟩ := exists_neighbor_fixed_line c h hcore hcenter E
  refine ⟨v₀,hv₀,?_⟩
  intro m hm
  obtain ⟨b,a,ha⟩ := sourceAffineChart_all_affine_lines h c hcore hcenter E horder o hn m hm
  exact ⟨b,a,fun t => (ha t).trans (hv t)⟩

/-- Every actual affine line has the ordinary field-line equation in the one chart. -/
theorem sourceAffineChart_line_equation
    (hn : B ≤ normalizer (c.actor : Set G)) (m : Line (family P)) (hm : m ≠ sourceAxis P) :
    ∃ b d : Fin 2 → k, d ≠ 0 ∧ ∀ t : Fin 2 → k,
      (sourceAffineChart h c hcore hcenter E horder o t).val ∈ m ↔
        ∃ r : k, t = b + r • d := by
  obtain ⟨v₀,hv₀,hv⟩ := sourceAffineChart_field_lines h c hcore hcenter E horder o hn
  obtain ⟨b,a,ha⟩ := hv m hm
  let A := c.quotient a
  let d := Matrix.mulVec A.val v₀
  have hd : d ≠ 0 := by
    intro hd
    apply hv₀
    have hh := congrArg (fun t : Fin 2 → k => A⁻¹ • t) hd
    change A⁻¹ • (A • v₀) = A⁻¹ • (0 : Fin 2 → k) at hh
    simpa only [inv_smul_smul, smul_zero] using hh
  refine ⟨b,d,hd,?_⟩
  intro t
  let u : Fin 2 → k := A⁻¹ • (t-b)
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

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
