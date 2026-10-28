module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.MarkedPlane

/-!
# Affine line equations through the independent amalgam marking

The original actor is transitive on the independently marked infinity line:
its endpoint map carries the full original overlap into the target Borel.
The shared original core acts freely on each marked-pencil affine line;
its order q proves that this orbit fills that line. Original natural
coordinates identify it with the fixed field line of the SAME SL₂ Sylow.
Actor transport supplies every direction and translation supplies every
ordinary affine field-line equation.

All actor, field and core parameters retain their original marking. No
ambient descent map, model isomorphism or perfect-factor hypothesis is
used. The projective-coordinate consumer uses affineChart_line_equation.
Source: DGS, Groups and Graphs, 10.5 and Theorem D, printed pp.156,224.
-/

@[expose] public noncomputable section
open Subgroup Configuration Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source.MarkedPlane
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open MarkedCoreTransport
variable {G X : Type*} [Group G] [Group X] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    d.standardAmalgam)
  (h : HypothesisF11 L S)

variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance markedAffineFieldAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
variable
  (c₀ : BOneActionData (fullFamily L S) (base (fullFamily L S) false)
    (base (fullFamily L S) true) k₀ W₀)
  (c₁ : BOneActionData (fullFamily L S) (base (fullFamily L S) true)
    (base (fullFamily L S) false) k₁ W₁)
  (hn₀ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₀.actor : Set (generated L S)))
  (hn₁ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₁.actor : Set (generated L S)))
  (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))

variable (hm : RootCoordinates.rotationOrder d = 3) (split : SplitData d.tits)
  (hcenter : centerIn c₁.actor = ⊥)
  (o : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d})
local notation "chart" => affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter

/-- The full right endpoint carries the whole original overlap into the actual Borel. -/
theorem endpoint_overlap_mem_borel
    (a : stabilizer (fullFamily L S) (base (fullFamily L S) true))
    (ha : (a : generated L S) ∈ fullFamily L S false) :
    (endpointMarking d mark true a : X ⧸ d.D) ∈ d.tits.B := by
  let b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G) :=
    ⟨(a : generated L S),ha,(original_stabilizer (L := L) (S := S) true).le a.property⟩
  rw [endpointMarking_right]
  have he := congrArg Subtype.val (mark.right_commutes b)
  rw [RootCoordinates.standardAmalgam_right_eq_inclusion] at he
  change (mark.right ⟨(a : generated L S),_⟩ : X ⧸ d.D) = (mark.middle b : X ⧸ d.D) at he
  rw [he]
  exact (mark.middle b).property

include h hn₁ in
/-- The SAME original natural actor reaches all infinity points in the independent quotient. -/
theorem actor_transitive_on_axis (p : Point (TriangleGeometry.family d)) (hp : p ∈ QuotientPlane.axis d) :
    ∃ a : c₁.actor,
      actorMap c₁ _ (endpointMarking d mark true) a • QuotientPlane.centerPoint d = p := by
  let F := TriangleGeometry.family d
  let F₀ := fullFamily L S
  obtain ⟨g,hg,hgp⟩ := neighbor_base_rep F true hp.symm
  obtain ⟨b,hb⟩ := (endpointMarking d mark true).surjective ⟨g,hg⟩
  have hbadj : (graph F₀).Adj (base F₀ true) ((b : generated L S) • base F₀ false) := by
    have hh := (CosetGeometry.translationGraphIso F₀ (b : generated L S)).map_adj_iff.mpr
      (show (graph F₀).Adj (base F₀ true) (base F₀ false) from
        ⟨by change true ≠ false; decide,CosetGeometry.incident_base _ _ _⟩)
    change (graph F₀).Adj ((b : generated L S) • base F₀ true) ((b : generated L S) • base F₀ false) at hh
    rw [b.property] at hh
    exact hh
  obtain ⟨a,ha⟩ := base_actor_neighbor_transitive h.generatedLocallyRankOneTriple true c₁ hn₁ _ hbadj
  let u : stabilizer F₀ (base F₀ true) := ⟨a,c₁.actor_le a.property⟩
  have hab : ((u⁻¹*b : stabilizer F₀ (base F₀ true)) : generated L S) ∈ F₀ false :=
    (Theory.AlgebraicGroup.TitsSystem.DihedralGeometry.smul_base_eq_iff F₀ (a : generated L S) b false).mp ha
  have hB := endpoint_overlap_mem_borel d mark (u⁻¹*b) hab
  have hJ : (actorMap c₁ _ (endpointMarking d mark true) a)⁻¹ * g ∈ F false := by
    have hh := (d.tits.B_le_standardParabolic {d.simple 0}) hB
    rw [map_mul,map_inv] at hh
    rw [hb] at hh
    exact hh
  have he := (Theory.AlgebraicGroup.TitsSystem.DihedralGeometry.smul_base_eq_iff F
    (actorMap c₁ _ (endpointMarking d mark true) a) g false).mpr hJ
  refine ⟨a,Subtype.ext ?_⟩
  apply he.trans
  change CosetGeometry.Vertex.mk false (g • ((1 : X ⧸ d.D) : (X ⧸ d.D) ⧸ F false)) = _
  change CosetGeometry.Vertex.mk false ((g : X ⧸ d.D) : (X ⧸ d.D) ⧸ F false) = p.val at hgp
  simpa only [MulAction.Quotient.smul_mk,smul_eq_mul,mul_one] using hgp

include h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter in
/-- The affine points on a marked-pencil line are exactly the original shared-core orbit. -/
theorem core_orbit_mem_line_iff (m : Line (TriangleGeometry.family d))
    (hCm : QuotientPlane.centerPoint d ∈ m) (hom : o.val ∈ m)
    (x : Q (fullFamily L S) (base (fullFamily L S) true)) :
    (originalCoreEquiv d mark true x : X ⧸ d.D) • o.val ∈ m ↔
      (x : generated L S) ∈ Q (fullFamily L S) (base (fullFamily L S) false) := by
  let := plane d mark h c₀ c₁ hn₀ hn₁ E₀ hm
  let A := (TriangleGeometry.family d true).pCoreIn 2
  let I := Q (fullFamily L S) (base (fullFamily L S) true) ⊓
    Q (fullFamily L S) (base (fullFamily L S) false)
  let fA : I → A := fun z => originalCoreEquiv d mark true ⟨z,z.property.1⟩
  have hother (z : I) : (fA z : X ⧸ d.D) ∈ (TriangleGeometry.family d false).pCoreIn 2 := by
    change originalCoreMap d mark true ⟨z,z.property.1⟩ ∈ _
    rw [←originalCoreMap_intersection d mark h ⟨z,z.property.2,z.property.1⟩]
    exact (originalCoreEquiv d mark false ⟨z,z.property.2⟩).property
  have hfix (z : I) : (fA z : X ⧸ d.D) • m = m := by
    apply Subtype.ext
    exact core_le_ballKernel d mark h c₀ c₁ split false (hother z) m.val
      ((mem_ball_one _ _ _).mpr (Or.inl hCm))
  let f : I → {p : Point (TriangleGeometry.family d) // p ∈ m ∧ p ∉ QuotientPlane.axis d} :=
    fun z => ⟨(fA z : X ⧸ d.D) • o.val,
      (hfix z) ▸ (IsCollineationAction.smul_mem_smul_iff (fA z : X ⧸ d.D) o.val m).mpr hom,
      (affineOrbit A (QuotientPlane.axis d) (core_fixes_axis d) o (fA z)).property⟩
  have hfree {a b : A} (he : (a : X ⧸ d.D) • o.val = (b : X ⧸ d.D) • o.val) : a = b :=
    affineOrbit_injective A (QuotientPlane.axis d) (core_fixes_axis d) o
      (core_isElation d mark h c₀ c₁ E₁ split hcenter) (Subtype.ext he)
  have hinj : Function.Injective f := by
    intro a b he
    have hh := (originalCoreEquiv d mark true).injective (hfree (congrArg Subtype.val he))
    exact Subtype.ext (congrArg (fun u : Q (fullFamily L S) (base (fullFamily L S) true) => (u : generated L S)) hh)
  have hml : m ≠ QuotientPlane.axis d := fun he => o.property (he ▸ hom)
  have hCl : QuotientPlane.centerPoint d ∈ QuotientPlane.axis d :=
    ⟨Bool.false_ne_true,CosetGeometry.incident_base _ _ _⟩
  have hcard : Nat.card I = Nat.card {p : Point (TriangleGeometry.family d) // p ∈ m ∧ p ∉ QuotientPlane.axis d} := by
    rw [card_line_off_axis _ m _ hCl hCm hml,plane_order d mark h c₀ c₁ hn₀ hn₁ E₀ hm]
    exact core_intersection_card c₁ h.generatedLocallyRankOneTriple
      (paired_cores_eq_centers_of_actions h.generatedLocallyRankOneTriple c₀ c₁).2 hcenter E₁
  have honto := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj,hcard⟩).2
  constructor
  · intro hx
    obtain ⟨z,hz⟩ := honto ⟨_,hx,
      (affineOrbit A (QuotientPlane.axis d) (core_fixes_axis d) o (originalCoreEquiv d mark true x)).property⟩
    have he := (originalCoreEquiv d mark true).injective (hfree (congrArg Subtype.val hz))
    exact (congrArg Subtype.val he) ▸ z.property.2
  · intro hx
    have he := hfix ⟨x,x.property,hx⟩
    exact he ▸ (IsCollineationAction.smul_mem_smul_iff (originalCoreEquiv d mark true x : X ⧸ d.D) o.val m).mpr hom

/-- The source marked Sylow determines the pencil's one field line after independent transport. -/
theorem affineChart_mem_line_iff (m : Line (TriangleGeometry.family d))
    (hCm : QuotientPlane.centerPoint d ∈ m) (hom : o.val ∈ m) (t : Fin 2 → k₁) :
    (chart o t).val ∈ m ↔
      ∀ s ∈ (c₁.imageSylow : Subgroup SL(2,k₁)), Matrix.mulVec s.val t = t := by
  let φ₀ := A2Source.coreCoordinates c₁ h.generatedLocallyRankOneTriple
    (paired_cores_eq_centers_of_actions h.generatedLocallyRankOneTriple c₀ c₁).2 hcenter E₁
  let x := φ₀.symm (.ofAdd t)
  have he : (φ₀ x).toAdd = t := congrArg Multiplicative.toAdd (φ₀.apply_symm_apply (.ofAdd t))
  exact (core_orbit_mem_line_iff d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o m hCm hom x).trans
    ((coreCoordinates_mem_neighbor_iff c₁ h.generatedLocallyRankOneTriple
      (paired_cores_eq_centers_of_actions h.generatedLocallyRankOneTriple c₀ c₁).2 hcenter E₁ x).trans
        (Iff.of_eq (congrArg (fun t => ∀ s ∈ (c₁.imageSylow : Subgroup SL(2,k₁)),
          Matrix.mulVec s.val t = t) he)))

/-- Move the affine origin by the original actor through its actual endpoint marking. -/
def actorAffineOrigin (a : c₁.actor) : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d} :=
  ⟨actorMap c₁ _ (endpointMarking d mark true) a • o.val,by
    intro hp
    exact o.property ((IsCollineationAction.smul_mem_smul_iff
      (actorMap c₁ _ (endpointMarking d mark true) a) o.val (QuotientPlane.axis d)).mp
        ((actor_fixes_axis d mark c₁ a).symm ▸ hp))⟩

/-- The transported actor uses precisely its supplied original SL₂ quotient matrix. -/
theorem affineChart_actor (a : c₁.actor) (t : Fin 2 → k₁) :
    (chart (actorAffineOrigin d mark c₁ o a) (Matrix.mulVec (c₁.quotient a).val t)).val =
      actorMap c₁ _ (endpointMarking d mark true) a • (chart o t).val := by
  let φ := originalCoordinates d mark h c₀ c₁ hcenter E₁
  let x := φ.symm (.ofAdd t)
  obtain ⟨y,hy,hφ⟩ := originalCoordinates_conjugate d mark h c₀ c₁ hcenter E₁ a x
  have hφ' : φ y = .ofAdd (Matrix.mulVec (c₁.quotient a).val t) := by
    apply Multiplicative.toAdd.injective
    simpa only [x,φ,MulEquiv.apply_symm_apply,toAdd_ofAdd] using hφ
  have he : φ.symm (.ofAdd (Matrix.mulVec (c₁.quotient a).val t)) = y :=
    (congrArg φ.symm hφ').symm.trans (φ.symm_apply_apply y)
  change (φ.symm (.ofAdd (Matrix.mulVec (c₁.quotient a).val t)) : X ⧸ d.D) •
    (actorMap c₁ _ (endpointMarking d mark true) a • o.val) =
      actorMap c₁ _ (endpointMarking d mark true) a • ((x : X ⧸ d.D) • o.val)
  rw [he,hy]
  simp only [mul_smul,inv_smul_smul]

/-- Every actor-transported pencil uses the transported fixed line over this same field. -/
theorem affineChart_mem_actor_line_iff (a : c₁.actor) (m : Line (TriangleGeometry.family d))
    (hCm : (actorMap c₁ _ (endpointMarking d mark true) a) • QuotientPlane.centerPoint d ∈ m) (hom : o.val ∈ m) (t : Fin 2 → k₁) :
    (affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
      (Matrix.mulVec (c₁.quotient a).val t)).val ∈ m ↔
      ∀ s ∈ (c₁.imageSylow : Subgroup SL(2,k₁)), Matrix.mulVec s.val t = t := by
  let o' := actorAffineOrigin d mark c₁ o a⁻¹
  have ho' : actorAffineOrigin d mark c₁ o' a = o := by
    apply Subtype.ext
    change actorMap c₁ _ (endpointMarking d mark true) a •
      (actorMap c₁ _ (endpointMarking d mark true) a⁻¹ • o.val) = o.val
    rw [map_inv,smul_inv_smul]
  have hCm' : QuotientPlane.centerPoint d ∈ (actorMap c₁ _ (endpointMarking d mark true) a)⁻¹ • m := by
    simpa only [inv_smul_smul] using
      (IsCollineationAction.smul_mem_smul_iff (actorMap c₁ _ (endpointMarking d mark true) a)⁻¹ ((actorMap c₁ _ (endpointMarking d mark true) a) • QuotientPlane.centerPoint d) m).mpr hCm
  have hom' : o'.val ∈ (actorMap c₁ _ (endpointMarking d mark true) a)⁻¹ • m := by
    change actorMap c₁ _ (endpointMarking d mark true) a⁻¹ • o.val ∈ _
    rw [map_inv]
    exact (IsCollineationAction.smul_mem_smul_iff (actorMap c₁ _ (endpointMarking d mark true) a)⁻¹ o.val m).mpr hom
  rw [← ho',affineChart_actor]
  have hi := IsCollineationAction.smul_mem_smul_iff (actorMap c₁ _ (endpointMarking d mark true) a)
    (affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o' t).val ((actorMap c₁ _ (endpointMarking d mark true) a)⁻¹ • m)
  rw [smul_inv_smul] at hi
  exact hi.trans (affineChart_mem_line_iff d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o' _ hCm' hom' t)

/-- Every line through the affine origin has a direction obtained from this one
Sylow fixed line by the original marked actor, without comparing two fields. -/
theorem affineChart_all_directions
    (m : Line (TriangleGeometry.family d)) (hom : o.val ∈ m) :
    ∃ a : c₁.actor, ∀ t : Fin 2 → k₁,
      (affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
        (Matrix.mulVec (c₁.quotient a).val t)).val ∈ m ↔
      ∀ s ∈ (c₁.imageSylow : Subgroup SL(2,k₁)), Matrix.mulVec s.val t = t := by
  let := plane d mark h c₀ c₁ hn₀ hn₁ E₀ hm
  have hml : m ≠ QuotientPlane.axis d := fun he => o.property (he ▸ hom)
  let C : Point (TriangleGeometry.family d) := HasPoints.mkPoint hml
  have hCm : C ∈ m := (HasPoints.mkPoint_ax hml).1
  have hCl : C ∈ QuotientPlane.axis d := (HasPoints.mkPoint_ax hml).2
  obtain ⟨a,haC⟩ := actor_transitive_on_axis d mark h c₁ hn₁ C hCl
  exact ⟨a,fun t => affineChart_mem_actor_line_iff d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
    a m (haC.symm ▸ hCm) hom t⟩

/-- Changing the affine origin is translation by its coordinates in the same chart. -/
theorem affineChart_change_origin (b t : Fin 2 → k₁) :
    (affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter
      (affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o b) t).val =
      (affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o (t + b)).val := by
  let φ := originalCoordinates d mark h c₀ c₁ hcenter E₁
  change (φ.symm (.ofAdd t) : X ⧸ d.D) • ((φ.symm (.ofAdd b) : X ⧸ d.D) • o.val) =
    (φ.symm (.ofAdd t * .ofAdd b) : X ⧸ d.D) • o.val
  rw [map_mul, Subgroup.coe_mul, mul_smul]

/-- All affine lines, not just the marked pencil, are cosets of the transported
fixed line in the single field chart. -/
theorem affineChart_all_affine_lines
    (m : Line (TriangleGeometry.family d)) (hml : m ≠ QuotientPlane.axis d) :
    ∃ b : Fin 2 → k₁, ∃ a : c₁.actor, ∀ t : Fin 2 → k₁,
      (affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
        (Matrix.mulVec (c₁.quotient a).val t + b)).val ∈ m ↔
      ∀ s ∈ (c₁.imageSylow : Subgroup SL(2,k₁)), Matrix.mulVec s.val t = t := by
  let := plane d mark h c₀ c₁ hn₀ hn₁ E₀ hm
  let C : Point (TriangleGeometry.family d) := HasPoints.mkPoint hml
  have hCm : C ∈ m := (HasPoints.mkPoint_ax hml).1
  have hCl : C ∈ QuotientPlane.axis d := (HasPoints.mkPoint_ax hml).2
  have hpos : 0 < Nat.card {p : Point (TriangleGeometry.family d) // p ∈ m ∧ p ∉ QuotientPlane.axis d} := by
    rw [card_line_off_axis (QuotientPlane.axis d) m C hCl hCm hml, plane_order d mark h c₀ c₁ hn₀ hn₁ E₀ hm]
    exact Nat.card_pos
  obtain ⟨p⟩ := (Nat.card_pos_iff.mp hpos).1
  let p' : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d} := ⟨p,p.property.2⟩
  let b := (affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).symm p'
  have hb : affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o b = p' :=
    Equiv.apply_symm_apply _ _
  obtain ⟨a,ha⟩ := affineChart_all_directions d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter p' m p.property.1
  refine ⟨b,a,?_⟩
  intro t
  rw [← affineChart_change_origin, hb]
  exact ha t

/-- The incidence equations are ordinary affine field lines: one nonzero field
vector parametrizes the fixed direction, and the same source actors give all directions. -/
theorem affineChart_field_lines :
    ∃ v₀ : Fin 2 → k₁, v₀ ≠ 0 ∧ ∀ m : Line (TriangleGeometry.family d), m ≠ QuotientPlane.axis d →
      ∃ b : Fin 2 → k₁, ∃ a : c₁.actor, ∀ t : Fin 2 → k₁,
        (affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
          (Matrix.mulVec (c₁.quotient a).val t + b)).val ∈ m ↔
          ∃ r : k₁, t = r • v₀ := by
  obtain ⟨v₀,hv₀,hv⟩ := exists_neighbor_fixed_line c₁ h.generatedLocallyRankOneTriple (paired_cores_eq_centers_of_actions h.generatedLocallyRankOneTriple c₀ c₁).2 hcenter E₁
  refine ⟨v₀,hv₀,?_⟩
  intro m hml
  obtain ⟨b,a,ha⟩ := affineChart_all_affine_lines d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o m hml
  exact ⟨b,a,fun t => (ha t).trans (hv t)⟩

/-- Every actual affine line has the ordinary field-line equation in the one chart. -/
theorem affineChart_line_equation
    (m : Line (TriangleGeometry.family d)) (hml : m ≠ QuotientPlane.axis d) :
    ∃ b e : Fin 2 → k₁, e ≠ 0 ∧ ∀ t : Fin 2 → k₁,
      (affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o t).val ∈ m ↔
        ∃ r : k₁, t = b + r • e := by
  obtain ⟨v₀,hv₀,hv⟩ := affineChart_field_lines d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
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

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source.MarkedPlane
