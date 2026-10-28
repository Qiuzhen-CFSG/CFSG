module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TriangleStructure.Plane
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TriangleStructure.FixedLine
public import Theory.Combinatorics.TranslationPlane.ProjectiveRecognition

/-!
# One-field incidence coordinates on the original split triangle

The middle-root orbit fills each affine line of the marked pencil by
regularity and its order q. Equivariant natural SL₂ coordinates identify
this root with a full field line. The actual root-generated actor is
transitive on the infinity line, so it supplies every direction. Radical
translations then give the ordinary equations of all affine lines.
The projective-completion theorem extends this chart to both full fibers.

One original linear factor, rotation three and the same fully marked split
quotient discharge every natural-action and incidence-coordinate premise.
The field of order two is included. Evaluations retain the actual radical,
quotient action and full endpoint marking. The recognition consumer uses
these coordinates to construct simultaneous roots and both endpoint squares.
Source: Fong--Seitz I (3E), printed p.14 (projective-plane recognition), and
DGS, Groups and Graphs (1985), (10.5), Theorem D, printed pp.156,224.
-/

@[expose] public noncomputable section
open Subgroup Configuration Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TriangleStructure
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 3) (i : Fin 2) {n : ℕ}
  (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n))

/-- The actual root-generated actor is transitive on the whole infinity line. -/
theorem rankOne_transitive_on_axis (p : Point (TriangleGeometry.family Q))
    (hp : p ∈ A2Source.QuotientPlane.axis Q) :
    ∃ a : rankOne Q split 1, (a : X ⧸ Q.D) • A2Source.QuotientPlane.centerPoint Q = p := by
  let F := TriangleGeometry.family Q
  obtain ⟨g,hg,hgp⟩ := neighbor_base_rep F true hp.symm
  let b : UnitarySource.PanelEndpoint Q 1 := ⟨g,hg⟩
  obtain ⟨r,hr⟩ := UnitarySource.exists_actor_from_base Q split 1 (QuotientGroup.mk b)
  rw [ReeSource.panelBase_eq_mk_one Q split 1] at hr
  have he : QuotientGroup.mk (r.val : UnitarySource.PanelEndpoint Q 1) =
      (QuotientGroup.mk b : Panel Q 1) := by
    change QuotientGroup.mk ((r.val : UnitarySource.PanelEndpoint Q 1)*1) = _ at hr
    simpa only [mul_one] using hr
  have hb := QuotientGroup.eq.mp he
  have hB : (r.val : X ⧸ Q.D)⁻¹*g ∈ Q.tits.B := hb
  let a : rankOne Q split 1 := ⟨r.val,r.property⟩
  have hh := (Theory.AlgebraicGroup.TitsSystem.DihedralGeometry.smul_base_eq_iff F
    (a : X ⧸ Q.D) g false).mpr (Q.tits.B_le_standardParabolic _ hB)
  refine ⟨a,Subtype.ext (hh.trans ?_)⟩
  change CosetGeometry.Vertex.mk false (g • ((1 : X ⧸ Q.D) : (X ⧸ Q.D) ⧸ F false)) = _
  change CosetGeometry.Vertex.mk false ((g : X ⧸ Q.D) : (X ⧸ Q.D) ⧸ F false) = p.val at hgp
  simpa only [MulAction.Quotient.smul_mk,smul_eq_mul,mul_one] using hgp

/-- The root-generated actor fixes the same infinity line. -/
theorem rankOne_fixes_axis (a : rankOne Q split 1) :
    (a : X ⧸ Q.D) • A2Source.QuotientPlane.axis Q = A2Source.QuotientPlane.axis Q := by
  apply Subtype.ext
  change (a : X ⧸ Q.D) • base (TriangleGeometry.family Q) true = _
  apply MulAction.mem_stabilizer_iff.mp
  rw [CosetGeometry.stabilizer_base]
  exact rankOne_le_parabolic Q split 1 a.property

namespace FieldCoordinates
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  (hF : Nat.card F = 2^n)
  (hV : ∀ j, simpleRemainder Q split j ≤ localKernel Q j)
  (μ : rankOne Q split 1 ≃* SL(2,F))
  (c : simpleRemainder Q split 1 ≃* Multiplicative (Fin 2 → F))
  (hc : ∀ r v, (c (radicalAction Q split 1 (hV 1) r v)).toAdd =
    Matrix.mulVec (μ r).val (c v).toAdd)

/-- One field chart obtained by evaluating the actual radical at the origin. -/
def chart (o : {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q}) :
    (Fin 2 → F) ≃ {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q} :=
  Multiplicative.ofAdd.trans (c.symm.toEquiv.trans
    (original_affineOrbitEquiv Q e h split hm i hi o))

omit [Finite F] [CharP F 2] in
theorem chart_apply (o : {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q})
    (t : Fin 2 → F) :
    (chart Q e h split hm i hi c o t).val = (c.symm (.ofAdd t) : X ⧸ Q.D) • o.val := rfl

include e h hm i hi in
/-- The middle-root orbit is the full affine part of each marked-pencil line. -/
theorem orbit_mem_line_iff
    (o : {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q})
    (m : Line (TriangleGeometry.family Q)) (hCm : A2Source.QuotientPlane.centerPoint Q ∈ m)
    (hom : o.val ∈ m) (x : simpleRemainder Q split 1) :
    (x : X ⧸ Q.D) • o.val ∈ m ↔ (x : X ⧸ Q.D) ∈ simpleRemainder Q split 0 := by
  let := original_plane Q e h split hm i hi
  let I := simpleRemainder Q split 1 ⊓ simpleRemainder Q split 0
  have hfix (z : I) : (z : X ⧸ Q.D) • m = m := by
    apply Subtype.ext
    exact original_radical_le_ballKernel Q e h split hm i hi false z.property.2 m.val
      ((mem_ball_one _ _ _).mpr (Or.inl hCm))
  let f : I → {p : Point (TriangleGeometry.family Q) // p ∈ m ∧ p ∉ A2Source.QuotientPlane.axis Q} :=
    fun z => ⟨(z : X ⧸ Q.D) • o.val,
      (hfix z) ▸ (IsCollineationAction.smul_mem_smul_iff (z : X ⧸ Q.D) o.val m).mpr hom,
      (original_affineOrbitEquiv Q e h split hm i hi o ⟨z,z.property.1⟩).property⟩
  have hfree {a b : simpleRemainder Q split 1}
      (he : (a : X ⧸ Q.D) • o.val = (b : X ⧸ Q.D) • o.val) : a = b :=
    (original_affineOrbitEquiv Q e h split hm i hi o).injective (Subtype.ext he)
  have hinj : Function.Injective f := by
    intro a b he
    exact Subtype.ext (congrArg (fun z : simpleRemainder Q split 1 => (z : X ⧸ Q.D)) (hfree (a := ⟨a,a.property.1⟩) (b := ⟨b,b.property.1⟩) (congrArg Subtype.val he)))
  have hml : m ≠ A2Source.QuotientPlane.axis Q := fun he => o.property (he ▸ hom)
  have hCl : A2Source.QuotientPlane.centerPoint Q ∈ A2Source.QuotientPlane.axis Q :=
    ⟨Bool.false_ne_true,CosetGeometry.incident_base _ _ _⟩
  have hcard : Nat.card I = Nat.card {p : Point (TriangleGeometry.family Q) //
      p ∈ m ∧ p ∉ A2Source.QuotientPlane.axis Q} := by
    rw [card_line_off_axis _ m _ hCl hCm hml,original_plane_order Q e h split hm i hi]
    change Nat.card (simpleRemainder Q split 1 ⊓ simpleRemainder Q split 0 : Subgroup (X ⧸ Q.D)) = _
    rw [Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure.radical_intersection Q split hm 1 0 (by decide)]
    simp only [rootAt,card_rightConjugate]
    obtain ⟨K,hK,hfin,hcard,⟨ν⟩⟩ := original_linear_factors Q e h split hm i hi 1
    let := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hcard)
    let := h.finite_local 1
    obtain ⟨T,hT⟩ := h.sylow 1
    exact (simpleRoot_card_linear Q e h split 1 T hT ν).trans hcard
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj,hcard⟩).2
  constructor
  · intro hx
    obtain ⟨z,hz⟩ := hs ⟨_,hx,(original_affineOrbitEquiv Q e h split hm i hi o x).property⟩
    exact (congrArg Subtype.val (hfree (a := ⟨z,z.property.1⟩) (b := x) (congrArg Subtype.val hz))) ▸ z.property.2
  · intro hx
    exact (hfix ⟨x,x.property,hx⟩) ▸
      (IsCollineationAction.smul_mem_smul_iff (x : X ⧸ Q.D) o.val m).mpr hom

/-- The actual root actor transports affine origins. -/
def actorOrigin
    (o : {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q})
    (a : rankOne Q split 1) : {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q} :=
  ⟨(a : X ⧸ Q.D) • o.val,by
    intro hp
    exact o.property ((IsCollineationAction.smul_mem_smul_iff (a : X ⧸ Q.D) o.val
      (A2Source.QuotientPlane.axis Q)).mp ((rankOne_fixes_axis Q split a).symm ▸ hp))⟩

omit [Finite F] [CharP F 2] in
include hc in
theorem chart_actor
    (o : {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q})
    (a : rankOne Q split 1) (t : Fin 2 → F) :
    (chart Q e h split hm i hi c (actorOrigin Q split o a) (Matrix.mulVec (μ a).val t)).val =
      (a : X ⧸ Q.D) • (chart Q e h split hm i hi c o t).val := by
  let x := c.symm (.ofAdd t)
  have he : c.symm (.ofAdd (Matrix.mulVec (μ a).val t)) = radicalAction Q split 1 (hV 1) a x := by
    apply c.injective
    apply Multiplicative.toAdd.injective
    rw [MulEquiv.apply_symm_apply,hc]
    simp only [x,MulEquiv.apply_symm_apply,toAdd_ofAdd]
  change (c.symm (.ofAdd (Matrix.mulVec (μ a).val t)) : X ⧸ Q.D) •
      ((a : X ⧸ Q.D) • o.val) = (a : X ⧸ Q.D) • ((x : X ⧸ Q.D) • o.val)
  rw [he,radicalAction_apply]
  simp only [mul_smul,inv_smul_smul]

omit [Finite F] [CharP F 2] in
theorem chart_change_origin
    (o : {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q}) (b t : Fin 2 → F) :
    (chart Q e h split hm i hi c (chart Q e h split hm i hi c o b) t).val =
      (chart Q e h split hm i hi c o (t+b)).val := by
  change (c.symm (.ofAdd t) : X ⧸ Q.D) • ((c.symm (.ofAdd b) : X ⧸ Q.D) • o.val) =
    (c.symm (.ofAdd t * .ofAdd b) : X ⧸ Q.D) • o.val
  rw [map_mul,Subgroup.coe_mul,mul_smul]

include hc in
/-- The same natural coordinates turn every line of the marked pencil into
one full field line, including over the binary field. -/
theorem pencil_field_line :
    ∃ v₀ : Fin 2 → F, v₀ ≠ 0 ∧
      ∀ (o : {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q})
        (m : Line (TriangleGeometry.family Q)),
        A2Source.QuotientPlane.centerPoint Q ∈ m → o.val ∈ m → ∀ t : Fin 2 → F,
          (chart Q e h split hm i hi c o t).val ∈ m ↔ ∃ r : F, t = r • v₀ := by
  have hE (j : Fin 2) := elementary_root_of_linear_factor Q e h split j
    (original_linear_factors Q e h split hm i hi j)
  obtain ⟨v₀,hv₀,hv⟩ :=
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure.radical_intersection_field_line
      Q split hm hV hE 1 0 (by decide) μ c hc
  refine ⟨v₀,hv₀,?_⟩
  intro o m hCm hom t
  exact (orbit_mem_line_iff Q e h split hm i hi o m hCm hom (c.symm (.ofAdd t))).trans
    (by simpa only [MulEquiv.apply_symm_apply,toAdd_ofAdd] using hv (c.symm (.ofAdd t)))

include hc in
/-- Every affine line has an ordinary equation over this single field.
The actual rank-one actor supplies the directions and the actual radical
supplies translations; no incidence equation is an input. -/
theorem chart_line_equation
    (o : {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q})
    (m : Line (TriangleGeometry.family Q)) (hml : m ≠ A2Source.QuotientPlane.axis Q) :
    ∃ b v : Fin 2 → F, v ≠ 0 ∧ ∀ t : Fin 2 → F,
      (chart Q e h split hm i hi c o t).val ∈ m ↔ ∃ r : F, t = b + r • v := by
  let := original_plane Q e h split hm i hi
  obtain ⟨v₀,hv₀,hv⟩ := pencil_field_line Q e h split hm i hi hV μ c hc
  let C : Point (TriangleGeometry.family Q) := HasPoints.mkPoint hml
  have hCm : C ∈ m := (HasPoints.mkPoint_ax hml).1
  have hCl : C ∈ A2Source.QuotientPlane.axis Q := (HasPoints.mkPoint_ax hml).2
  obtain ⟨a,haC⟩ := rankOne_transitive_on_axis Q split C hCl
  have hpos : 0 < Nat.card {p : Point (TriangleGeometry.family Q) //
      p ∈ m ∧ p ∉ A2Source.QuotientPlane.axis Q} := by
    rw [card_line_off_axis _ m C hCl hCm hml,original_plane_order Q e h split hm i hi]
    exact pow_pos (by decide) _
  obtain ⟨p⟩ := (Nat.card_pos_iff.mp hpos).1
  let p' : {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q} :=
    ⟨p,p.property.2⟩
  let b := (chart Q e h split hm i hi c o).symm p'
  have hb : chart Q e h split hm i hi c o b = p' := Equiv.apply_symm_apply _ _
  let o' := actorOrigin Q split p' a⁻¹
  have ho' : actorOrigin Q split o' a = p' := by
    apply Subtype.ext
    change (a : X ⧸ Q.D) • ((a : X ⧸ Q.D)⁻¹ • p'.val) = _
    exact smul_inv_smul _ _
  have hC' : A2Source.QuotientPlane.centerPoint Q ∈ (a : X ⧸ Q.D)⁻¹ • m := by
    have hh := (IsCollineationAction.smul_mem_smul_iff (a : X ⧸ Q.D)⁻¹
      ((a : X ⧸ Q.D) • A2Source.QuotientPlane.centerPoint Q) m).mpr (haC.symm ▸ hCm)
    simpa only [inv_smul_smul] using hh
  have ho'm : o'.val ∈ (a : X ⧸ Q.D)⁻¹ • m :=
    (IsCollineationAction.smul_mem_smul_iff (a : X ⧸ Q.D)⁻¹ p'.val m).mpr p.property.1
  have ha (t : Fin 2 → F) :
      (chart Q e h split hm i hi c o (Matrix.mulVec (μ a).val t + b)).val ∈ m ↔
        ∃ r : F, t = r • v₀ := by
    rw [←chart_change_origin,hb,←ho',chart_actor Q e h split hm i hi hV μ c hc]
    have ht := IsCollineationAction.smul_mem_smul_iff (a : X ⧸ Q.D)
      (chart Q e h split hm i hi c o' t).val ((a : X ⧸ Q.D)⁻¹ • m)
    rw [smul_inv_smul] at ht
    exact ht.trans (hv o' _ hC' ho'm t)
  let A := μ a
  let v := Matrix.mulVec A.val v₀
  have hnv : v ≠ 0 := by
    intro hz
    have hh := congrArg (fun t : Fin 2 → F => A⁻¹ • t) hz
    change A⁻¹ • (A • v₀) = A⁻¹ • (0 : Fin 2 → F) at hh
    exact hv₀ (by simpa only [inv_smul_smul,smul_zero] using hh)
  refine ⟨b,v,hnv,?_⟩
  intro t
  let u : Fin 2 → F := A⁻¹ • (t-b)
  have hu : Matrix.mulVec A.val u = t-b := smul_inv_smul A (t-b)
  have hut : Matrix.mulVec A.val u+b = t := (congrArg (·+b) hu).trans (sub_add_cancel t b)
  rw [←hut,ha]
  constructor
  · rintro ⟨r,hr⟩
    exact ⟨r,by rw [hr,Matrix.mulVec_smul]; exact add_comm _ _⟩
  · rintro ⟨r,hr⟩
    refine ⟨r,?_⟩
    apply MulAction.injective A
    change Matrix.mulVec A.val u = Matrix.mulVec A.val (r • v₀)
    rw [Matrix.mulVec_smul]
    exact add_right_cancel (hr.trans (add_comm b (r • v)))

include e h hm i hi hc in
/-- The proved field-line equations extend to all projective points and lines,
with the marked axis and the literal radical evaluation preserved. -/
theorem projective_coordinates
    (o : {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q}) :
    ∃ (ep : Point (TriangleGeometry.family Q) ≃ TranslationPlane.FieldChart.PG F)
      (el : Line (TriangleGeometry.family Q) ≃ TranslationPlane.FieldChart.PG F),
      el (A2Source.QuotientPlane.axis Q) = TranslationPlane.FieldChart.axis F ∧
      (∀ p m, ep p ∈ el m ↔ p ∈ m) ∧
      ∀ t : Fin 2 → F, ep ((c.symm (.ofAdd t) : X ⧸ Q.D) • o.val) =
        TranslationPlane.FieldChart.point F t := by
  let := original_plane Q e h split hm i hi
  exact TranslationPlane.exists_projective_coordinates (A2Source.QuotientPlane.axis Q)
    (chart Q e h split hm i hi c o)
    (chart_line_equation Q e h split hm i hi hV μ c hc o)

end FieldCoordinates

include e h split hm i hi in
/-- One original linear factor constructs projective field coordinates for the
same marked triangle. No natural-action or incidence-coordinate premise remains. -/
theorem original_field_coordinates :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2^n ∧
      ∃ c : simpleRemainder Q split 1 ≃* Multiplicative (Fin 2 → F),
        ∀ o : {p : Point (TriangleGeometry.family Q) // p ∉ A2Source.QuotientPlane.axis Q},
          ∃ (ep : Point (TriangleGeometry.family Q) ≃ TranslationPlane.FieldChart.PG F)
            (el : Line (TriangleGeometry.family Q) ≃ TranslationPlane.FieldChart.PG F),
            el (A2Source.QuotientPlane.axis Q) = TranslationPlane.FieldChart.axis F ∧
            (∀ p m, ep p ∈ el m ↔ p ∈ m) ∧
            ∀ t : Fin 2 → F, ep ((c.symm (.ofAdd t) : X ⧸ Q.D) • o.val) =
              TranslationPlane.FieldChart.point F t := by
  have hV (j : Fin 2) := (odd_linear_regularity Q e h split
    (hm ▸ (by decide : Odd 3)) i hi j).1
  have hE (j : Fin 2) := elementary_root_of_linear_factor Q e h split j
    (original_linear_factors Q e h split hm i hi j)
  obtain ⟨F,hF,hfin,hchar,hcard,μ,_,_⟩ := original_natural_cores Q e h split hm i hi 1
  let := Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure.remainder_elementary
    Q split hm hV hE 1
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨d,hd⟩ := Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure.radical_natural_coordinates
    Q split hm hV hE 1 μ
  let c : simpleRemainder Q split 1 ≃* Multiplicative (Fin 2 → F) :=
    d.toAddEquiv.toMultiplicative
  have hc : ∀ r v, (c (radicalAction Q split 1 (hV 1) r v)).toAdd =
      Matrix.mulVec (μ r).val (c v).toAdd := fun r v => hd r (Additive.ofMul v)
  exact ⟨F,hF,hfin,hchar,hcard,c,
    FieldCoordinates.projective_coordinates Q e h split hm i hi hV μ c hc⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TriangleStructure
