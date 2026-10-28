module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.Base
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoPointDisplacement

/-!
# Natural coordinates for the original whole core

The ambient initial cover selects one natural symplectic marking. Innerness
makes its component the full ambient quotient, so that marking acts on the
entire endpoint stabilizer. The cover projection and the projection through
the complete fixed core have the same kernel and are both surjective onto
their images. Their quotient comparison gives natural coordinates on the
literal whole core modulo its complete fixed attachment.

The same inner conjugator twists the natural coordinates and the descended
marking. Conjugation compatibility is proved from the ambient cover, and no
compatibility of an independently chosen symplectic marking is assumed.

Source: Meierfrankenfeld–Stellmacher (1993), (3.7), pp.876–877.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
open DistanceTwoRecognition ChapterB.QuasisimpleSource MSCentralOrbit
open Theory.SpecificGroups.SymplecticFour

private theorem equiv_of_same_kernel {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (p : A →* C) (hf : Function.Surjective f) (hp : Function.Surjective p)
    (hfp : f.ker = p.ker) : ∃ b : B ≃* C, ∀ w, b (f w) = p w := by
  let b := (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hfp).trans
      (QuotientGroup.quotientKerEquivOfSurjective p hp))
  refine ⟨b,?_⟩
  intro w
  have hh := (QuotientGroup.quotientKerEquivOfSurjective f hf).symm_apply_apply
    (QuotientGroup.mk' f.ker w)
  change (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f w) = _ at hh
  change QuotientGroup.quotientKerEquivOfSurjective p hp
    (QuotientGroup.quotientMulEquivOfEq hfp
      ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f w))) = _
  rw [hh]
  rfl

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)

omit [Finite H] in
/-- Innerness makes the original component image the whole ambient quotient. -/
theorem original_component_eq_top (hinner : K ⊔ pCore 2 H = ⊤) :
    K.map (QuotientGroup.mk' (pCore 2 H)) = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hh := congrArg (fun A : Subgroup H => A.map q) hinner
  rw [Subgroup.map_sup,show (pCore 2 H).map q = ⊥ from
    (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
  exact hh

/-- The component marking selected by the actual ambient natural cover. -/
def coverComponentEquiv {a : Vertex R}
    (cv : AmbientVertexCover R (originalMovedSection h) n a) :
    K.map (QuotientGroup.mk' (pCore 2 H)) ≃* Sp cv.field.Carrier :=
  cv.equiv.groupEquiv.trans ((MulEquiv.subgroupCongr
    (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top (by
      rw [cv.field.card_eq,cv.degree]
      exact lt_of_lt_of_le (by decide : 2 < 2^2)
        (Nat.pow_le_pow_right (by decide) h.nonbinary)))).trans Subgroup.topEquiv)

/-- One compatible marking of the whole original endpoint stabilizer. -/
def coverQuotient (hinner : K ⊔ pCore 2 H = ⊤) {a : Vertex R}
    (cv : AmbientVertexCover R (originalMovedSection h) n a) :
    stabilizer R a →* Sp cv.field.Carrier :=
  (coverComponentEquiv h cv).toMonoidHom.comp
    (cv.quotient.codRestrict (K.map (QuotientGroup.mk' (pCore 2 H)))
      (fun _ => (original_component_eq_top hinner).symm.le (mem_top _)))

/-- The selected whole marking agrees with the component action on every
quotient element, since innerness puts that element in the component. -/
theorem coverQuotient_apply (hinner : K ⊔ pCore 2 H = ⊤) {a : Vertex R}
    (cv : AmbientVertexCover R (originalMovedSection h) n a) (x : stabilizer R a) :
    coverQuotient h hinner cv x =
      (cv.equiv.groupEquiv ⟨cv.quotient x,
        (original_component_eq_top hinner).symm.le (mem_top _)⟩).val := by rfl

/-- The compatible marking is onto the complete symplectic group. -/
theorem coverQuotient_onto (hinner : K ⊔ pCore 2 H = ⊤) {a : Vertex R}
    (cv : AmbientVertexCover R (originalMovedSection h) n a) :
    Function.Surjective (coverQuotient h hinner cv) := by
  intro y
  obtain ⟨c,hc⟩ := (coverComponentEquiv h cv).surjective y
  obtain ⟨x,hx⟩ := cv.onto c.val
  refine ⟨x,?_⟩
  change coverComponentEquiv h cv ⟨cv.quotient x,_⟩ = y
  rw [show (⟨cv.quotient x,_⟩ : K.map (QuotientGroup.mk' (pCore 2 H))) = c from
    Subtype.ext hx]
  exact hc

/-- The kernel is exactly the original endpoint two-core. -/
theorem coverQuotient_kernel (hinner : K ⊔ pCore 2 H = ⊤) {a : Vertex R}
    (cv : AmbientVertexCover R (originalMovedSection h) n a) :
    (coverQuotient h hinner cv).ker = (Q R a).subgroupOf (stabilizer R a) := by
  have hk : (coverQuotient h hinner cv).ker = cv.quotient.ker := by
    ext x
    change coverComponentEquiv h cv ⟨cv.quotient x,_⟩ = 1 ↔ cv.quotient x = 1
    rw [(coverComponentEquiv h cv).map_eq_one_iff]
    exact Subtype.ext_iff
  rw [hk,←cv.kernel_Q,subgroupOf_map_subtype_eq]

/-- The original cover projection intertwines the selected full marking. -/
theorem coverQuotient_projection (hinner : K ⊔ pCore 2 H = ⊤) {a : Vertex R}
    (cv : AmbientVertexCover R (originalMovedSection h) n a)
    (x : stabilizer R a) (v : (originalMovedSection h).space.toSubmodule) :
    MovedSection.coverProjection (originalMovedSection h) cv.equiv
        ((originalMovedSection h).space.toRepresentation (cv.quotient x) v) =
      coverQuotient h hinner cv x •
        MovedSection.coverProjection (originalMovedSection h) cv.equiv v := by
  rw [cv.projection]
  let c : K.map (QuotientGroup.mk' (pCore 2 H)) :=
    ⟨cv.quotient x,(original_component_eq_top hinner).symm.le (mem_top _)⟩
  exact MovedSection.ambientAction_component (originalMovedSection h) cv.equiv c _

omit [Finite H] [Finite F] [CharP F 2] in
private theorem coordinates_of_cover
    {W : Type*} [AddCommGroup W] {a : Vertex R}
    (κ : stabilizer R a →* Sp F)
    (hκ : κ.ker = (Q R a).subgroupOf (stabilizer R a)) (u : Sp F)
    (hwhole : Q R a = U R a ⊔ fixedCore R a)
    (act : stabilizer R a → W → W)
    (j : Multiplicative W →* FreeAmalgam R) (hjr : j.range = U R a)
    (p₀ : W →+ Vector F) (hp₀ : Function.Surjective p₀)
    (hker : ∀ v : W, p₀ v = 0 ↔
      j (Multiplicative.ofAdd v) ∈ centralizer (Ltilde R a : Set (FreeAmalgam R)))
    (hconj : ∀ (x : stabilizer R a) (v : W),
      j (Multiplicative.ofAdd (act x v)) = x.val*j (Multiplicative.ofAdd v)*x.val⁻¹)
    (hproj : ∀ (x : stabilizer R a) (v : W), p₀ (act x v) = κ x • p₀ v) :
    ∃ natural : layerImage R a (Q R a) ≃* Multiplicative (Vector F),
      ∀ (x : FixedQuotient R a) (v w : layerImage R a (Q R a)),
        (w : FixedQuotient R a) = x*v*x⁻¹ →
          (natural w).toAdd = markedQuotient R κ hκ u x • (natural v).toAdd := by
  have hUQ : U R a ≤ Q R a := le_sup_left.trans hwhole.symm.le
  have hQS : Q R a ≤ stabilizer R a := fun _ hx => hx.1
  let jS : Multiplicative W →* stabilizer R a :=
    j.codRestrict _ (fun w => hQS (hUQ (hjr ▸ ⟨w,rfl⟩)))
  have hjSr : jS.range = (U R a).subgroupOf (stabilizer R a) := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      exact hjr ▸ ⟨w,rfl⟩
    · intro hx
      obtain ⟨w,hw⟩ := (hjr.symm ▸ hx : x.val ∈ j.range)
      exact ⟨w,Subtype.ext hw⟩
  have himage : layerImage R a (Q R a) = layerImage R a (U R a) := by
    change ((Q R a).subgroupOf _).map _ = _
    rw [hwhole,subgroupOf_sup (hUQ.trans hQS) ((show fixedCore R a ≤ Q R a from inf_le_left).trans hQS),Subgroup.map_sup]
    have hzero : layerImage R a (fixedCore R a) = ⊥ := QuotientGroup.map_mk'_self _
    change layerImage R a (U R a) ⊔ layerImage R a (fixedCore R a) = _
    rw [hzero,sup_bot_eq]
  let f₀ := (fixedProjection R a).comp jS
  have hfr : f₀.range = layerImage R a (Q R a) := by
    rw [MonoidHom.range_comp,hjSr]
    exact himage.symm
  let f : Multiplicative W →* layerImage R a (Q R a) :=
    f₀.codRestrict _ (fun w => hfr ▸ ⟨w,rfl⟩)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨w,hw⟩ := (hfr.symm ▸ x.property : x.val ∈ f₀.range)
    exact ⟨w,Subtype.ext hw⟩
  let p := p₀.toMultiplicative
  have hp : Function.Surjective p := hp₀
  have hfp : f.ker = p.ker := by
    ext w
    change f w = 1 ↔ p w = 1
    rw [Subtype.ext_iff]
    change fixedProjection R a (jS w) = 1 ↔ p₀ w.toAdd = 0
    rw [show fixedProjection R a (jS w) = 1 ↔ jS w ∈ fixedAttachment R a from
      QuotientGroup.eq_one_iff (jS w)]
    change (j w ∈ Q R a ∧ j w ∈ centralizer (Ltilde R a : Set (FreeAmalgam R))) ↔ _
    exact (and_iff_right (hUQ (hjr ▸ ⟨w,rfl⟩))).trans (hker w.toAdd).symm
  obtain ⟨b,hbmap⟩ := equiv_of_same_kernel f p hf hp hfp
  let twist : Vector F ≃+ Vector F :=
    { toFun := fun v => u • v
      invFun := fun v => u⁻¹ • v
      left_inv := inv_smul_smul u
      right_inv := smul_inv_smul u
      map_add' := smul_add u }
  refine ⟨b.trans twist.toMultiplicative,?_⟩
  intro x v w hw
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (fixedAttachment R a) x
  obtain ⟨v,rfl⟩ := hf v
  let y := Multiplicative.ofAdd (act x v.toAdd)
  have hy : f y = w := by
    apply Subtype.ext
    rw [hw]
    change fixedProjection R a (jS y) =
      fixedProjection R a x * fixedProjection R a (jS v) * (fixedProjection R a x)⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    apply congrArg (fixedProjection R a)
    apply Subtype.ext
    exact hconj x v.toAdd
  rw [←hy]
  change u • (b (f y)).toAdd = markedQuotient R κ hκ u (fixedProjection R a x) •
    (u • (b (f v)).toAdd)
  rw [hbmap,hbmap,markedQuotient_projection]
  change u • p₀ (act x v.toAdd) = (u*κ x*u⁻¹) • (u • p₀ v.toAdd)
  rw [hproj]
  simp only [mul_smul,inv_smul_smul]

/-- The whole original core modulo its complete fixed attachment has natural
coordinates for the same selected symplectic marking, including its twist. -/
theorem natural_coordinates (hinner : K ⊔ pCore 2 H = ⊤) {a : Vertex R}
    (cv : AmbientVertexCover R (originalMovedSection h) n a)
    (hwhole : Q R a = U R a ⊔ fixedCore R a) (u : Sp cv.field.Carrier) :
    ∃ natural : layerImage R a (Q R a) ≃* Multiplicative (Vector cv.field.Carrier),
      ∀ (x : FixedQuotient R a) (v w : layerImage R a (Q R a)),
        (w : FixedQuotient R a) = x*v*x⁻¹ →
          (natural w).toAdd =
            markedQuotient R (coverQuotient h hinner cv)
              (coverQuotient_kernel h hinner cv) u x • (natural v).toAdd := by
  exact coordinates_of_cover (coverQuotient h hinner cv) (coverQuotient_kernel h hinner cv)
    u hwhole (fun x => (originalMovedSection h).space.toRepresentation (cv.quotient x))
    cv.embedding cv.range_eq
    (MovedSection.coverProjection (originalMovedSection h) cv.equiv).toLinearMap.toAddMonoidHom
    cv.cover.1 cv.kernel cv.conjugation (coverQuotient_projection h hinner cv)

/-- The ambient natural cover required by the whole-core construction exists
at every original-color vertex of the original radical. -/
theorem exists_ambient_cover {a : Vertex R} (ha : color R a = false) :
    Nonempty (AmbientVertexCover R (originalMovedSection h) n a) := by
  obtain ⟨E,hE,e,he,j,hj,hr,κ,hκ,hQ,hC,hL,hf,hs,hc,hp,hk⟩ :=
    h.ambient_initial_cover_at_vertex ha
  exact ⟨⟨E,hE,e,he,j,hj,hr,κ,hκ,hQ,hC,hL,hf,hs,hc,hp,hk⟩⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
