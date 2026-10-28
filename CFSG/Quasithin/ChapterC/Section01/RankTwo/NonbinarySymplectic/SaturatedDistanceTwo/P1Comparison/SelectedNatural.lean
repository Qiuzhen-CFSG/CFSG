module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThree

/-!
# Natural coordinates from an internally selected MS input

Choose a replacement omega cover once. Its acting-group
isomorphism, the component image quotient, and the restriction of K to the
replacement overgroup define a new Input on exactly K, R and n. All structural
fields are copied. The characteristic reduction therefore stays the same.
Positive distance makes the replacement component the entire core quotient,
so any edge marking for this selected input agrees with the chosen natural
actor on every element of the endpoint stabilizer.

Under whole-core collapse, the cover and the projection through the entire
fixed attachment have identical kernels and surjective images. Their quotient
comparison constructs the required natural coordinates on the literal tilde
core. Twisting these coordinates by the same inner conjugator used in
markedQuotient preserves all marking equations.

The final source application fills the natural fields of the existing
SourceEndgame, retaining its other geometric premises in the selected marking.
It returns n = 2 and hence cardinality four for the original field. It never
assumes cardinality four, and does not assert compatibility of the original
arbitrary quotient marking with the selected natural action.

Source: Meierfrankenfeld–Stellmacher, Pushing up weak BN-pairs of rank two,
(3.7), printed pp.876–877; natural cover convention (1.5)(ii).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison.Selected
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
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F) (d : CharacteristicReduction K R)
include h

def componentEquiv (E : BinaryField) (hE : E.degree = n)
    (e : ActionEquiv ((replacementMovedSection h d).action.comp (replacementComponent d).subtype)
      (binaryNatural (K := E.Carrier))) : replacementComponent d ≃* Sp E.Carrier :=
  e.groupEquiv.trans ((MulEquiv.subgroupCongr
    (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top (by
      rw [E.card_eq,hE]
      exact lt_of_lt_of_le (by decide : 2 < 2^2)
        (Nat.pow_le_pow_right (by decide) h.nonbinary)))).trans Subgroup.topEquiv)

def input (E : BinaryField) (hE : E.degree = n)
    (e : ActionEquiv ((replacementMovedSection h d).action.comp (replacementComponent d).subtype)
      (binaryNatural (K := E.Carrier))) : Input K R n E.Carrier where
  nonbinary := h.nonbinary
  field_card := E.card_eq.trans (congrArg (2^·) hE)
  sqtk := h.sqtk
  fitting := h.fitting
  component := h.component
  product := h.product
  radical := h.radical
  characteristic := h.characteristic
  quotientEquiv := (subgroupOfCoreQuotientEquiv (show K ≤ d.overgroup from le_sup_left)).symm.trans
    ((cComponentTwoCoreQuotientEquiv (replacement_component h d)).trans
      (componentEquiv h d E hE e))

@[simp] theorem componentProjection_input (E : BinaryField) (hE : E.degree = n)
    (e : ActionEquiv ((replacementMovedSection h d).action.comp (replacementComponent d).subtype)
      (binaryNatural (K := E.Carrier))) (k : K.subgroupOf d.overgroup) :
    componentProjection (input h d E hE e) (subgroupOfEquivOfLe le_sup_left k) =
      componentEquiv h d E hE e ((QuotientGroup.mk' (pCore 2 d.overgroup)).subgroupMap
        (K.subgroupOf d.overgroup) k) := by
  change componentEquiv h d E hE e (cComponentTwoCoreQuotientEquiv (replacement_component h d)
    ((subgroupOfCoreQuotientEquiv le_sup_left).symm
      (QuotientGroup.mk' (pCore 2 K) (subgroupOfEquivOfLe le_sup_left k)))) = _
  rw [←subgroupOfCoreQuotientEquiv_mk le_sup_left k,MulEquiv.symm_apply_apply]
  rfl

theorem component_eq_top (g : Geometry d.radical) (hb : 0 < g.b d.radical) :
    replacementComponent d = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
    (replacement_inner_of_positive h d g hb)
  rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q = ⊥ from
    (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
  exact hh

def projection (E : BinaryField) (hE : E.degree = n)
    (e : ActionEquiv ((replacementMovedSection h d).action.comp (replacementComponent d).subtype)
      (binaryNatural (K := E.Carrier))) (g : Geometry d.radical) (hb : 0 < g.b d.radical) :
    d.overgroup →* Sp E.Carrier :=
  (componentEquiv h d E hE e).toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 d.overgroup)).codRestrict (replacementComponent d)
      (fun _ => component_eq_top h d g hb ▸ mem_top _))

theorem edge_projection (E : BinaryField) (hE : E.degree = n)
    (e : ActionEquiv ((replacementMovedSection h d).action.comp (replacementComponent d).subtype)
      (binaryNatural (K := E.Carrier))) (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    {a t : Vertex d.radical} (c : EdgeMarking (input h d E hE e) d a t)
    (x : d.overgroup) :
    c.quotient ⟨c.embedding x,c.range_eq ▸ (show c.embedding x ∈ c.embedding.range from ⟨x,rfl⟩)⟩ =
      projection h d E hE e g hb x := by
  let i : d.overgroup →* stabilizer d.radical a := c.embedding.codRestrict _
    (fun x => c.range_eq ▸ (show c.embedding x ∈ c.embedding.range from ⟨x,rfl⟩))
  change (c.quotient.comp i) x = projection h d E hE e g hb x
  have hx : x ∈ K.subgroupOf d.overgroup ⊔ pCore 2 d.overgroup :=
    (replacement_inner_of_positive h d g hb).symm ▸ mem_top x
  obtain ⟨k,hk,q,hq,rfl⟩ := mem_sup_of_normal_right.mp hx
  rw [map_mul,map_mul]
  have hkc : (c.quotient.comp i) k = projection h d E hE e g hb k := by
    exact (c.component_equation ⟨k,hk⟩).trans (componentProjection_input h d E hE e ⟨k,hk⟩)
  have hq₁ : (c.quotient.comp i) q = 1 := by
    have he : c.quotient.ker = (Q d.radical a).subgroupOf (stabilizer d.radical a) := by
      rw [←c.kernel,subgroupOf_map_subtype_eq]
    change i q ∈ c.quotient.ker
    rw [he]
    exact c.core_eq ▸ mem_map_of_mem c.embedding hq
  have hq₂ : projection h d E hE e g hb q = 1 := by
    apply (componentEquiv h d E hE e).map_eq_one_iff.mpr
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr hq
  rw [hkc,hq₁,hq₂]


omit [Finite H] [Finite F] [CharP F 2] in
private theorem coordinates_of_cover
    {W : Type*} [AddCommGroup W] {a t : Vertex d.radical}
    (c : EdgeMarking h d a t) (u : Sp F)
    (hwhole : Q d.radical a = U d.radical a ⊔ fixedCore d.radical a)
    (act : stabilizer d.radical a → W → W)
    (j : Multiplicative W →* FreeAmalgam d.radical) (hjr : j.range = U d.radical a)
    (p₀ : W →+ Vector F) (hp₀ : Function.Surjective p₀)
    (hker : ∀ v : W, p₀ v = 0 ↔
      j (Multiplicative.ofAdd v) ∈ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)))
    (hconj : ∀ (x : stabilizer d.radical a) (v : W),
      j (Multiplicative.ofAdd (act x v)) = x.val*j (Multiplicative.ofAdd v)*x.val⁻¹)
    (hproj : ∀ (x : stabilizer d.radical a) (v : W), p₀ (act x v) = c.quotient x • p₀ v) :
    ∃ natural : layerImage d a (Q d.radical a) ≃* Multiplicative (Vector F),
      ∀ (x : FixedQuotient d a) (v w : layerImage d a (Q d.radical a)),
        (w : FixedQuotient d a) = x*v*x⁻¹ →
          (natural w).toAdd = markedQuotient h d c u x • (natural v).toAdd := by
  have hUQ : U d.radical a ≤ Q d.radical a := le_sup_left.trans hwhole.symm.le
  have hQS : Q d.radical a ≤ stabilizer d.radical a := fun _ hx => hx.1
  let jS : Multiplicative W →* stabilizer d.radical a :=
    j.codRestrict _ (fun w => hQS (hUQ (hjr ▸ ⟨w,rfl⟩)))
  have hjSr : jS.range = (U d.radical a).subgroupOf (stabilizer d.radical a) := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      exact hjr ▸ ⟨w,rfl⟩
    · intro hx
      obtain ⟨w,hw⟩ := (hjr.symm ▸ hx : x.val ∈ j.range)
      exact ⟨w,Subtype.ext hw⟩
  have himage : layerImage d a (Q d.radical a) = layerImage d a (U d.radical a) := by
    change ((Q d.radical a).subgroupOf _).map _ = _
    rw [hwhole,subgroupOf_sup (hUQ.trans hQS) ((show fixedCore d.radical a ≤ Q d.radical a from inf_le_left).trans hQS),Subgroup.map_sup]
    have hzero : layerImage d a (fixedCore d.radical a) = ⊥ := QuotientGroup.map_mk'_self _
    change layerImage d a (U d.radical a) ⊔ layerImage d a (fixedCore d.radical a) = _
    rw [hzero,sup_bot_eq]
  let f₀ := (fixedProjection d a).comp jS
  have hfr : f₀.range = layerImage d a (Q d.radical a) := by
    rw [MonoidHom.range_comp,hjSr]
    exact himage.symm
  let f : Multiplicative W →* layerImage d a (Q d.radical a) :=
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
    change fixedProjection d a (jS w) = 1 ↔ p₀ w.toAdd = 0
    rw [show fixedProjection d a (jS w) = 1 ↔ jS w ∈ fixedAttachment d a from
      QuotientGroup.eq_one_iff (jS w)]
    change (j w ∈ Q d.radical a ∧ j w ∈ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) ↔ _
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
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (fixedAttachment d a) x
  obtain ⟨v,rfl⟩ := hf v
  let y := Multiplicative.ofAdd (act x v.toAdd)
  have hy : f y = w := by
    apply Subtype.ext
    rw [hw]
    change fixedProjection d a (jS y) =
      fixedProjection d a x * fixedProjection d a (jS v) * (fixedProjection d a x)⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    apply congrArg (fixedProjection d a)
    apply Subtype.ext
    exact hconj x v.toAdd
  rw [←hy]
  change u • (b (f y)).toAdd = markedQuotient h d c u (fixedProjection d a x) •
    (u • (b (f v)).toAdd)
  rw [hbmap,hbmap,markedQuotient_projection]
  change u • p₀ (act x v.toAdd) = (u*c.quotient x*u⁻¹) • (u • p₀ v.toAdd)
  rw [hproj]
  simp only [mul_smul,inv_smul_smul]

/-- The selected marking acts naturally on the whole core after its full
fixed attachment is removed. Whole-core collapse is the geometric premise. -/
theorem natural_coordinates (E : BinaryField) (hE : E.degree = n)
    (e : ActionEquiv ((replacementMovedSection h d).action.comp (replacementComponent d).subtype)
      (binaryNatural (K := E.Carrier)))
    (he : IsCover (MovedSection.coverProjection (replacementMovedSection h d) e))
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false) (hat : Adjacent d.radical a t)
    (c : EdgeMarking (input h d E hE e) d a t)
    (hwhole : Q d.radical a = U d.radical a ⊔ fixedCore d.radical a)
    (u : Sp E.Carrier) :
    ∃ natural : layerImage d a (Q d.radical a) ≃* Multiplicative (Vector E.Carrier),
      ∀ (x : FixedQuotient d a) (v w : layerImage d a (Q d.radical a)),
        (w : FixedQuotient d a) = x*v*x⁻¹ →
          (natural w).toAdd = markedQuotient (input h d E hE e) d c u x • (natural v).toAdd := by
  let := replacementComponent_normal h d
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let : ((K.subgroupOf d.overgroup).map q).Normal := replacementComponent_normal h d
  let hq := QuotientGroup.mk'_surjective (pCore 2 d.overgroup)
  let hk := (QuotientGroup.ker_mk' _).trans (replacement_centralOmega_centralizer h d).symm
  let s := replacementMovedSection h d
  let j := c.embedding.comp (ElementaryMovedCover.embedding
    (omegaCenterIn (pCore 2 d.overgroup)) (K.subgroupOf d.overgroup) q hq hk)
  have hjr : j.range = U d.radical a := by
    dsimp only [j]
    rw [MonoidHom.range_comp,ElementaryMovedCover.embedding_range,map_commutator,c.residual_eq]
    have hx : (omegaCenterIn (pCore 2 d.overgroup)).map c.embedding = X d.radical a := by
      change (omegaCenter (pCore 2 d.overgroup)).map c.embedding = omegaCenter (Q d.radical a)
      rw [←c.core_eq,omegaCenter_map _ _ c.injective]
    rw [hx,X_eq_Z_of_core_decomposition (input h d E hE e) d g hb ha hat c hwhole]
    rfl
  obtain ⟨_,_,_,hker⟩ := ElementaryMovedCover.exists_conjugationActor
    (omegaCenterIn (pCore 2 d.overgroup)) (K.subgroupOf d.overgroup) q hq hk
    c.embedding c.injective (Ltilde d.radical a) c.residual_eq e
  let κ := ElementaryMovedCover.embeddedQuotient q c.embedding c.injective
    (stabilizer d.radical a) c.range_eq
  apply coordinates_of_cover (input h d E hE e) d c u hwhole
    (fun x => s.space.toRepresentation (κ x)) j hjr
    (MovedSection.coverProjection s e).toLinearMap.toAddMonoidHom he.1 hker
  · exact fun x v => ElementaryMovedCover.embedded_ambient_conjugate
      (omegaCenterIn (pCore 2 d.overgroup)) (K.subgroupOf d.overgroup) q hq hk
      c.embedding c.injective _ c.range_eq x v
  · intro x v
    let k : replacementComponent d := ⟨κ x,component_eq_top h d g hb ▸ mem_top _⟩
    have heq : componentEquiv h d E hE e k = c.quotient x := by
      let vtx := (MonoidHom.ofInjective c.injective).trans (MulEquiv.subgroupCongr c.range_eq)
      have hh := edge_projection h d E hE e g hb c (vtx.symm x)
      change c.quotient (vtx (vtx.symm x)) = componentEquiv h d E hE e k at hh
      rw [vtx.apply_symm_apply] at hh
      exact hh.symm
    change MovedSection.coverProjection s e (s.space.toRepresentation (κ x) v) = _
    rw [MovedSection.coverProjection_ambient]
    have hh := MovedSection.ambientAction_component s e k (MovedSection.coverProjection s e v)
    change _ = componentEquiv h d E hE e k • (MovedSection.coverProjection s e v) at hh
    change _ = c.quotient x • MovedSection.coverProjection s e v
    rw [←heq]
    exact hh

/-- One certified choice of the replacement natural cover. This stores only
already constructed data, with no additional source assumptions. -/
structure Selection where
  field : BinaryField
  degree : field.degree = n
  equiv : ActionEquiv ((replacementMovedSection h d).action.comp (replacementComponent d).subtype)
    (binaryNatural (K := field.Carrier))
  cover : IsCover (MovedSection.coverProjection (replacementMovedSection h d) equiv)

/-- Choose once, before forming any endpoint marking. -/
def select : Selection h d := Classical.choice <| by
  obtain ⟨E,hE,e,he⟩ := replacement_centralOmega_initial_cover h d
  exact ⟨⟨E,hE,e,he⟩⟩


/-- The internally selected input preserves the original subgroups and degree. -/
@[expose] def selectedInput : Input K R n (select h d).field.Carrier :=
  input h d (select h d).field (select h d).degree (select h d).equiv

/-- The chosen input supplies a natural marking of the literal full-core image
for every selected edge and inner conjugation, assuming whole-core collapse. -/
theorem selected_natural_coordinates
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false) (hat : Adjacent d.radical a t)
    (c : EdgeMarking (selectedInput h d) d a t)
    (hwhole : Q d.radical a = U d.radical a ⊔ fixedCore d.radical a)
    (u : Sp (select h d).field.Carrier) :
    ∃ natural : layerImage d a (Q d.radical a) ≃* Multiplicative (Vector (select h d).field.Carrier),
      ∀ (x : FixedQuotient d a) (v w : layerImage d a (Q d.radical a)),
        (w : FixedQuotient d a) = x*v*x⁻¹ →
          (natural w).toAdd = markedQuotient (selectedInput h d) d c u x • (natural v).toAdd :=
  natural_coordinates h d (select h d).field (select h d).degree (select h d).equiv
    (select h d).cover g hb ha hat c hwhole u

/-- Select the replacement cover once. Every edge and natural coordinate
construction below uses the induced marking of the original component quotient. -/
theorem exists_input_coordinates (g : Geometry d.radical) (hb : 0 < g.b d.radical) :
    ∃ (E : BinaryField) (hE : E.degree = n),
      ∃ e : ActionEquiv ((replacementMovedSection h d).action.comp (replacementComponent d).subtype)
          (binaryNatural (K := E.Carrier)),
        IsCover (MovedSection.coverProjection (replacementMovedSection h d) e) ∧
        ∀ (a t : Vertex d.radical) (_ha : color d.radical a = false)
          (_hat : Adjacent d.radical a t),
          ∃ c : EdgeMarking (input h d E hE e) d a t,
            Q d.radical a = U d.radical a ⊔ fixedCore d.radical a →
            ∀ u : Sp E.Carrier,
              ∃ natural : layerImage d a (Q d.radical a) ≃* Multiplicative (Vector E.Carrier),
                ∀ (x : FixedQuotient d a) (v w : layerImage d a (Q d.radical a)),
                  (w : FixedQuotient d a) = x*v*x⁻¹ →
                    (natural w).toAdd =
                      markedQuotient (input h d E hE e) d c u x • (natural v).toAdd := by
  let s := select h d
  refine ⟨s.field,s.degree,s.equiv,s.cover,?_⟩
  intro a t ha hat
  obtain ⟨c⟩ := exists_edgeMarking (input h d s.field s.degree s.equiv) d g hb ha hat
  exact ⟨c,fun hwhole u => natural_coordinates h d s.field s.degree s.equiv s.cover
    g hb ha hat c hwhole u⟩

/-- Discharge the two natural-coordinate fields of the existing endgame
from the selected cover. Every remaining geometric hypothesis uses the same
selected edge quotient and inner conjugation. The conclusion returns to the
original field using its unchanged degree. -/
theorem degree_and_original_field_of_geometry (E : BinaryField) (hE : E.degree = n)
    (e : ActionEquiv ((replacementMovedSection h d).action.comp (replacementComponent d).subtype)
      (binaryNatural (K := E.Carrier)))
    (he : IsCover (MovedSection.coverProjection (replacementMovedSection h d) e))
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking (input h d E hE e) d a t)
    (c' : EdgeMarking (input h d E hE e) d z t) (u : Sp E.Carrier)
    (hwhole : Q d.radical a = U d.radical a ⊔ fixedCore d.radical a)
    (hroot : (layerImage d a (Z d.radical z)).map (markedQuotient (input h d E hE e) d c u) =
      RootSubgroup.group 0)
    (hopposite : (stabilizer (point E.Carrier)).comap (markedQuotient (input h d E hE e) d c u) ≤
      normalizer (layerImage d a (Z d.radical z) : Set (FixedQuotient d a)))
    (hintersection : (layerImage d a (Z d.radical z)).relIndex (layerImage d a (Z d.radical a)) = 2^n)
    (hintercentral : layerImage d a (Z d.radical a) ⊓ layerImage d a (Z d.radical z) ≤
      relativeCentralizer (input h d E hE e) d (z := z) c u)
    (hcentralorder : (layerImage d a (Z d.radical a) ⊓ layerImage d a (Z d.radical z)).relIndex
      (relativeCentralizer (input h d E hE e) d (z := z) c u) = 2^n)
    (hcentralnorm : (stabilizer (point E.Carrier)).comap (markedQuotient (input h d E hE e) d c u) ≤
      normalizer (relativeCentralizer (input h d E hE e) d (z := z) c u : Set (FixedQuotient d a)))
    (hprojection : (layerImage d a (Z d.radical a)).relIndex
      (relativeCentralizer (input h d E hE e) d (z := z) c u ⊔ layerImage d a (Z d.radical a)) = 2^n)
    (hdisjoint : Disjoint (fixedCore d.radical a) (U d.radical z))
    (hcommutator : Nat.card (⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) = 2^n)
    (hstrict : 2^n < Nat.card (⁅Z d.radical z,markedPointCore (input h d E hE e) d c u ⊓
      Q d.radical t⁆ : Subgroup (FreeAmalgam d.radical))) : n = 2 ∧ Nat.card F = 4 := by
  obtain ⟨natural,hconj⟩ := natural_coordinates h d E hE e he g (by omega)
    path.start_color hat c hwhole u
  let s : SourceEndgame (input h d E hE e) d (z := z) c u :=
    { whole_core := hwhole
      natural := natural
      natural_conjugation := hconj
      root_image := hroot
      opposite_normalized := hopposite
      intersection_index := hintersection
      intersection_centralizes := hintercentral
      centralizer_order := hcentralorder
      centralizer_normalized := hcentralnorm
      projection_index := hprojection
      fixed_disjoint := hdisjoint
      commutator_order := hcommutator
      strict_movement := hstrict }
  have hn := s.degree_eq_two path hb hat hzt c'
  exact ⟨hn,by rw [h.field_card,hn]; rfl⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison.Selected
