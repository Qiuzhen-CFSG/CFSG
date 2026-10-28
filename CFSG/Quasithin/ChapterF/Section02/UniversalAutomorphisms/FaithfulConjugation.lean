module
public import CFSG.Quasithin.ChapterF.Section02.UniversalAutomorphisms
import all CFSG.Quasithin.ChapterF.Section02
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Faithful stabilizers and conjugation of subgroup amalgams

This extension proves Aschbacher--Smith, *The Classification of Quasithin
Groups*, §F.2.8(5) and §F.2.10 (printed pp. 266–268).

For a faithful completion, restriction identifies the automorphisms preserving
each vertex image with the stabilizer of its completion class. The inverse is
the previously constructed descent representation `piMinus`.

For nested subgroup amalgams, `YAmalgam.NormalIn` records vertex containment and
normality. A least index lets its larger vertex conjugate every smaller vertex;
transport to the subgroup types gives an automorphism of the diagram. The
kernel is the intersection of centralizers. On the smaller least vertex, this
action is conjugation inside every vertex, hence becomes inner in every
completion. This proves both universal conjugation and the descent formula.

The internal import of `Section02` is intentional: this proof extension checks
the subgroup diagram's inclusion maps without changing that module's public
boundary. Public evaluation lemmas here keep these details out of consumers.
-/

public section
namespace CFSG.Quasithin.ChapterF
universe u v w
namespace AmalgamCompletion
variable {D : Type u} [PartialOrder D] {X : D → Type v} [∀ d, Group (X d)]
variable {A : AmalgamDiagram D X} {G : Type w} [Group G]
variable (μ : AmalgamCompletion A G)

/-- The subgroup of automorphisms preserving each vertex image. -/
def imageStabilizer : Subgroup (MulAut G) where
  carrier := {b | ∀ d x, b x ∈ (μ.map d).range ↔ x ∈ (μ.map d).range}
  one_mem' := by intro d x; rfl
  mul_mem' := by intro a b ha hb d x; exact (ha d (b x)).trans (hb d x)
  inv_mem' := by
    intro a ha d x
    have h := ha d (a.symm x)
    simpa only [MulAut.inv_apply, MulEquiv.apply_symm_apply] using h.symm

/-- Membership is precisely setwise preservation of every vertex image. -/
theorem mem_imageStabilizer_iff (b : MulAut G) :
    b ∈ μ.imageStabilizer ↔ ∀ d, (μ.image d).map b.toMonoidHom = μ.image d := by
  constructor
  · intro hb d
    rw [μ.image_eq_map]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hb d y).2 hy
    · intro hx
      exact ⟨b.symm x, (hb d (b.symm x)).1 (by simpa using hx), b.apply_symm_apply x⟩
  · intro hb d x
    simp only [μ.image_eq_map] at hb
    constructor
    · intro hx
      rw [← hb d] at hx
      obtain ⟨y, hy, h⟩ := hx
      exact b.injective h ▸ hy
    · intro hx
      rw [← hb d]
      exact ⟨x, hx, rfl⟩

private def imageAut (b : μ.imageStabilizer) (d : D) : MulAut (μ.map d).range where
  toFun x := ⟨b.val x, (b.property d x).2 x.property⟩
  invFun x := ⟨b.val.symm x, (b.property d (b.val.symm x)).1 (by simp only [MulEquiv.apply_symm_apply]; exact x.property)⟩
  left_inv x := by ext; exact b.val.symm_apply_apply x
  right_inv x := by ext; exact b.val.apply_symm_apply x
  map_mul' x y := by ext; exact b.val.map_mul x y

private noncomputable def restrictVertex (hμ : μ.Faithful)
    (b : μ.imageStabilizer) (d : D) : MulAut (X d) :=
  let e := MonoidHom.ofInjective (hμ d)
  (e.trans (μ.imageAut b d)).trans e.symm

private theorem restrictVertex_spec (hμ : μ.Faithful)
    (b : μ.imageStabilizer) (d : D) (x : X d) :
    μ.map d (μ.restrictVertex hμ b d x) = b.val (μ.map d x) := by
  exact MonoidHom.apply_ofInjective_symm (hμ d) _

/-- F.2.8(5): restriction of an image-preserving automorphism to the diagram. -/
noncomputable def restriction (hμ : μ.Faithful) :
    μ.imageStabilizer →* AmalgamAutomorphism A where
  toFun b :=
    { map := μ.restrictVertex hμ b
      commutes := by
        intro d e h
        ext x
        apply hμ e
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          restrictVertex_spec, compatible_apply] }
  map_one' := by
    apply AmalgamAutomorphism.ext
    intro d x
    apply hμ d
    exact μ.restrictVertex_spec hμ 1 d x
  map_mul' a b := by
    apply AmalgamAutomorphism.ext
    intro d x
    apply hμ d
    change μ.map d (μ.restrictVertex hμ (a * b) d x) =
      μ.map d (μ.restrictVertex hμ a d (μ.restrictVertex hμ b d x))
    simp only [restrictVertex_spec]
    rfl

@[simp] theorem restriction_map (hμ : μ.Faithful)
    (b : μ.imageStabilizer) (d : D) (x : X d) :
    μ.map d ((μ.restriction hμ b).map d x) = b.val (μ.map d x) :=
  μ.restrictVertex_spec hμ b d x
end AmalgamCompletion

namespace UniversalCompletion
variable {D : Type u} [PartialOrder D] {X : D → Type v} [∀ d, Group (X d)]
variable {A : AmalgamDiagram D X} {G U : Type w} [Group G] [Group U]
variable (ucomp : UniversalCompletion A U) (μ : AmalgamCompletion A G)

theorem restriction_mem_kernelStabilizer (hμ : μ.Faithful) (b : μ.imageStabilizer) :
    μ.restriction hμ b ∈ ucomp.kernelStabilizer μ :=
  ucomp.mem_kernelStabilizer_of_compatible μ _ b.val
    (fun d x => (μ.restriction_map hμ b d x).symm)

/-- Restriction with codomain the stabilizer of the completion class. -/
noncomputable def restrictionToStabilizer (hμ : μ.Faithful) :
    μ.imageStabilizer →* ucomp.kernelStabilizer μ :=
  (μ.restriction hμ).codRestrict _ (ucomp.restriction_mem_kernelStabilizer μ hμ)

@[simp] theorem restrictionToStabilizer_apply (hμ : μ.Faithful) (b : μ.imageStabilizer) :
    (ucomp.restrictionToStabilizer μ hμ b).val = μ.restriction hμ b := by rfl

theorem piMinus_mem_imageStabilizer (a : ucomp.kernelStabilizer μ) :
    ucomp.piMinus μ a ∈ μ.imageStabilizer := by
  intro d x
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(a.val.map d).symm y, ?_⟩
    apply (ucomp.piMinus μ a).injective
    rw [piMinus_map, MulEquiv.apply_symm_apply, hy]
  · rintro ⟨y, rfl⟩
    exact ⟨a.val.map d y, (ucomp.piMinus_map μ a d y).symm⟩

/-- Descent with codomain the automorphisms preserving the vertex images. -/
noncomputable def piMinusToImageStabilizer :
    ucomp.kernelStabilizer μ →* μ.imageStabilizer :=
  (ucomp.piMinus μ).codRestrict _ (ucomp.piMinus_mem_imageStabilizer μ)

@[simp] theorem piMinusToImageStabilizer_apply (a : ucomp.kernelStabilizer μ) :
    (ucomp.piMinusToImageStabilizer μ a).val = ucomp.piMinus μ a := by rfl

@[simp] theorem piMinus_restriction (hμ : μ.Faithful) (b : μ.imageStabilizer) :
    ucomp.piMinus μ (ucomp.restrictionToStabilizer μ hμ b) = b.val :=
  ucomp.piMinus_eq_of_compatible μ _ b.val
    (fun d x => (μ.restriction_map hμ b d x).symm)

@[simp] theorem restriction_piMinus (hμ : μ.Faithful) (a : ucomp.kernelStabilizer μ) :
    ucomp.restrictionToStabilizer μ hμ (ucomp.piMinusToImageStabilizer μ a) = a := by
  apply ucomp.piMinus_injective μ hμ
  exact ucomp.piMinus_restriction μ hμ _

/-- F.2.8(5): restriction and descent are mutually inverse group isomorphisms. -/
noncomputable def faithfulStabilizerEquiv (hμ : μ.Faithful) :
    μ.imageStabilizer ≃* ucomp.kernelStabilizer μ where
  toFun := ucomp.restrictionToStabilizer μ hμ
  invFun := ucomp.piMinusToImageStabilizer μ
  left_inv b := by apply Subtype.ext; exact ucomp.piMinus_restriction μ hμ b
  right_inv := ucomp.restriction_piMinus μ hμ
  map_mul' := (ucomp.restrictionToStabilizer μ hμ).map_mul

@[simp] theorem faithfulStabilizerEquiv_apply (hμ : μ.Faithful) (b : μ.imageStabilizer) :
    (ucomp.faithfulStabilizerEquiv μ hμ b).val = μ.restriction hμ b  := by rfl

@[simp] theorem faithfulStabilizerEquiv_symm_apply (hμ : μ.Faithful)
    (a : ucomp.kernelStabilizer μ) :
    ((ucomp.faithfulStabilizerEquiv μ hμ).symm a).val = ucomp.piMinus μ a  := by rfl
/-- The restriction representation has exactly the completion stabilizer as image. -/
theorem restriction_range (hμ : μ.Faithful) :
    (μ.restriction hμ).range = ucomp.kernelStabilizer μ := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact ucomp.restriction_mem_kernelStabilizer μ hμ b
  · intro ha
    refine ⟨(ucomp.faithfulStabilizerEquiv μ hμ).symm ⟨a, ha⟩, ?_⟩
    exact congrArg Subtype.val ((ucomp.faithfulStabilizerEquiv μ hμ).apply_symm_apply ⟨a, ha⟩)

/-- The descended representation has exactly the vertex-image stabilizer as image. -/
theorem piMinus_range (hμ : μ.Faithful) :
    (ucomp.piMinus μ).range = μ.imageStabilizer := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact ucomp.piMinus_mem_imageStabilizer μ a
  · intro hb
    exact ⟨ucomp.restrictionToStabilizer μ hμ ⟨b, hb⟩,
      ucomp.piMinus_restriction μ hμ ⟨b, hb⟩⟩

end UniversalCompletion

namespace YAmalgam
variable {D : Type u} [PartialOrder D] {Y : Type v} [Group Y]
variable {X : Subgroup Y} (α : YAmalgam D X) (γ : YAmalgam D Y)

/-- Nested subgroup amalgams with each smaller vertex normal in the larger one. -/
structure NormalIn : Prop where
  le : ∀ d, (α.subgroup d).map X.subtype ≤ γ.subgroup d
  normal : ∀ d, ((α.subgroup d).map X.subtype |>.subgroupOf (γ.subgroup d)).Normal

namespace NormalIn
variable {α γ} (h : α.NormalIn γ) {e : D} (he : ∀ d, e ≤ d)
include h he

private theorem mem_vertex_normalizer (y : γ.subgroup e) (d : D) :
    (y : Y) ∈ Subgroup.normalizer (((α.subgroup d).map X.subtype : Subgroup Y) : Set Y) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (h.le d)).mp (h.normal d)
    (γ.le (he d) y.property)

private noncomputable def conjugationVertex (y : γ.subgroup e) (d : D) :
    MulAut (α.subgroup d) :=
  let f := (α.subgroup d).equivMapOfInjective X.subtype Subtype.val_injective
  let b := ((α.subgroup d).map X.subtype).normalizerMonoidHom
    ⟨y.val, h.mem_vertex_normalizer he y d⟩
  (f.trans b).trans f.symm

private theorem conjugationVertex_apply (y : γ.subgroup e) (d : D)
    (x : α.subgroup d) :
    (((h.conjugationVertex he y d x : α.subgroup d) : X) : Y) =
      (y : Y) * (x : X) * (y : Y)⁻¹ := by
  let f := (α.subgroup d).equivMapOfInjective X.subtype Subtype.val_injective
  let b := ((α.subgroup d).map X.subtype).normalizerMonoidHom
    ⟨y.val, h.mem_vertex_normalizer he y d⟩
  have hf := congrArg (fun z : (α.subgroup d).map X.subtype => (z : Y))
    (f.apply_symm_apply (b (f x)))
  exact hf

/-- F.2.10(1): conjugation by the least vertex of the larger amalgam. -/
noncomputable def conjugation : γ.subgroup e →* AmalgamAutomorphism α.diagram where
  toFun y :=
    { map := h.conjugationVertex he y
      commutes := by
        intro d f hdf
        ext x
        change (((h.conjugationVertex he y f (α.diagram.map hdf x) : α.subgroup f) : X) : Y) =
          (((h.conjugationVertex he y d x : α.subgroup d) : X) : Y)
        rw [conjugationVertex_apply, conjugationVertex_apply]
        rfl }
  map_one' := by
    apply AmalgamAutomorphism.ext
    intro d x
    apply Subtype.ext
    apply Subtype.ext
    simpa only [Subgroup.coe_one, one_mul, inv_one, mul_one,
      AmalgamAutomorphism.one_map_apply] using
      h.conjugationVertex_apply he 1 d x
  map_mul' a b := by
    apply AmalgamAutomorphism.ext
    intro d x
    apply Subtype.ext
    apply Subtype.ext
    change (((h.conjugationVertex he (a * b) d x : α.subgroup d) : X) : Y) =
      (((h.conjugationVertex he a d (h.conjugationVertex he b d x) : α.subgroup d) : X) : Y)
    simp only [conjugationVertex_apply, Subgroup.coe_mul, mul_inv_rev, mul_assoc]

@[simp] theorem conjugation_apply (y : γ.subgroup e) (d : D) (x : α.subgroup d) :
    ((((h.conjugation he y).map d x : α.subgroup d) : X) : Y) =
      (y : Y) * (x : X) * (y : Y)⁻¹ := h.conjugationVertex_apply he y d x

/-- F.2.10(2): the kernel is the intersection of the vertex centralizers in `Y_e`. -/
theorem conjugation_ker :
    (h.conjugation he).ker = ⨅ d,
      (Subgroup.centralizer (((α.subgroup d).map X.subtype : Subgroup Y) : Set Y)).comap
        (γ.subgroup e).subtype := by
  ext y
  simp only [MonoidHom.mem_ker, Subgroup.mem_iInf, Subgroup.mem_comap,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro hy d z hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hf := congrArg (fun a : AmalgamAutomorphism α.diagram =>
      (((a.map d ⟨x, hx⟩ : α.subgroup d) : X) : Y)) hy
    rw [conjugation_apply] at hf
    change (y : Y) * (x : Y) * (y : Y)⁻¹ = (x : Y) at hf
    exact ((mul_inv_eq_iff_eq_mul).mp hf).symm
  · intro hy
    apply AmalgamAutomorphism.ext
    intro d x
    apply Subtype.ext
    apply Subtype.ext
    rw [conjugation_apply]
    change (y : Y) * (x : X) * (y : Y)⁻¹ = (x : X)
    exact mul_inv_eq_iff_eq_mul.mpr (hy d (x : X) ⟨x, x.property, rfl⟩).symm

/-- The inclusion of the least smaller vertex in the least larger vertex. -/
def leastInclusion : α.subgroup e →* γ.subgroup e where
  toFun x := ⟨(x : X), h.le e ⟨x, x.property, rfl⟩⟩
  map_one' := by rfl
  map_mul' _ _ := by rfl

omit he in
@[simp] theorem leastInclusion_apply (x : α.subgroup e) :
    (h.leastInclusion x : Y) = (x : X) := by rfl

/-- The conjugation action of `X_e`, viewed inside the action of `Y_e`. -/
noncomputable def innerConjugation : α.subgroup e →* AmalgamAutomorphism α.diagram :=
  (h.conjugation he).comp h.leastInclusion

@[simp] theorem innerConjugation_apply (x : α.subgroup e) :
    h.innerConjugation he x = h.conjugation he (h.leastInclusion x) := by rfl

/-- On every vertex, conjugation by `X_e` is computed inside that vertex. -/
theorem innerConjugation_map (x : α.subgroup e) (d : D) (z : α.subgroup d) :
    (h.innerConjugation he x).map d z =
      α.diagram.map (he d) x * z * (α.diagram.map (he d) x)⁻¹ := by
  apply Subtype.ext
  apply Subtype.ext
  exact h.conjugation_apply he (h.leastInclusion x) d z

/-- Conjugation compatibility holds in every completion, without faithfulness. -/
theorem innerConjugation_compatible {G : Type w} [Group G]
    (μ : AmalgamCompletion α.diagram G) (x : α.subgroup e) (d : D)
    (z : α.subgroup d) :
    conjugationHom (μ.map e x) (μ.map d z) =
      μ.map d ((h.innerConjugation he x).map d z) := by
  rw [innerConjugation_map, map_mul, map_mul, map_inv, μ.compatible_apply]
  exact conjugationHom_apply _ _

/-- F.2.10(3): the universal action of `X_e` consists of inner automorphisms. -/
theorem piHat_innerConjugation {U : Type w} [Group U]
    (ucomp : UniversalCompletion α.diagram U) (x : α.subgroup e) :
    ucomp.piHat (h.innerConjugation he x) = conjugationHom (ucomp.completion.map e x) := by
  apply MulEquiv.toMonoidHom_injective
  apply ucomp.completion.hom_ext
  intro d z
  simpa only [MulEquiv.coe_toMonoidHom, UniversalCompletion.piHat_map] using
    (h.innerConjugation_compatible he ucomp.completion x d z).symm

/-- F.2.10(4), kernel form: `X_e` stabilizes every completion class. -/
theorem innerConjugation_mem_kernelStabilizer {U G : Type w} [Group U] [Group G]
    (ucomp : UniversalCompletion α.diagram U) (μ : AmalgamCompletion α.diagram G)
    (x : α.subgroup e) : h.innerConjugation he x ∈ ucomp.kernelStabilizer μ :=
  ucomp.mem_kernelStabilizer_of_compatible μ _ (conjugationHom (μ.map e x))
    (h.innerConjugation_compatible he μ x)

/-- F.2.10(4), expressed as equivalence of completions. -/
theorem innerConjugation_act_equivalent {U G : Type w} [Group U] [Group G]
    (ucomp : UniversalCompletion α.diagram U) (μ : AmalgamCompletion α.diagram G)
    (x : α.subgroup e) :
    Nonempty (CompletionEquivalence ((h.innerConjugation he x).act μ) μ) :=
  (ucomp.mem_kernelStabilizer_iff μ _).mp (h.innerConjugation_mem_kernelStabilizer he ucomp μ x)

/-- The action of `X_e` with codomain the stabilizer of a completion class. -/
noncomputable def innerConjugationToStabilizer {U G : Type w} [Group U] [Group G]
    (ucomp : UniversalCompletion α.diagram U) (μ : AmalgamCompletion α.diagram G) :
    α.subgroup e →* ucomp.kernelStabilizer μ :=
  (h.innerConjugation he).codRestrict _ (h.innerConjugation_mem_kernelStabilizer he ucomp μ)

@[simp] theorem innerConjugationToStabilizer_apply {U G : Type w} [Group U] [Group G]
    (ucomp : UniversalCompletion α.diagram U) (μ : AmalgamCompletion α.diagram G)
    (x : α.subgroup e) :
    (h.innerConjugationToStabilizer he ucomp μ x).val = h.innerConjugation he x := by rfl

/-- F.2.10(5): descent agrees with conjugation by the image of the least vertex.
The formula in fact does not require the completion to be faithful. -/
theorem piMinus_innerConjugation {U G : Type w} [Group U] [Group G]
    (ucomp : UniversalCompletion α.diagram U) (μ : AmalgamCompletion α.diagram G)
    (x : α.subgroup e) :
    ucomp.piMinus μ (h.innerConjugationToStabilizer he ucomp μ x) =
      conjugationHom (μ.map e x) :=
  ucomp.piMinus_eq_of_compatible μ _ _ (h.innerConjugation_compatible he μ x)

end NormalIn
end YAmalgam
end CFSG.Quasithin.ChapterF
