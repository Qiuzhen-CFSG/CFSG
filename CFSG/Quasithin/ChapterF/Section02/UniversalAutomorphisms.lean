module

public import CFSG.Quasithin.ChapterF.Section02
import all CFSG.Quasithin.ChapterF.Section02
public import Mathlib.Algebra.Group.End

/-!
# Universal automorphisms and descent for amalgams

For Aschbacher--Smith, §F.2.5--F.2.8, automorphisms of a diagram act on its
completions and induce automorphisms of its universal group. The stabilizer of
a completion kernel acts on the quotient and hence on the completion itself.
The resulting homomorphism `piMinus` is the one used in F.2.10 and F.2.11.

This internal proof extension imports the parent implementation to establish
evaluation lemmas without changing its public boundary.

The proofs use generation by vertex images to check equality, and the first
isomorphism theorem to transport the quotient action to the completion.
-/

public section

namespace CFSG.Quasithin.ChapterF

universe u v w

namespace AmalgamAutomorphism

variable {D : Type u} [PartialOrder D] {X : D → Type v} [∀ d, Group (X d)]
variable {A : AmalgamDiagram D X}

@[ext] theorem ext {a b : AmalgamAutomorphism A}
    (h : ∀ d x, a.map d x = b.map d x) : a = b := by
  cases a
  cases b
  congr 1
  funext d
  exact MulEquiv.ext (h d)

@[simp] theorem commutes_apply (a : AmalgamAutomorphism A)
    {d e : D} (h : d ≤ e) (x : X d) :
    a.map e (A.map h x) = A.map h (a.map d x) :=
  DFunLike.congr_fun (a.commutes h) x

instance : Group (AmalgamAutomorphism A) where
  one := refl
  mul a b :=
    { map := fun d => (b.map d).trans (a.map d)
      commutes := by
        intro d e h
        ext x
        change a.map e (b.map e (A.map h x)) = A.map h (a.map d (b.map d x))
        rw [commutes_apply, commutes_apply] }
  inv := inv
  mul_assoc a b c := by ext d x; rfl
  one_mul a := by ext d x; rfl
  mul_one a := by ext d x; rfl
  inv_mul_cancel a := by ext d x; exact (a.map d).symm_apply_apply x

@[simp] theorem one_map_apply (d : D) (x : X d) :
    (1 : AmalgamAutomorphism A).map d x = x := by rfl

@[simp] theorem mul_map_apply (a b : AmalgamAutomorphism A) (d : D) (x : X d) :
    (a * b).map d x = a.map d (b.map d x) := by rfl

@[simp] theorem inv_map_apply (a : AmalgamAutomorphism A) (d : D) (x : X d) :
    a⁻¹.map d x = (a.map d).symm x := by rfl

@[simp] theorem act_map_apply {G : Type w} [Group G] (a : AmalgamAutomorphism A)
    (μ : AmalgamCompletion A G) (d : D) (x : X d) :
    (a.act μ).map d x = μ.map d (a⁻¹.map d x) := by rfl

theorem act_mul {G : Type w} [Group G] (a b : AmalgamAutomorphism A)
    (μ : AmalgamCompletion A G) : (a * b).act μ = a.act (b.act μ) := by
  ext d x
  rfl

/-- F.2.5: the action on completions. -/
instance {G : Type w} [Group G] : MulAction (AmalgamAutomorphism A)
    (AmalgamCompletion A G) where
  smul := act
  one_smul := act_refl
  mul_smul := act_mul

end AmalgamAutomorphism

namespace CompletionEquivalence

variable {D : Type u} [PartialOrder D] {X : D → Type v} [∀ d, Group (X d)]
variable {A : AmalgamDiagram D X} {G H : Type w} [Group G] [Group H]
variable {μ : AmalgamCompletion A G} {η : AmalgamCompletion A H}

/-- The action preserves equivalence classes (F.2.5). -/
def act (e : CompletionEquivalence μ η) (a : AmalgamAutomorphism A) :
    CompletionEquivalence (a.act μ) (a.act η) where
  equiv := e.equiv
  commutes := by
    intro d
    ext x
    exact e.commutes_apply d (a⁻¹.map d x)

end CompletionEquivalence

/-- F.2.6: quasiequivalence means equivalence to a member of the automorphism
orbit, with the same indexing diagram. -/
theorem quasiequivalent_iff_orbit {D : Type u} [PartialOrder D] {X : D → Type v}
    [∀ d, Group (X d)] {A : AmalgamDiagram D X} {G H : Type w} [Group G] [Group H]
    (μ : AmalgamCompletion A G) (η : AmalgamCompletion A H) :
    Nonempty (Quasiequivalence μ η) ↔
      ∃ a : AmalgamAutomorphism A, Nonempty (CompletionEquivalence (a.act μ) η) := by
  constructor
  · rintro ⟨q⟩
    refine ⟨q.source, ⟨q.equiv, ?_⟩⟩
    intro d
    ext x
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      AmalgamAutomorphism.act_map_apply, q.commutes,
      AmalgamAutomorphism.inv_map_apply, MulEquiv.apply_symm_apply]
  · rintro ⟨a, ⟨e⟩⟩
    refine ⟨e.equiv, a, ?_⟩
    intro d x
    have h := e.commutes_apply d (a.map d x)
    simpa only [AmalgamAutomorphism.act_map_apply, AmalgamAutomorphism.inv_map_apply,
      MulEquiv.symm_apply_apply] using h

namespace UniversalCompletion

variable {D : Type u} [PartialOrder D] {X : D → Type v} [∀ d, Group (X d)]
variable {A : AmalgamDiagram D X} {U G : Type w} [Group U] [Group G]
variable (ucomp : UniversalCompletion A U)

/-- F.2.7: the automorphism induced on the universal completion. -/
def inducedAut (a : AmalgamAutomorphism A) : MulAut U :=
  MonoidHom.toMulEquiv (ucomp.lift (ucomp.completion.precompose a))
    (ucomp.lift (ucomp.completion.precompose a⁻¹))
    (by
      apply ucomp.completion.hom_ext
      intro d x
      simp only [MonoidHom.comp_apply, lift_spec_apply, MonoidHom.id_apply]
      change ucomp.lift (ucomp.completion.precompose a⁻¹)
        (ucomp.completion.map d (a.map d x)) = ucomp.completion.map d x
      rw [lift_spec_apply]
      change ucomp.completion.map d ((a.map d).symm (a.map d x)) = _
      rw [MulEquiv.symm_apply_apply])
    (by
      apply ucomp.completion.hom_ext
      intro d x
      simp only [MonoidHom.comp_apply, lift_spec_apply, MonoidHom.id_apply]
      change ucomp.lift (ucomp.completion.precompose a)
        (ucomp.completion.map d ((a.map d).symm x)) = ucomp.completion.map d x
      rw [lift_spec_apply]
      change ucomp.completion.map d (a.map d ((a.map d).symm x)) = _
      rw [MulEquiv.apply_symm_apply])

@[simp] theorem inducedAut_map (a : AmalgamAutomorphism A) (d : D) (x : X d) :
    ucomp.inducedAut a (ucomp.completion.map d x) =
      ucomp.completion.map d (a.map d x) := ucomp.lift_spec _ d x

/-- The representation `π̂` of F.2.7. -/
def piHat : AmalgamAutomorphism A →* MulAut U where
  toFun := ucomp.inducedAut
  map_one' := by
    apply MulEquiv.toMonoidHom_injective
    apply ucomp.completion.hom_ext
    intro d x
    simp
  map_mul' a b := by
    apply MulEquiv.toMonoidHom_injective
    apply ucomp.completion.hom_ext
    intro d x
    simp

@[simp] theorem piHat_map (a : AmalgamAutomorphism A) (d : D) (x : X d) :
    ucomp.piHat a (ucomp.completion.map d x) =
      ucomp.completion.map d (a.map d x) := ucomp.inducedAut_map a d x

/-- F.2.8(1), also recording the precomposition version. -/
theorem lift_precompose (μ : AmalgamCompletion A G) (a : AmalgamAutomorphism A) :
    ucomp.lift (μ.precompose a) = (ucomp.lift μ).comp (ucomp.piHat a).toMonoidHom := by
  apply ucomp.completion.hom_ext
  intro d x
  simp only [lift_spec_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, piHat_map]
  rfl

theorem lift_act (μ : AmalgamCompletion A G) (a : AmalgamAutomorphism A) :
    ucomp.lift (a.act μ) = (ucomp.lift μ).comp (ucomp.piHat a⁻¹).toMonoidHom :=
  ucomp.lift_precompose μ a⁻¹

/-- F.2.8(2): the kernel transforms by the universal automorphism. -/
theorem completionKernel_act (μ : AmalgamCompletion A G) (a : AmalgamAutomorphism A) :
    ucomp.completionKernel (a.act μ) =
      (ucomp.completionKernel μ).map (ucomp.piHat a).toMonoidHom := by
  ext x
  change ucomp.lift (a.act μ) x = 1 ↔ _
  rw [lift_act]
  constructor
  · intro hx
    refine ⟨ucomp.piHat a⁻¹ x, hx, ?_⟩
    simp
  · rintro ⟨y, hy, rfl⟩
    change ucomp.lift μ (ucomp.piHat a⁻¹ (ucomp.piHat a y)) = 1
    change ucomp.lift μ y = 1 at hy
    simpa using hy

/-- F.2.8(3): equivalence-class stabilization is kernel stabilization. -/
theorem act_equivalent_iff (μ : AmalgamCompletion A G) (a : AmalgamAutomorphism A) :
    Nonempty (CompletionEquivalence (a.act μ) μ) ↔
      (ucomp.completionKernel μ).map (ucomp.piHat a).toMonoidHom =
        ucomp.completionKernel μ := by
  rw [ucomp.equivalent_iff_kernel_eq, ucomp.completionKernel_act]

/-- Automorphisms stabilizing the equivalence class of a completion. -/
def kernelStabilizer (μ : AmalgamCompletion A G) : Subgroup (AmalgamAutomorphism A) where
  carrier := {a | (ucomp.completionKernel μ).map (ucomp.piHat a).toMonoidHom =
    ucomp.completionKernel μ}
  one_mem' := by
    change (ucomp.completionKernel μ).map (ucomp.piHat 1).toMonoidHom = _
    rw [map_one]
    exact Subgroup.map_id _
  mul_mem' := by
    intro a b ha hb
    change (ucomp.completionKernel μ).map (ucomp.piHat (a * b)).toMonoidHom = _
    rw [map_mul]
    change (ucomp.completionKernel μ).map
      ((ucomp.piHat a).toMonoidHom.comp (ucomp.piHat b).toMonoidHom) = _
    rw [← Subgroup.map_map, hb, ha]
  inv_mem' := by
    intro a ha
    have h := congrArg (fun K : Subgroup U => K.map (ucomp.piHat a⁻¹).toMonoidHom) ha
    rw [Subgroup.map_map] at h
    have hid : (ucomp.piHat a⁻¹).toMonoidHom.comp (ucomp.piHat a).toMonoidHom =
        MonoidHom.id U := by ext x; simp
    rw [hid, Subgroup.map_id] at h
    exact h.symm

/-- The defining kernel condition, available without unfolding the subgroup. -/
theorem mem_kernelStabilizer_iff_map (μ : AmalgamCompletion A G)
    (a : AmalgamAutomorphism A) : a ∈ ucomp.kernelStabilizer μ ↔
      (ucomp.completionKernel μ).map (ucomp.piHat a).toMonoidHom =
        ucomp.completionKernel μ := Iff.rfl

theorem mem_kernelStabilizer_iff (μ : AmalgamCompletion A G) (a : AmalgamAutomorphism A) :
    a ∈ ucomp.kernelStabilizer μ ↔ Nonempty (CompletionEquivalence (a.act μ) μ) :=
  (ucomp.act_equivalent_iff μ a).symm

/-- F.2.8(4.i): the automorphism of the quotient by the completion kernel. -/
def quotientAut (μ : AmalgamCompletion A G) (a : ucomp.kernelStabilizer μ) :
    MulAut (U ⧸ (ucomp.lift μ).ker) :=
  QuotientGroup.congr _ _ (ucomp.piHat a.val) a.property

@[simp] theorem quotientAut_mk (μ : AmalgamCompletion A G)
    (a : ucomp.kernelStabilizer μ) (x : U) :
    ucomp.quotientAut μ a (QuotientGroup.mk x) =
      QuotientGroup.mk (ucomp.piHat a.val x) := by rfl

/-- F.2.8(4.ii): evaluation on the images of the vertex groups in the quotient. -/
theorem quotientAut_vertex (μ : AmalgamCompletion A G)
    (a : ucomp.kernelStabilizer μ) (d : D) (x : X d) :
    ucomp.quotientAut μ a (QuotientGroup.mk (ucomp.completion.map d x)) =
      QuotientGroup.mk (ucomp.completion.map d (a.val.map d x)) := by simp

/-- F.2.8(4.iii): transport the quotient automorphism to the completion. -/
noncomputable def descendAut (μ : AmalgamCompletion A G)
    (a : ucomp.kernelStabilizer μ) : MulAut G :=
  let e := QuotientGroup.liftEquiv (ucomp.lift μ).ker (ucomp.lift_surjective μ) rfl
  (e.symm.trans (ucomp.quotientAut μ a)).trans e

/-- The descent square commutes on the entire universal group. -/
@[simp] theorem descendAut_lift (μ : AmalgamCompletion A G)
    (a : ucomp.kernelStabilizer μ) (x : U) :
    ucomp.descendAut μ a (ucomp.lift μ x) = ucomp.lift μ (ucomp.piHat a.val x) := by
  let e := QuotientGroup.liftEquiv (ucomp.lift μ).ker (ucomp.lift_surjective μ) rfl
  have he (z : U) : e (QuotientGroup.mk z) = ucomp.lift μ z := by rfl
  change e (ucomp.quotientAut μ a (e.symm (ucomp.lift μ x))) = _
  rw [← he x, MulEquiv.symm_apply_apply, quotientAut_mk, he]

/-- F.2.8(4.iv): evaluation compatibility at each vertex image. -/
@[simp] theorem descendAut_map (μ : AmalgamCompletion A G)
    (a : ucomp.kernelStabilizer μ) (d : D) (x : X d) :
    ucomp.descendAut μ a (μ.map d x) = μ.map d (a.val.map d x) := by
  rw [← ucomp.lift_spec μ d x, descendAut_lift, piHat_map, lift_spec_apply]

/-- F.2.8(4.v): `π⁻`, the representation on a completion of its equivalence-class
stabilizer. Multiplication is composition, with the right factor applied first. -/
noncomputable def piMinus (μ : AmalgamCompletion A G) :
    ucomp.kernelStabilizer μ →* MulAut G where
  toFun := ucomp.descendAut μ
  map_one' := by
    apply MulEquiv.toMonoidHom_injective
    apply μ.hom_ext
    intro d x
    simp
  map_mul' a b := by
    apply MulEquiv.toMonoidHom_injective
    apply μ.hom_ext
    intro d x
    simp

@[simp] theorem piMinus_map (μ : AmalgamCompletion A G)
    (a : ucomp.kernelStabilizer μ) (d : D) (x : X d) :
    ucomp.piMinus μ a (μ.map d x) = μ.map d (a.val.map d x) :=
  ucomp.descendAut_map μ a d x

theorem piMinus_mul (μ : AmalgamCompletion A G) (a b : ucomp.kernelStabilizer μ) :
    ucomp.piMinus μ (a * b) = ucomp.piMinus μ a * ucomp.piMinus μ b :=
  (ucomp.piMinus μ).map_mul a b

/-- The induced action on a faithful completion is faithful. -/
theorem piMinus_injective (μ : AmalgamCompletion A G) (hμ : μ.Faithful) :
    Function.Injective (ucomp.piMinus μ) := by
  intro a b hab
  apply Subtype.ext
  apply AmalgamAutomorphism.ext
  intro d x
  apply hμ d
  have h := DFunLike.congr_fun hab (μ.map d x)
  simpa only [piMinus_map] using h

/-- A compatible automorphism of the completion certifies kernel stabilization. -/
theorem mem_kernelStabilizer_of_compatible (μ : AmalgamCompletion A G)
    (a : AmalgamAutomorphism A) (e : MulAut G)
    (he : ∀ d x, e (μ.map d x) = μ.map d (a.map d x)) :
    a ∈ ucomp.kernelStabilizer μ := by
  have hcomp : (ucomp.lift μ).comp (ucomp.piHat a).toMonoidHom =
      e.toMonoidHom.comp (ucomp.lift μ) := by
    apply ucomp.completion.hom_ext
    intro d x
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, piHat_map,
      lift_spec_apply] using (he d x).symm
  apply (ucomp.mem_kernelStabilizer_iff_map μ a).2
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ucomp.lift μ (ucomp.piHat a y) = 1
    have h := DFunLike.congr_fun hcomp y
    change ucomp.lift μ y = 1 at hy
    simpa [hy] using h
  · intro hx
    obtain ⟨y, rfl⟩ := (ucomp.piHat a).surjective x
    refine ⟨y, ?_, rfl⟩
    change ucomp.lift μ y = 1
    apply e.injective
    have h := DFunLike.congr_fun hcomp y
    change ucomp.lift μ (ucomp.piHat a y) = 1 at hx
    simpa [hx] using h.symm

/-- Compatibility on the generating vertex groups characterizes `π⁻`. -/
theorem piMinus_eq_of_compatible (μ : AmalgamCompletion A G)
    (a : ucomp.kernelStabilizer μ) (e : MulAut G)
    (he : ∀ d x, e (μ.map d x) = μ.map d (a.val.map d x)) :
    ucomp.piMinus μ a = e := by
  apply MulEquiv.toMonoidHom_injective
  apply μ.hom_ext
  intro d x
  simpa only [MulEquiv.coe_toMonoidHom, piMinus_map] using (he d x).symm

end UniversalCompletion

end CFSG.Quasithin.ChapterF
