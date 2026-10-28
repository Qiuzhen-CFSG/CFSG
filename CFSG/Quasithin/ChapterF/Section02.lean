module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Amalgams, equivalences, and automorphisms

This file formalizes the reusable, purely algebraic part of Aschbacher--Smith,
§F.2 (printed pp. 264--268).  An amalgam is a diagram of groups indexed by a
poset.  A completion records the compatible maps into a generated group, and
the universal-completion structure records the usual universal property.  The
remaining statements are then kernel, conjugation, and transport lemmas.

This module supplies definitions and basic transport results; it does not assert
existence of the universal completion or the extension claim F.2.11. The latter
has a missing hypothesis in the printed source (see `Section02.Obstruction`).
-/

public section

namespace CFSG.Quasithin.ChapterF

universe u v w

/-- A group-valued diagram on a poset. -/
structure AmalgamDiagram (D : Type u) [PartialOrder D] (X : D → Type v)
    [∀ d, Group (X d)] where
  map : ∀ {d e : D}, d ≤ e → X d →* X e
  map_id : ∀ d, map (le_refl d) = MonoidHom.id (X d)
  map_comp : ∀ {d e f : D} (hde : d ≤ e) (hef : e ≤ f),
    (map hef).comp (map hde) = map (hde.trans hef)

namespace AmalgamDiagram

variable {D : Type u} [PartialOrder D] {X : D → Type v} [∀ d, Group (X d)]
variable (A : AmalgamDiagram D X)

@[simp] theorem map_id_apply (d : D) (x : X d) : A.map (le_refl d) x = x := by
  rw [A.map_id]
  rfl

@[simp] theorem map_comp_apply {d e f : D} (hde : d ≤ e) (hef : e ≤ f) (x : X d) :
    A.map hef (A.map hde x) = A.map (hde.trans hef) x := by
  simpa only [MonoidHom.comp_apply] using
    DFunLike.congr_fun (A.map_comp hde hef) x

end AmalgamDiagram

/-- A completion of an amalgam. Faithfulness is a separate property, as in F.2.1. -/
structure AmalgamCompletion {D : Type u} [PartialOrder D] {X : D → Type v}
    [∀ d, Group (X d)] (A : AmalgamDiagram D X) (G : Type w) [Group G] where
  map : ∀ d, X d →* G
  compatible : ∀ {d e : D} (h : d ≤ e), (map e).comp (A.map h) = map d
  generated : Subgroup.closure (⋃ d, Set.range (map d)) = ⊤

namespace AmalgamCompletion

variable {D : Type u} [PartialOrder D] {X : D → Type v} [∀ d, Group (X d)]
variable {A : AmalgamDiagram D X} {G : Type w} [Group G]
variable (μ : AmalgamCompletion A G)

@[simp] theorem compatible_apply {d e : D} (h : d ≤ e) (x : X d) :
    μ.map e (A.map h x) = μ.map d x := by
  exact DFunLike.congr_fun (μ.compatible h) x

/-- A completion is faithful if every vertex map is injective. -/
@[expose] def Faithful : Prop := ∀ d, Function.Injective (μ.map d)

theorem map_injective (hμ : μ.Faithful) (d : D) : Function.Injective (μ.map d) := hμ d

/-- The image of each vertex group is a subgroup of the completion group. -/
def image (d : D) : Subgroup G := (μ.map d).range

theorem image_eq_map (d : D) : μ.image d = (μ.map d).range := by rfl

/-- Homomorphisms from a completion are determined on its vertex groups. -/
theorem hom_ext {H : Type*} [Group H] {f g : G →* H}
    (h : ∀ d x, f (μ.map d x) = g (μ.map d x)) : f = g := by
  apply MonoidHom.eq_of_eqOn_dense μ.generated
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨d, y, rfl⟩
  exact h d y

end AmalgamCompletion

/-- An isomorphism exhibiting equivalence of two completions of the same
amalgam. -/
structure CompletionEquivalence {D : Type u} [PartialOrder D] {X : D → Type v}
    [∀ d, Group (X d)] {A : AmalgamDiagram D X}
    {G : Type w} [Group G] {H : Type w} [Group H]
    (μ : AmalgamCompletion A G) (η : AmalgamCompletion A H) where
  equiv : G ≃* H
  commutes : ∀ d, equiv.toMonoidHom.comp (μ.map d) = η.map d

namespace CompletionEquivalence

variable {D : Type u} [PartialOrder D] {X : D → Type v} [∀ d, Group (X d)]
variable {A : AmalgamDiagram D X} {G H K : Type w} [Group G] [Group H] [Group K]
variable {μ : AmalgamCompletion A G} {η : AmalgamCompletion A H}

theorem commutes_apply (e : CompletionEquivalence μ η) (d : D) (x : X d) :
    e.equiv (μ.map d x) = η.map d x := DFunLike.congr_fun (e.commutes d) x

def refl (μ : AmalgamCompletion A G) : CompletionEquivalence μ μ :=
  ⟨MulEquiv.refl G, by intro d; ext x; rfl⟩

def symm (e : CompletionEquivalence μ η) : CompletionEquivalence η μ :=
  ⟨e.equiv.symm, by
    intro d
    ext x
    apply e.equiv.injective
    simp [e.commutes_apply]⟩

def trans {ν : AmalgamCompletion A K} (e₁ : CompletionEquivalence μ η)
    (e₂ : CompletionEquivalence η ν) : CompletionEquivalence μ ν :=
  ⟨e₁.equiv.trans e₂.equiv, by
    intro d
    ext x
    simp [e₁.commutes_apply, e₂.commutes_apply]⟩

end CompletionEquivalence

/-- The universal completion property.  `lift` is the unique homomorphism out
of the universal group extending every completion map. -/
structure UniversalCompletion {D : Type u} [PartialOrder D] {X : D → Type v}
    [∀ d, Group (X d)] (A : AmalgamDiagram D X) (U : Type w) [Group U] where
  completion : AmalgamCompletion A U
  lift : ∀ {G : Type w} [Group G], AmalgamCompletion A G → U →* G
  lift_spec : ∀ {G : Type w} [Group G] (μ : AmalgamCompletion A G) (d : D) (x : X d),
    lift μ (completion.map d x) = μ.map d x
  lift_unique : ∀ {G : Type w} [Group G] (μ : AmalgamCompletion A G)
    (f : U →* G), ((∀ d x, f (completion.map d x) = μ.map d x) → f = lift μ)

namespace UniversalCompletion

variable {D : Type u} [PartialOrder D] {X : D → Type v} [∀ d, Group (X d)]
variable {A : AmalgamDiagram D X} {U G H : Type w} [Group U] [Group G] [Group H]
variable (ucomp : UniversalCompletion A U)

@[simp] theorem lift_spec_apply (μ : AmalgamCompletion A G) (d : D) (x : X d) :
    ucomp.lift μ (ucomp.completion.map d x) = μ.map d x :=
  ucomp.lift_spec μ d x

theorem lift_unique_eq (μ : AmalgamCompletion A G) (f : U →* G)
    (hf : ∀ d x, f (ucomp.completion.map d x) = μ.map d x) :
    f = ucomp.lift μ := ucomp.lift_unique μ f hf

theorem lift_comp_lift (μ : AmalgamCompletion A G) (η : AmalgamCompletion A H)
    (f : G →* H) (hf : ∀ d x, f (μ.map d x) = η.map d x) :
    (ucomp.lift η) = f.comp (ucomp.lift μ) := by
  symm
  apply ucomp.lift_unique η
  intro d x
  simpa only [MonoidHom.comp_apply, ucomp.lift_spec_apply] using hf d x

end UniversalCompletion

/-- An automorphism of a group diagram over the fixed indexing poset. -/
structure AmalgamAutomorphism {D : Type u} [PartialOrder D] {X : D → Type v}
    [∀ d, Group (X d)] (A : AmalgamDiagram D X) where
  map : ∀ d, X d ≃* X d
  commutes : ∀ {d e} (h : d ≤ e),
    (map e).toMonoidHom.comp (A.map h) =
      (A.map h).comp (map d).toMonoidHom

namespace AmalgamAutomorphism

variable {D : Type u} [PartialOrder D] {X : D → Type v} [∀ d, Group (X d)]
variable {A : AmalgamDiagram D X}

def refl : AmalgamAutomorphism A where
  map d := MulEquiv.refl (X d)
  commutes := by intro d e h; ext x; rfl

@[simp] theorem refl_apply (d : D) (x : X d) :
    (refl (A := A)).map d x = x := by rfl

def inv (a : AmalgamAutomorphism A) : AmalgamAutomorphism A :=
  { map := fun d => (a.map d).symm
    commutes := by
      intro d e h
      ext x
      apply (a.map e).injective
      simp only [MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp, Function.comp_apply,
        MulEquiv.apply_symm_apply]
      have hx := DFunLike.congr_fun (a.commutes h) ((a.map d).symm x)
      simpa only [MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp, Function.comp_apply,
        MulEquiv.apply_symm_apply] using hx.symm }

end AmalgamAutomorphism

/-- Precomposition transports a completion along an automorphism of the
amalgam. -/
def AmalgamCompletion.precompose {D : Type u} [PartialOrder D] {X : D → Type v}
    [∀ d, Group (X d)] {A : AmalgamDiagram D X} {G : Type w} [Group G]
    (μ : AmalgamCompletion A G) (a : AmalgamAutomorphism A) :
    AmalgamCompletion A G where
  map d := (μ.map d).comp (a.map d).toMonoidHom
  compatible := by
    intro d e h
    ext x
    change μ.map e ((a.map e) (A.map h x)) = μ.map d ((a.map d) x)
    have ha : (a.map e) (A.map h x) = A.map h ((a.map d) x) := by
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using
        DFunLike.congr_fun (a.commutes h) x
    rw [ha, μ.compatible_apply]
  generated := by
    apply le_antisymm
    · exact le_top
    · rw [← μ.generated]
      refine (Subgroup.closure_le _).2 ?_
      intro g hg
      rcases Set.mem_iUnion.1 hg with ⟨d, hg⟩
      rcases hg with ⟨x, rfl⟩
      exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨d, ⟨(a.map d).symm x, by simp⟩⟩)

namespace AmalgamCompletion

variable {D : Type u} [PartialOrder D] {X : D → Type v} [∀ d, Group (X d)]
variable {A : AmalgamDiagram D X} {G : Type w} [Group G]

@[ext] theorem ext {μ ν : AmalgamCompletion A G}
    (h : ∀ d x, μ.map d x = ν.map d x) : μ = ν := by
  cases μ with
  | mk m c g =>
    cases ν with
    | mk n c' g' =>
      have hm : m = n := by
        funext d
        exact MonoidHom.ext (h d)
      subst n
      rfl

theorem faithful_precompose (μ : AmalgamCompletion A G) (hμ : μ.Faithful)
    (a : AmalgamAutomorphism A) : (μ.precompose a).Faithful :=
  fun d => (hμ d).comp (a.map d).injective

theorem precompose_precompose (μ : AmalgamCompletion A G) (a : AmalgamAutomorphism A) :
    (μ.precompose a).precompose (AmalgamAutomorphism.inv a) = μ := by
  apply AmalgamCompletion.ext
  intro d x
  change μ.map d ((a.map d) ((a.map d).symm x)) = μ.map d x
  simp

end AmalgamCompletion

namespace AmalgamAutomorphism

variable {D : Type u} [PartialOrder D] {X : D → Type v} [∀ d, Group (X d)]
variable {A : AmalgamDiagram D X}

/-- The permutation action from F.2.5, written by precomposing with the inverse
automorphism. -/
def act {G : Type w} [Group G] (a : AmalgamAutomorphism A)
    (μ : AmalgamCompletion A G) : AmalgamCompletion A G :=
  μ.precompose (inv a)

@[simp] theorem act_refl {G : Type w} [Group G] (μ : AmalgamCompletion A G) :
    (refl (A := A)).act μ = μ := by
  apply AmalgamCompletion.ext
  intro d x
  rfl

end AmalgamAutomorphism

/-- A quasiequivalence of completions, allowing an automorphism of the source
amalgam as in F.2.6. -/
structure Quasiequivalence {D : Type u} [PartialOrder D] {X : D → Type v}
    [∀ d, Group (X d)] {A : AmalgamDiagram D X} {G H : Type w}
    [Group G] [Group H] (μ : AmalgamCompletion A G) (η : AmalgamCompletion A H) where
  equiv : G ≃* H
  source : AmalgamAutomorphism A
  commutes : ∀ d x, equiv (μ.map d x) = η.map d (source.map d x)

namespace UniversalCompletion

variable {D : Type u} [PartialOrder D] {X : D → Type v} [∀ d, Group (X d)]
variable {A : AmalgamDiagram D X} {U G H : Type w} [Group U] [Group G] [Group H]
variable (ucomp : UniversalCompletion A U)

/-- The canonical map onto any completion is surjective, since the vertex
images generate the target. -/
theorem lift_surjective (μ : AmalgamCompletion A G) :
    Function.Surjective (ucomp.lift μ) := by
  apply MonoidHom.range_eq_top.1
  apply top_unique
  rw [← μ.generated]
  apply (Subgroup.closure_le _).2
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨d, y, rfl⟩
  exact ⟨ucomp.completion.map d y, ucomp.lift_spec μ d y⟩

/-- F.2.4(1): the vertex-level and universal-level commuting squares agree. -/
theorem equivalence_iff_lift (μ : AmalgamCompletion A G)
    (η : AmalgamCompletion A H) (e : G ≃* H) :
    (∀ d, e.toMonoidHom.comp (μ.map d) = η.map d) ↔
      e.toMonoidHom.comp (ucomp.lift μ) = ucomp.lift η := by
  constructor
  · intro h
    apply ucomp.lift_unique η
    intro d x
    simpa only [MonoidHom.comp_apply, ucomp.lift_spec_apply] using
      DFunLike.congr_fun (h d) x
  · intro h d
    ext x
    simpa only [MonoidHom.comp_apply, ucomp.lift_spec_apply] using
      DFunLike.congr_fun h (ucomp.completion.map d x)

/-- The kernel of the canonical map from the universal completion to a
completion. -/
def completionKernel (μ : AmalgamCompletion A G) : Subgroup U :=
  (ucomp.lift μ).ker

theorem completionKernel_eq_of_equiv (μ : AmalgamCompletion A G)
    (η : AmalgamCompletion A H) (e : CompletionEquivalence μ η) :
    ucomp.completionKernel μ = ucomp.completionKernel η := by
  have hlift : ucomp.lift η = e.equiv.toMonoidHom.comp (ucomp.lift μ) := by
    exact ucomp.lift_comp_lift μ η e.equiv.toMonoidHom (fun d x => e.commutes_apply d x)
  ext z
  constructor
  · intro hz
    change ucomp.lift μ z = 1 at hz
    change ucomp.lift η z = 1
    rw [hlift]
    simp [hz]
  · intro hz
    change ucomp.lift η z = 1 at hz
    change ucomp.lift μ z = 1
    have hz' : e.equiv (ucomp.lift μ z) = 1 := by simpa [hlift] using hz
    apply e.equiv.injective
    simpa using hz'

/-- F.2.4(2), constructive direction: equal kernels induce an equivalence by
the two isomorphisms out of the common quotient of the universal completion. -/
noncomputable def equivalenceOfKernelEq (μ : AmalgamCompletion A G)
    (η : AmalgamCompletion A H)
    (h : ucomp.completionKernel μ = ucomp.completionKernel η) :
    CompletionEquivalence μ η := by
  let K := (ucomp.lift μ).ker
  have hK : K = (ucomp.lift η).ker := h
  let eμ := QuotientGroup.liftEquiv K (ucomp.lift_surjective μ) rfl
  let eη := QuotientGroup.liftEquiv K (ucomp.lift_surjective η) hK
  refine ⟨eμ.symm.trans eη, ?_⟩
  intro d
  ext x
  change eη (eμ.symm (μ.map d x)) = η.map d x
  have hx : eμ (QuotientGroup.mk (ucomp.completion.map d x)) = μ.map d x := by
    simp [eμ]
  rw [← hx, MulEquiv.symm_apply_apply]
  simp [eη]

/-- F.2.4(2). -/
theorem equivalent_iff_kernel_eq (μ : AmalgamCompletion A G)
    (η : AmalgamCompletion A H) :
    Nonempty (CompletionEquivalence μ η) ↔
      ucomp.completionKernel μ = ucomp.completionKernel η :=
  ⟨fun ⟨e⟩ => ucomp.completionKernel_eq_of_equiv μ η e,
    fun h => ⟨ucomp.equivalenceOfKernelEq μ η h⟩⟩

end UniversalCompletion

/-- A subgroup amalgam inside a group, the notion called a `Y`-amalgam in
F.2.9. -/
structure YAmalgam (D : Type u) [PartialOrder D] (Y : Type v) [Group Y] where
  subgroup : D → Subgroup Y
  le : ∀ {d e : D}, d ≤ e → subgroup d ≤ subgroup e
  generated : Subgroup.closure (⋃ d, (subgroup d : Set Y)) = ⊤

namespace YAmalgam

variable {D : Type u} [PartialOrder D] {Y : Type v} [Group Y]
variable (γ : YAmalgam D Y)

private def map {d e : D} (h : d ≤ e) : (γ.subgroup d : Type v) →* (γ.subgroup e : Type v) where
  toFun x := ⟨x.1, γ.le h x.2⟩
  map_one' := by ext; rfl
  map_mul' := by intro x y; ext; rfl

def diagram : AmalgamDiagram D (fun d => (γ.subgroup d : Type v)) where
  map := fun h => map γ h
  map_id := by
    intro d
    ext x
    rfl
  map_comp := by
    intro d e f hde hef
    ext x
    rfl

def completion : AmalgamCompletion γ.diagram Y where
  map d := (γ.subgroup d).subtype
  compatible := by
    intro d e h
    ext x
    rfl
  generated := by simpa using γ.generated

theorem completion_faithful : γ.completion.Faithful := by
  intro d x y h
  exact Subtype.ext h

@[simp] theorem completion_map_apply (d : D) (x : γ.subgroup d) :
    γ.completion.map d x = (x : Y) := by rfl

end YAmalgam

/-- A conjugation action on a completion, as used in F.2.8 and F.2.10. -/
def conjugationHom {G : Type*} [Group G] (g : G) : G ≃* G :=
  { toFun := fun x => g * x * g⁻¹
    invFun := fun x => g⁻¹ * x * g
    left_inv := by intro x; simp [mul_assoc]
    right_inv := by intro x; simp [mul_assoc]
    map_mul' := by intro x y; simp [mul_assoc] }

theorem conjugationHom_apply {G : Type*} [Group G] (g x : G) :
    conjugationHom g x = g * x * g⁻¹ := by rfl

theorem conjugationHom_mul {G : Type*} [Group G] (g h : G) :
    conjugationHom (g * h) = (conjugationHom h).trans (conjugationHom g) := by
  ext x
  simp [conjugationHom, mul_assoc]

end CFSG.Quasithin.ChapterF
