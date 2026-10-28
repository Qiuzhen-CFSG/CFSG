module

public import CFSG.Quasithin.ChapterF.Section02
public import Mathlib.GroupTheory.PresentedGroup

/-!
# Existence of universal completions

For an arbitrary group-valued amalgam, the universal completion is the group
presented by one generator for each vertex element, with the vertex
multiplication and diagram compatibility relations.  This is the elementary
free-group construction behind Aschbacher--Smith, F.2.1--F.2.2 (printed
pp. 264--265).  The carrier has universe `max u v`, matching the convention in
`UniversalCompletion`.
-/

public section

namespace CFSG.Quasithin.ChapterF

universe u v

namespace UniversalCompletion

variable {D : Type u} [PartialOrder D] {X : D → Type v} [∀ d, Group (X d)]
variable (A : AmalgamDiagram D X)

abbrev PresentationGenerator := Σ d : D, X d

inductive PresentationRelation
  | mul (d : D) (x y : X d)
  | map {d e : D} (h : d ≤ e) (x : X d)

def presentationWord : PresentationRelation (D := D) (X := X) →
    FreeGroup (PresentationGenerator (D := D) (X := X)) := fun r =>
  match r with
  | PresentationRelation.mul d x y =>
      FreeGroup.of ⟨d, x * y⟩ *
        (FreeGroup.of ⟨d, x⟩ * FreeGroup.of ⟨d, y⟩)⁻¹
  | PresentationRelation.map h x =>
      FreeGroup.of ⟨_, A.map h x⟩ * (FreeGroup.of ⟨_, x⟩)⁻¹

def presentationRelations : Set (FreeGroup (PresentationGenerator (D := D) (X := X))) :=
  Set.range (presentationWord (D := D) (X := X) A)

abbrev universalCarrier := PresentedGroup (presentationRelations A)

def generator (z : PresentationGenerator (D := D) (X := X)) : universalCarrier A :=
  PresentedGroup.of z

lemma generator_mul (d : D) (x y : X d) :
    generator A ⟨d, x * y⟩ = generator A ⟨d, x⟩ * generator A ⟨d, y⟩ := by
  apply eq_of_mul_inv_eq_one
  change PresentedGroup.mk (presentationRelations A) _ = 1
  apply PresentedGroup.one_of_mem
  exact ⟨PresentationRelation.mul d x y, rfl⟩

lemma generator_map {d e : D} (h : d ≤ e) (x : X d) :
    generator A ⟨e, A.map h x⟩ = generator A ⟨d, x⟩ := by
  apply eq_of_mul_inv_eq_one
  change PresentedGroup.mk (presentationRelations A) _ = 1
  apply PresentedGroup.one_of_mem
  exact ⟨PresentationRelation.map h x, rfl⟩

@[expose] def vertexMap (d : D) : X d →* universalCarrier A where
  toFun x := generator A ⟨d, x⟩
  map_one' := by
    have h := generator_mul A d 1 1
    have h' : (1 : universalCarrier A) * generator A ⟨d, (1 : X d)⟩ =
        generator A ⟨d, (1 : X d)⟩ * generator A ⟨d, (1 : X d)⟩ := by
      simpa using h
    exact (mul_right_cancel h').symm
  map_mul' x y := generator_mul A d x y

lemma vertexMap_apply (d : D) (x : X d) :
    vertexMap A d x = generator A ⟨d, x⟩ := rfl

lemma vertexMap_compatible {d e : D} (h : d ≤ e) :
    (vertexMap A e).comp (A.map h) = vertexMap A d := by
  ext x
  exact generator_map A h x

lemma vertexMaps_generated :
    Subgroup.closure (⋃ d, Set.range (vertexMap A d)) =
      (⊤ : Subgroup (universalCarrier A)) := by
  have hsets : (⋃ d, Set.range (vertexMap A d)) =
      Set.range (PresentedGroup.of :
        PresentationGenerator (D := D) (X := X) → universalCarrier A) := by
    ext z
    constructor
    · intro hz
      rcases Set.mem_iUnion.1 hz with ⟨d, hz⟩
      rcases hz with ⟨x, rfl⟩
      exact ⟨⟨d, x⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      rcases w with ⟨d, x⟩
      exact Set.mem_iUnion.2 ⟨d, ⟨x, rfl⟩⟩
  rw [hsets, PresentedGroup.closure_range_of]

@[expose] def canonicalCompletion : AmalgamCompletion A (universalCarrier A) where
  map := vertexMap A
  compatible := vertexMap_compatible A
  generated := vertexMaps_generated A

variable {G : Type (max u v)} [Group G]

def relationEvaluation (μ : AmalgamCompletion A G) :
    PresentationGenerator (D := D) (X := X) → G := fun z => μ.map z.1 z.2

lemma relationEvaluation_rel (μ : AmalgamCompletion A G) :
    ∀ r ∈ presentationRelations A,
      FreeGroup.lift (relationEvaluation A μ) r = 1 := by
  rintro r ⟨q, rfl⟩
  cases q with
  | mul d x y =>
      simp [presentationWord, relationEvaluation, map_mul]
  | map h x =>
      simp only [presentationWord, relationEvaluation, FreeGroup.lift_apply_of,
        map_mul, map_inv]
      rw [μ.compatible_apply]
      simp

def canonicalLift (μ : AmalgamCompletion A G) :
    universalCarrier A →* G :=
  PresentedGroup.toGroup (relationEvaluation_rel A μ)

lemma canonicalLift_spec (μ : AmalgamCompletion A G) (d : D) (x : X d) :
    canonicalLift A μ ((canonicalCompletion A).map d x) = μ.map d x := by
  change canonicalLift A μ (generator A ⟨d, x⟩) = _
  exact PresentedGroup.toGroup.of _

lemma canonicalLift_unique (μ : AmalgamCompletion A G)
    (f : universalCarrier A →* G)
    (hf : ∀ d x, f ((canonicalCompletion A).map d x) = μ.map d x) :
    f = canonicalLift A μ := by
  apply PresentedGroup.ext
  rintro ⟨d, x⟩
  calc
    f (PresentedGroup.of ⟨d, x⟩) = f ((canonicalCompletion A).map d x) := by rfl
    _ = μ.map d x := hf d x
    _ = canonicalLift A μ ((canonicalCompletion A).map d x) :=
      (canonicalLift_spec A μ d x).symm
    _ = canonicalLift A μ (PresentedGroup.of ⟨d, x⟩) := by rfl

/-- The presented universal completion of an arbitrary amalgam. -/
def universalCompletion : UniversalCompletion A (universalCarrier A) where
  completion := canonicalCompletion A
  lift := by
    intro G _ μ
    exact canonicalLift A μ
  lift_spec := by
    intro G _ μ d x
    exact canonicalLift_spec A μ d x
  lift_unique := by
    intro G _ μ f hf
    exact canonicalLift_unique A μ f hf

/-- The completion underlying the universal construction. -/
@[simp] theorem universalCompletion_completion :
    (universalCompletion A).completion = canonicalCompletion A := by rfl

/-- Public evaluation of the universal vertex maps. -/
@[simp] theorem universalCompletion_map (d : D) (x : X d) :
    (universalCompletion A).completion.map d x = generator A ⟨d, x⟩ := by rfl

/-- The universal lift is the homomorphism defined by the presentation. -/
@[simp] theorem universalCompletion_lift (μ : AmalgamCompletion A G) :
    (universalCompletion A).lift μ = canonicalLift A μ := by rfl

/-- A faithful completion forces the canonical vertex maps in the universal
completion to be faithful. -/
theorem canonicalCompletion_faithful_of_faithful
    (μ : AmalgamCompletion A G) (hμ : μ.Faithful) :
    (canonicalCompletion A).Faithful := by
  intro d x y hxy
  apply hμ d
  have h := congrArg (canonicalLift A μ) hxy
  calc
    μ.map d x = canonicalLift A μ ((canonicalCompletion A).map d x) :=
      (canonicalLift_spec A μ d x).symm
    _ = canonicalLift A μ ((canonicalCompletion A).map d y) := h
    _ = μ.map d y := canonicalLift_spec A μ d y

/-- Faithfulness in the interface used by universal automorphisms and descent. -/
theorem universalCompletion_faithful_of_faithful
    (μ : AmalgamCompletion A G) (hμ : μ.Faithful) :
    (universalCompletion A).completion.Faithful := by
  rw [universalCompletion_completion]
  exact canonicalCompletion_faithful_of_faithful A μ hμ

end UniversalCompletion

end CFSG.Quasithin.ChapterF
