module

public import Theory.GroupTheory.NoncentralChiefRefinement.Actions

/-!
# Restricting normal filtrations to a subgroup

Intersect each ambient-normal subgroup with the new actor, using `subgroupOf`.
The resulting relative section injects into the original section by the literal
inclusion on representatives, and this injection intertwines conjugation by
the restricted actor. Finite normal filtrations admit chief refinements even
when successive intersections coincide. These constructions are the section
maps needed for the residual comparison in Aschbacher–Smith 14.7.70, p.1074.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {K : Type*} [Group K]

/-- The intersection with the subgroup actor, regarded as a normal subgroup of it. -/
@[expose] def restrictNormalNode (R : Subgroup K) (A : NormalNode K) : NormalNode R :=
  ⟨A.val.subgroupOf R, inferInstanceAs (A.val.subgroupOf R).Normal⟩

@[simp] theorem restrictNormalNode_bot (R : Subgroup K) :
    restrictNormalNode R ⊥ = ⊥ := by
  apply Subtype.ext
  ext r
  change (r : K) = 1 ↔ r = 1
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

@[simp] theorem restrictNormalNode_top (R : Subgroup K) :
    restrictNormalNode R ⊤ = ⊤ := by
  apply Subtype.ext
  exact comap_top R.subtype

theorem restrictNormalNode_monotone (R : Subgroup K) : Monotone (restrictNormalNode R) :=
  fun _ _ h => comap_mono h

private def restrictionRepresentative (R : Subgroup K) (B : NormalNode K) :
    (restrictNormalNode R B).val →* B.val where
  toFun b := ⟨b.val.val, b.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private def restrictionQuotientHom (R : Subgroup K) (A B : NormalNode K) :
    (restrictNormalNode R B).val →* Section A B :=
  (QuotientGroup.mk' _).comp (restrictionRepresentative R B)

private theorem restrictionQuotientHom_ker (R : Subgroup K) (A B : NormalNode K) :
    (restrictNormalNode R A).val.subgroupOf (restrictNormalNode R B).val =
      (restrictionQuotientHom R A B).ker := by
  ext b
  exact (QuotientGroup.eq_one_iff (N := A.val.subgroupOf B.val)
    (restrictionRepresentative R B b)).symm

/-- The map of actual intersected normal sections induced by inclusion. -/
def restrictionSectionMap (R : Subgroup K) (A B : NormalNode K) :
    Section (restrictNormalNode R A) (restrictNormalNode R B) →* Section A B :=
  QuotientGroup.lift _ (restrictionQuotientHom R A B) (restrictionQuotientHom_ker R A B).le

/-- No quotient elements are lost by inclusion of the intersected section. -/
theorem restrictionSectionMap_injective (R : Subgroup K) (A B : NormalNode K) :
    Function.Injective (restrictionSectionMap R A B) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (restrictionQuotientHom_ker R A B)

@[simp] theorem restrictionSectionMap_mk (R : Subgroup K) (A B : NormalNode K)
    (b : (restrictNormalNode R B).val) :
    restrictionSectionMap R A B (QuotientGroup.mk' _ b) =
      QuotientGroup.mk' _ (⟨b.val.val, b.property⟩ : B.val) := by rfl

/-- Conjugation by a subgroup element is conjugation by its literal ambient image. -/
theorem restrictionSectionMap_equivariant (R : Subgroup K) (A B : NormalNode K)
    (r : R) (x : Section (restrictNormalNode R A) (restrictNormalNode R B)) :
    restrictionSectionMap R A B
        (sectionAction (restrictNormalNode R A) (restrictNormalNode R B) r x) =
      sectionAction A B (r : K) (restrictionSectionMap R A B x) := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rfl

/-- An intersected section of a two-group section is itself a two-group. -/
theorem restrictionSection_isPGroup (R : Subgroup K) (A B : NormalNode K)
    (hp : IsPGroup 2 (Section A B)) :
    IsPGroup 2 (Section (restrictNormalNode R A) (restrictNormalNode R B)) :=
  hp.of_injective (restrictionSectionMap R A B) (restrictionSectionMap_injective R A B)

/-- Restrict the terms of a chief series. It is only a filtration: chiefness
and strictness can both be lost upon changing the actor. -/
@[expose] def ChiefSeries.restrictionFiltration (s : ChiefSeries K) (R : Subgroup K) :
    Filtration R s.length where
  term i := restrictNormalNode R (s i)
  monotone := (restrictNormalNode_monotone R).comp s.strictMono.monotone

/-- The literal intersected filtration always admits a complete chief refinement. -/
theorem ChiefSeries.exists_complete_restriction_refinement [Finite K]
    (s : ChiefSeries K) (R : Subgroup K) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    ∃ (t : ChiefSeries R) (ι : Fin (s.length + 1) →o Fin (t.length + 1)),
      (∀ i, t (ι i) = restrictNormalNode R (s i)) ∧
      ι 0 = 0 ∧ ι (Fin.last s.length) = Fin.last t.length ∧
      t.head = ⊥ ∧ t.last = ⊤ := by
  obtain ⟨t, ι, hi, hi0, hi1⟩ := exists_refinement (s.restrictionFiltration R)
  refine ⟨t, ι, hi, hi0, hi1, ?_, ?_⟩
  · have h := hi 0
    rw [hi0] at h
    exact h.trans (by change restrictNormalNode R s.head = ⊥; rw [h0, restrictNormalNode_bot])
  · have h := hi (Fin.last s.length)
    rw [hi1] at h
    exact h.trans (by change restrictNormalNode R s.last = ⊤; rw [h1, restrictNormalNode_top])

end NoncentralChiefRefinement
