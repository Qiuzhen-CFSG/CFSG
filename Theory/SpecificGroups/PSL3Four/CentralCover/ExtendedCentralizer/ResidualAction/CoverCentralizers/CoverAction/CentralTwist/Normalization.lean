module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.Reduction
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.ProjectiveFixer

/-!
# Normalizing the projective coordinates of the marked graph-field lift

The projected E₉ residual is a Sylow three-subgroup of PSL₃(4). Its pointwise
fixer in the standard automorphism group is the product of its inner action
with the standard graph-field involution. That product has just one nonidentity
involution. Sylow conjugacy therefore normalizes the marked graph-field action
by an inner automorphism of the actual projective group.

Postcomposing the covering projection with this inner automorphism keeps L,
the marked action on L, its fixed residual, and all eventual twist witnesses
unchanged. The full standard automorphism-lifting property is preserved too.
No simultaneous conjugacy of the graph and field representatives is used.
The lifting property also constructs compatible graph and field automorphisms
whose product is the specified action, by faithful descent of the perfect cover.

This establishes the coordinate reduction, not the nonidentity central twist.
Source: Aschbacher--Smith 15.3.38, printed pp.1136--1137, manuscript of
1 March 2004.
-/

public section

open Subgroup
open scoped Pointwise
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.CentralTwist
open ProjectiveFixer

private theorem modelInner_eq_one_of_square (x : model) (hx : modelInner x ^ 2 = 1) :
    modelInner x = 1 := by
  have h9 : modelInner x ^ 9 = 1 := by
    rw [← map_pow]
    have h : x ^ 9 = 1 := by simpa only [model_card] using (pow_card_eq_one' : x ^ Nat.card model = 1)
    rw [h, map_one]
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 9)
    (orderOf_dvd_of_pow_eq_one hx) (orderOf_dvd_of_pow_eq_one h9))

private theorem candidate_involution (a : MulAut PSL) (ha : a ∈ candidate)
    (h2 : a ^ 2 = 1) (hne : a ≠ 1) : a = graphField := by
  obtain ⟨⟨x, t⟩, rfl⟩ := ha
  have ht : t = 1 ∨ t = Multiplicative.ofAdd (1 : ZMod 2) := by
    change t.toAdd = (0 : ZMod 2) ∨ t.toAdd = 1
    change ZMod 2 at t
    fin_cases t <;> decide
  rcases ht with rfl | rfl
  · change modelInner x * involutionHom graphField graphField_sq 1 ≠ 1 at hne
    change (modelInner x * involutionHom graphField graphField_sq 1) ^ 2 = 1 at h2
    simp only [map_one, mul_one] at hne h2
    exact (hne (modelInner_eq_one_of_square x h2)).elim
  · change modelInner x * involutionHom graphField graphField_sq
      (Multiplicative.ofAdd (1 : ZMod 2)) = graphField
    rw [involutionHom_generator]
    change (modelInner x * involutionHom graphField graphField_sq
      (Multiplicative.ofAdd (1 : ZMod 2))) ^ 2 = 1 at h2
    rw [involutionHom_generator, (modelInner_commute_graphField x).mul_pow,
      graphField_sq, mul_one] at h2
    rw [modelInner_eq_one_of_square x h2, one_mul]

private theorem model_fixer_involution (a : MulAut PSL) (ha : a ∈ fixer model)
    (h2 : a ^ 2 = 1) (hne : a ≠ 1) : a = graphField := by
  apply candidate_involution a _ h2 hne
  rwa [← model_fixer_eq_candidate]

/-- Standard lifting constructs compatible factors of the specified graph-field action.
These are new factors; they need not equal any originally marked graph and field pair. -/
theorem compatible_actions_for_standard_lift {E : Type*} [Group E]
    (c : FourCover E) (a : MulAut E)
    (hlift : PSL3.OuterSolvable.standard F ≤ (c.toCover.autMap c.ker_eq_center).range)
    (hcompat : ∀ x : E, c.toMonoidHom (a x) = graphField (c.toMonoidHom x)) :
    ∃ b : CoverActions E c, b.graphField = a := by
  obtain ⟨g, hg⟩ := hlift (PSL3.OuterSolvable.graph_mem_standard F)
  have hfmem : pslFrobenius ∈ PSL3.OuterSolvable.standard F := by
    rw [frobenius_eq_fieldAction]
    exact PSL3.OuterSolvable.fieldAction_mem_standard F _
  obtain ⟨f, hf⟩ := hlift hfmem
  let b : CoverActions E c := {
    graph := g
    field := f
    graph_compatible := fun x => by rw [← c.toCover.autMap_apply c.ker_eq_center, hg]
    field_compatible := fun x => by rw [← c.toCover.autMap_apply c.ker_eq_center, hf] }
  refine ⟨b, ?_⟩
  apply c.toCover.autMap_injective c.ker_eq_center
  ext x
  obtain ⟨y, rfl⟩ := c.surjective x
  rw [c.toCover.autMap_apply, c.toCover.autMap_apply, b.graphField_compatible, hcompat]
  rfl

variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]

/-- A nonidentity involution fixing the projected E₉ is inner-conjugate to the standard graph-field action. -/
theorem projective_inner_normalization (d : Overgroup L) (w : I)
    (e : pResidual 2 (MulAut.conjNormal w : MulAut L).fixedSubgroup ≃* ElementaryNine)
    (h2 : w ^ 2 = 1) (hne : projectiveAction L d.cover w ≠ 1) :
    ∃ g : PSL, MulAut.conj g * projectiveAction L d.cover w * (MulAut.conj g)⁻¹ =
      graphField := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL (projectedResidualSylow d.cover w e) sylow
  have hp : (projectedResidual d.cover w).map (MulAut.conj g).toMonoidHom = model := by
    rw [← projectedResidualSylow_coe d.cover w e, ← sylow_coe, ← hg,
      Sylow.coe_subgroup_smul]
    rfl
  have hw : projectiveAction L d.cover w ∈ fixer (projectedResidual d.cover w) := by
    constructor
    · rw [← d.full_action]
      exact ⟨w, rfl⟩
    · rintro ⟨r, s, rfl⟩
      change d.cover.toCover.autMap d.cover.ker_eq_center (MulAut.conjNormal w)
        (d.cover.toMonoidHom (residualToLinear w s)) = _
      rw [d.cover.toCover.autMap_apply]
      apply congrArg d.cover.toMonoidHom
      apply Subtype.ext
      change w * s.val.val * w⁻¹ = s.val.val
      rw [← mem_centralizer_singleton_iff.mp s.val.property, mul_inv_cancel_right]
  refine ⟨g, model_fixer_involution _ ?_ ?_ ?_⟩
  · rw [← hp, ← fixer_map _ (MulAut.conj g)
      (PSL3.OuterSolvable.inner_le_standard F ⟨g, rfl⟩)]
    exact mem_map_of_mem (MulAut.conj (MulAut.conj g)).toMonoidHom hw
  · change (MulAut.conj (MulAut.conj g) (projectiveAction L d.cover w)) ^ 2 = 1
    rw [← map_pow, ← map_pow, h2, map_one, map_one]
  · change MulAut.conj (MulAut.conj g) (projectiveAction L d.cover w) ≠ 1
    intro he
    apply hne
    exact (MulAut.conj (MulAut.conj g)).injective (he.trans (map_one _).symm)

private noncomputable def rebase {E : Type*} [Group E] (c : FourCover E) (b : MulAut PSL) :
    FourCover E where
  toMonoidHom := b.toMonoidHom.comp c.toMonoidHom
  surjective := b.surjective.comp c.surjective
  isPerfect := c.isPerfect
  ker_le_center := by
    intro x hx
    apply c.ker_le_center
    exact b.injective (hx.trans (map_one b).symm)
  ker_eq_center := by
    ext x
    change b (c.toMonoidHom x) = 1 ↔ x ∈ center E
    rw [← map_one b, b.injective.eq_iff]
    change x ∈ c.toMonoidHom.ker ↔ _
    rw [c.ker_eq_center]
  center_isKleinFour := c.center_isKleinFour

private theorem rebase_autMap {E : Type*} [Group E] (c : FourCover E) (b : MulAut PSL)
    (a : MulAut E) :
    (rebase c b).toCover.autMap (rebase c b).ker_eq_center a =
      b * c.toCover.autMap c.ker_eq_center a * b⁻¹ := by
  ext y
  obtain ⟨x, rfl⟩ := (rebase c b).surjective y
  rw [(rebase c b).toCover.autMap_apply]
  change b (c.toMonoidHom (a x)) =
    (b * c.toCover.autMap c.ker_eq_center a * b⁻¹) (b (c.toMonoidHom x))
  simp only [MulAut.mul_apply, MulAut.inv_apply_self, c.toCover.autMap_apply]

private theorem rebase_standard_lifts (d : Overgroup L) (b : MulAut PSL)
    (hb : b ∈ PSL3.OuterSolvable.standard F) :
    PSL3.OuterSolvable.standard F ≤
      ((rebase d.cover b).toCover.autMap (rebase d.cover b).ker_eq_center).range := by
  intro a ha
  have ht : b⁻¹ * a * b ∈ PSL3.OuterSolvable.standard F :=
    (PSL3.OuterSolvable.standard F).mul_mem
      ((PSL3.OuterSolvable.standard F).mul_mem
        ((PSL3.OuterSolvable.standard F).inv_mem hb) ha) hb
  rw [← d.full_action] at ht
  obtain ⟨x, hx⟩ := ht
  refine ⟨MulAut.conjNormal x, ?_⟩
  rw [rebase_autMap]
  change b * projectiveAction L d.cover x * b⁻¹ = a
  rw [hx]
  group

/-- Rechoose only the projective coordinates; the cover group and marked automorphism stay fixed.
Every standard projective automorphism still lifts through this covering map. -/
theorem standard_cover_for_marked_action (d : Overgroup L) (n : NormalizerGeometry d)
    (e : pResidual 2 (MulAut.conjNormal n.graphFieldI : MulAut L).fixedSubgroup ≃*
      ElementaryNine) :
    ∃ (g : PSL) (c : FourCover L),
      c.toMonoidHom = (MulAut.conj g).toMonoidHom.comp d.cover.toMonoidHom ∧
      PSL3.OuterSolvable.standard F ≤ (c.toCover.autMap c.ker_eq_center).range ∧
      ∀ x : L, c.toMonoidHom ((MulAut.conjNormal n.graphFieldI : MulAut L) x) =
        graphField (c.toMonoidHom x) := by
  obtain ⟨g, hg⟩ := projective_inner_normalization d n.graphFieldI e n.graphField_sq
    n.graphField_projective_ne_one
  refine ⟨g, rebase d.cover (MulAut.conj g), rfl,
    rebase_standard_lifts d _ (PSL3.OuterSolvable.inner_le_standard F ⟨g, rfl⟩), ?_⟩
  intro x
  change (MulAut.conj g) (d.cover.toMonoidHom (MulAut.conjNormal n.graphFieldI x)) =
    graphField (MulAut.conj g (d.cover.toMonoidHom x))
  rw [← d.cover.toCover.autMap_apply d.cover.ker_eq_center]
  have hh := congrArg (fun a : MulAut PSL => a (MulAut.conj g (d.cover.toMonoidHom x))) hg
  simpa only [MulAut.mul_apply, MulAut.inv_apply_self, projectiveAction,
    MonoidHom.comp_apply] using hh

end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.CentralTwist
