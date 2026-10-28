module

public import Theory.Representation.BinaryNaturalDual.FourActors.Model
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic

/-!
# Outer involutions on the marked natural-plus-dual module

Inner/inverse-transpose coverage shows that every outer actor exchanges the
natural and dual summands. For an involution the literal diagonal map identifies
the natural module with both the fixed space and the displacement image. It
intertwines the actual inner centralizer, without changing the natural marking.

For a commuting actor subgroup containing such an involution, this same map
restricts to an equivalence from the natural fixed space of its inner part.
The index-two inner subgroup supplies the other coset, so fixing the inner part
and the chosen outer actor fixes the entire subgroup. No actor classification
or numerical dimension of that restricted fixed space is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.3(2,6),
printed pp.391–392, PDF pp.402–403.
-/

@[expose] public section

namespace BinaryNaturalDual.FourActors
open BinaryLinear.OuterCyclic

variable (d : CoordinateAction 4)

def action : M →* (V ≃ₗ[ZMod 2] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
    d.representation.asGroupHom
@[simp] theorem action_apply (a : M) (v : V) : action d a v = d.representation a v := rfl

def naturalSummand : Submodule (ZMod 2) V := (LinearMap.inl (ZMod 2) X _).range
def dualSummand : Submodule (ZMod 2) V := (LinearMap.inr (ZMod 2) X _).range
noncomputable def naturalSummandEquiv : X ≃ₗ[ZMod 2] naturalSummand :=
  LinearEquiv.ofInjective (LinearMap.inl (ZMod 2) X _) (LinearMap.inl_injective)

theorem summands_complementary : IsCompl naturalSummand dualSummand :=
  LinearMap.isCompl_range_inl_inr

@[simp] theorem mem_naturalSummand (v : V) : v ∈ naturalSummand ↔ v.2 = 0 := by
  change (∃ x : X, (x, 0) = v) ↔ v.2 = 0
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro hv
    exact ⟨v.1, Prod.ext rfl hv.symm⟩
@[simp] theorem mem_dualSummand (v : V) : v ∈ dualSummand ↔ v.1 = 0 := by
  change (∃ f : Module.Dual (ZMod 2) X, (0, f) = v) ↔ v.1 = 0
  constructor
  · rintro ⟨f, rfl⟩
    rfl
  · intro hv
    exact ⟨v.2, Prod.ext hv.symm rfl⟩

theorem outer_natural (a : M) (ha : a ∉ inner) (v : V) (hv : v ∈ naturalSummand) :
    action d a v ∈ dualSummand := by
  obtain ⟨g, hg | hg⟩ := inner_graph (Or.inl rfl) a
  · exact (ha ⟨g, hg.symm⟩).elim
  · rw [hg, action_apply, map_mul]
    change d.representation (graphLinear 4) (d.representation (MulAut.conj g) v) ∈ dualSummand
    rw [d.on_inner, d.on_graph, naturalDualRepresentation_apply, mem_dualSummand,
      coordinateSwap_apply]
    have hv0 := (mem_naturalSummand v).mp hv
    simp [hv0]

theorem outer_dual (a : M) (ha : a ∉ inner) (v : V) (hv : v ∈ dualSummand) :
    action d a v ∈ naturalSummand := by
  obtain ⟨g, hg | hg⟩ := inner_graph (Or.inl rfl) a
  · exact (ha ⟨g, hg.symm⟩).elim
  · rw [hg, action_apply, map_mul]
    change d.representation (graphLinear 4) (d.representation (MulAut.conj g) v) ∈ naturalSummand
    rw [d.on_inner, d.on_graph, naturalDualRepresentation_apply, mem_naturalSummand,
      coordinateSwap_apply]
    have hv0 := (mem_dualSummand v).mp hv
    simp [hv0]

theorem action_involutive (a : M) (ha : a ^ 2 = 1) :
    Function.Involutive (action d a) := by
  intro v
  have h : action d a * action d a = 1 := by rw [← map_mul, ← pow_two, ha, map_one]
  exact congrArg (fun e : V ≃ₗ[ZMod 2] V => e v) h

noncomputable def outerDiagonalEquiv (a : M) (ha : a ^ 2 = 1) (hout : a ∉ inner) :
    X ≃ₗ[ZMod 2] fixedSpace (action d a) :=
  naturalSummandEquiv.trans (diagonalEquiv summands_complementary (action d a)
    (action_involutive d a ha) (outer_natural d a hout) (outer_dual d a hout))

@[simp] theorem outerDiagonalEquiv_apply (a : M) (ha : a ^ 2 = 1) (hout : a ∉ inner) (x : X) :
    (outerDiagonalEquiv d a ha hout x : V) = (x, 0) + d.representation a (x, 0) := rfl

theorem outer_fixedSpace_eq_displacement (a : M) (ha : a ^ 2 = 1) (hout : a ∉ inner) :
    fixedSpace (action d a) = LinearMap.range (d.representation a - LinearMap.id) :=
  fixedSpace_eq_displacement summands_complementary (action d a)
    (action_involutive d a ha) (outer_natural d a hout) (outer_dual d a hout)

theorem outer_fixedSpace_finrank (a : M) (ha : a ^ 2 = 1) (hout : a ∉ inner) :
    Module.finrank (ZMod 2) (fixedSpace (action d a)) = 4 := by
  rw [← (outerDiagonalEquiv d a ha hout).finrank_eq]
  simp [X, BinaryLinear.OuterCyclic.Space]

theorem outerDiagonalEquiv_equivariant (a : M) (ha : a ^ 2 = 1) (hout : a ∉ inner)
    (g : G) (hg : a g = g) (x : X) :
    (outerDiagonalEquiv d a ha hout (g x) : V) =
      d.representation (MulAut.conj g) (outerDiagonalEquiv d a ha hout x : V) := by
  have hcomm : Commute (MulAut.conj g) a := by
    ext z : 1
    change g * a z * g⁻¹ = a (g * z * g⁻¹)
    rw [map_mul, map_mul, map_inv, hg]
  have hc : Function.Commute (action d (MulAut.conj g)) (action d a) := by
    intro v
    exact congrArg (fun e : V ≃ₗ[ZMod 2] V => e v) (hcomm.map (action d)).eq
  have hi : action d (MulAut.conj g) (x, 0) = (g x, 0) := by
    simp only [action_apply, d.on_inner, naturalDualRepresentation_apply, map_zero]
  simpa only [outerDiagonalEquiv_apply, action_apply, hi] using
    (diagonal_equivariant (action d a) (action d (MulAut.conj g)) hc (x, 0)).symm

/-- The diagonal parametrization retains the original natural coordinate. -/
@[simp] theorem outerDiagonalEquiv_fst (a : M) (ha : a ^ 2 = 1) (hout : a ∉ inner) (x : X) :
    (outerDiagonalEquiv d a ha hout x : V).1 = x := by
  have hs : (d.representation a (x, 0)).1 = 0 :=
    (mem_dualSummand _).mp (outer_natural d a hout (x, 0) (by simp))
  simp only [outerDiagonalEquiv_apply, Prod.fst_add, hs, add_zero]

/-- For a commuting actor subgroup containing an outer involution, the diagonal
map restricts precisely to the fixed vectors of its inner part. -/
theorem outerDiagonal_mem_actorFixed_iff (A : Subgroup M)
    (hcomm : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b)
    (a : M) (haA : a ∈ A) (ha : a ^ 2 = 1) (hout : a ∉ inner) (x : X) :
    (outerDiagonalEquiv d a ha hout x : V) ∈ actorFixed d A ↔ x ∈ naturalFixed A := by
  constructor
  · intro h
    apply (mem_naturalFixed A x).mpr
    intro g hg
    have he := (mem_actorFixed d A _).mp h (MulAut.conj g) hg
    rw [d.on_inner, naturalDualRepresentation_apply] at he
    have hf := congrArg Prod.fst he
    change g (outerDiagonalEquiv d a ha hout x : V).1 =
      (outerDiagonalEquiv d a ha hout x : V).1 at hf
    simpa only [outerDiagonalEquiv_fst] using hf
  · intro h
    have hfix (b : M) (hb : b ∈ A) (hbi : b ∈ inner) :
        d.representation b (outerDiagonalEquiv d a ha hout x : V) =
          (outerDiagonalEquiv d a ha hout x : V) := by
      obtain ⟨g, rfl⟩ := hbi
      have hg := (mem_naturalFixed A x).mp h g hb
      have hc : Function.Commute (action d (MulAut.conj g)) (action d a) := by
        intro v
        exact congrArg (fun e : V ≃ₗ[ZMod 2] V => e v)
          ((show Commute (MulAut.conj g) a from hcomm _ hb _ haA).map (action d)).eq
      have hi : action d (MulAut.conj g) (x, 0) = (x, 0) := by
        simp only [action_apply, d.on_inner, naturalDualRepresentation_apply, map_zero, hg]
      have he := diagonal_equivariant (action d a) (action d (MulAut.conj g)) hc (x, 0)
      rw [hi] at he
      exact he
    apply (mem_actorFixed d A _).mpr
    intro b hb
    by_cases hbi : b ∈ inner
    · exact hfix b hb hbi
    · have hci : b * a⁻¹ ∈ inner :=
        (Subgroup.mul_mem_iff_of_index_two inner_index).mpr
          (iff_of_false hbi (by simpa only [Subgroup.inv_mem_iff] using hout))
      have hca : b * a⁻¹ ∈ A := A.mul_mem hb (A.inv_mem haA)
      have hfa : d.representation a (outerDiagonalEquiv d a ha hout x : V) =
          (outerDiagonalEquiv d a ha hout x : V) :=
        (mem_fixedSpace _ _).mp (outerDiagonalEquiv d a ha hout x).property
      calc
        d.representation b (outerDiagonalEquiv d a ha hout x : V) =
            d.representation (b * a⁻¹)
              (d.representation a (outerDiagonalEquiv d a ha hout x : V)) := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
        _ = _ := by rw [hfa, hfix _ hca hci]

/-- The literal set equality used for `A₂` in H.9.3(6), before computing its dimension. -/
theorem actorFixed_eq_outer_diagonal (A : Subgroup M)
    (hcomm : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b)
    (a : M) (haA : a ∈ A) (ha : a ^ 2 = 1) (hout : a ∉ inner) (v : V) :
    v ∈ actorFixed d A ↔
      ∃ x ∈ naturalFixed (A ⊓ inner), (x, 0) + d.representation a (x, 0) = v := by
  rw [naturalFixed_inf_inner]
  constructor
  · intro hv
    have hfa : v ∈ fixedSpace (action d a) :=
      (mem_fixedSpace _ _).mpr ((mem_actorFixed d A v).mp hv a haA)
    obtain ⟨x, hx⟩ := (outerDiagonalEquiv d a ha hout).surjective ⟨v, hfa⟩
    have he : (outerDiagonalEquiv d a ha hout x : V) = v := congrArg Subtype.val hx
    refine ⟨x, (outerDiagonal_mem_actorFixed_iff d A hcomm a haA ha hout x).mp ?_, he⟩
    rwa [he]
  · rintro ⟨x, hx, rfl⟩
    exact (outerDiagonal_mem_actorFixed_iff d A hcomm a haA ha hout x).mpr hx

/-- The fixed module of a commuting group with an outer involution is linearly
isomorphic to the fixed natural module of its inner part, by the same literal map. -/
noncomputable def actorFixedEquiv (A : Subgroup M)
    (hcomm : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b)
    (a : M) (haA : a ∈ A) (ha : a ^ 2 = 1) (hout : a ∉ inner) :
    naturalFixed A ≃ₗ[ZMod 2] actorFixed d A := by
  let f : naturalFixed A →ₗ[ZMod 2] actorFixed d A := {
    toFun x := ⟨outerDiagonalEquiv d a ha hout x.val,
      (outerDiagonal_mem_actorFixed_iff d A hcomm a haA ha hout x.val).mpr x.property⟩
    map_add' x y := by
      apply Subtype.ext
      exact congrArg (fun z : fixedSpace (action d a) => (z : V))
        ((outerDiagonalEquiv d a ha hout).map_add x.val y.val)
    map_smul' c x := by
      apply Subtype.ext
      exact congrArg (fun z : fixedSpace (action d a) => (z : V))
        ((outerDiagonalEquiv d a ha hout).map_smul c x.val) }
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    apply (outerDiagonalEquiv d a ha hout).injective
    exact Subtype.ext (congrArg (fun z : actorFixed d A => (z : V)) h)
  · intro v
    obtain ⟨x, hx, he⟩ := (actorFixed_eq_outer_diagonal d A hcomm a haA ha hout v).mp v.property
    rw [naturalFixed_inf_inner] at hx
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩

theorem actorFixed_finrank (A : Subgroup M)
    (hcomm : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b)
    (a : M) (haA : a ∈ A) (ha : a ^ 2 = 1) (hout : a ∉ inner) :
    Module.finrank (ZMod 2) (actorFixed d A) =
      Module.finrank (ZMod 2) (naturalFixed (A ⊓ inner)) := by
  rw [naturalFixed_inf_inner]
  exact (actorFixedEquiv d A hcomm a haA ha hout).finrank_eq.symm

end BinaryNaturalDual.FourActors
