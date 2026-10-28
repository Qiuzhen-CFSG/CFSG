module
public import Theory.Representation.BinaryOffender.DistinctHeadBudget
public import Theory.Representation.BinaryAlternatingSixModels.Geometry
public import Theory.Representation.AlternatingSixInvolutionDisplacement
public import Theory.ElementaryAbelian.Injective

/-!
# The combined cost of the two marked natural A₆ heads

Inflation along a surjection retains the inequivalence of the duad and
syntheme natural modules. The distinct-head inequality therefore adds their
fixed codimensions on every actor subgroup, without a direct-sum hypothesis.
Every nonidentity involution in A₆ moves at least two dimensions on each
natural module. Elementary A₆ subgroups have rank at most two, so their
combined cost exceeds the near-maximum bound of image rank plus one.

This treats actors inside the component. An extension of A₆ can have outer
involutions and still requires the separate simultaneous-transvection and
strong-offender exclusions. Source: Aschbacher--Smith 13.4.7(1iv), p.901.
-/

public noncomputable section
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Theory.SpecificGroups.SymmetricSix BinaryDuadModule
namespace BinaryAlternatingSix
variable {H M M₁ M₂ : Type*} [Group H]
  [AddCommGroup M] [Module (ZMod 2) M]
  [AddCommGroup M₁] [Module (ZMod 2) M₁]
  [AddCommGroup M₂] [Module (ZMod 2) M₂]

/-- The two natural heads, inflated along one actual quotient, have additive cost. -/
theorem paired_head_fixedCodim
    (f : H →* A6) (hf : Function.Surjective f)
    (ρ : Representation (ZMod 2) H M)
    (ρ₁ : Representation (ZMod 2) H M₁) (ρ₂ : Representation (ZMod 2) H M₂)
    [FiniteDimensional (ZMod 2) M]
    (i : ρ₁.IntertwiningMap ρ) (hi : Function.Injective i)
    (j : ρ₂.IntertwiningMap ρ) (hj : Function.Injective j)
    (p : ρ₁.IntertwiningMap (firstAlternating.comp f)) (hp : Function.Surjective p)
    (q : ρ₂.IntertwiningMap (secondAlternating.comp f)) (hq : Function.Surjective q)
    (A : Subgroup H) :
    fixedCodim firstAlternating (A.map f) + fixedCodim secondAlternating (A.map f) ≤
      fixedCodim ρ A := by
  let : IsIrreducible (firstAlternating.comp f) :=
    (irreducible_comp_surjective_iff f hf firstAlternating).mpr firstAlternating_irreducible
  let : IsIrreducible (secondAlternating.comp f) :=
    (irreducible_comp_surjective_iff f hf secondAlternating).mpr secondAlternating_irreducible
  have hne : ¬ Nonempty (Representation.Equiv (firstAlternating.comp f)
      (secondAlternating.comp f)) := by
    rintro ⟨e⟩
    apply natural_inequivalent.false
    refine Representation.Equiv.mk e.toLinearEquiv ?_
    intro g
    obtain ⟨a,rfl⟩ := hf g
    exact e.isIntertwining' a
  have hh := fixedCodim_add_le_of_distinct_embedded_heads ρ ρ₁ ρ₂
    (firstAlternating.comp f) (secondAlternating.comp f) i hi j hj p hp q hq hne A
  have h1 := fixedCodim_map_equivariant (firstAlternating.comp f) firstAlternating f
    (LinearEquiv.refl (ZMod 2) NaturalModule) (fun _ _ => rfl) A
  have h2 := fixedCodim_map_equivariant (secondAlternating.comp f) secondAlternating f
    (LinearEquiv.refl (ZMod 2) NaturalModule) (fun _ _ => rfl) A
  rwa [h1,h2] at hh

private theorem natural_actions_nontrivial :
    (∃ g : A6, firstAlternating g ≠ 1) ∧ (∃ g : A6, secondAlternating g ≠ 1) := by
  have hfirst : ∃ g : A6, firstAlternating g ≠ 1 := by
    by_contra! h
    apply first_has_no_line
    refine ⟨polarLine 0,polarLine_finrank 0,?_⟩
    intro g _ v hv
    rw [h g]
    exact hv
  refine ⟨hfirst,?_⟩
  obtain ⟨g,hg⟩ := hfirst
  refine ⟨alternatingDiagramAut.symm g,?_⟩
  intro he
  apply hg
  change firstAlternating (alternatingDiagramAut (alternatingDiagramAut.symm g)) = 1 at he
  simpa only [MulEquiv.apply_symm_apply] using he

/-- Every actor whose A₆ image contains an involution costs at least four
on a module containing both marked natural heads. -/
theorem four_le_fixedCodim_of_paired_heads
    (f : H →* A6) (hf : Function.Surjective f)
    (ρ : Representation (ZMod 2) H M)
    (ρ₁ : Representation (ZMod 2) H M₁) (ρ₂ : Representation (ZMod 2) H M₂)
    [FiniteDimensional (ZMod 2) M]
    (i : ρ₁.IntertwiningMap ρ) (hi : Function.Injective i)
    (j : ρ₂.IntertwiningMap ρ) (hj : Function.Injective j)
    (p : ρ₁.IntertwiningMap (firstAlternating.comp f)) (hp : Function.Surjective p)
    (q : ρ₂.IntertwiningMap (secondAlternating.comp f)) (hq : Function.Surjective q)
    (A : Subgroup H) (a : A6) (ha : orderOf a = 2) (haA : a ∈ A.map f) :
    4 ≤ fixedCodim ρ A := by
  have h1 := AlternatingSixInvolutionDisplacement.fixedCodim_lower_of_involution_mem
    firstAlternating natural_actions_nontrivial.1 a ha haA
  have h2 := AlternatingSixInvolutionDisplacement.fixedCodim_lower_of_involution_mem
    secondAlternating natural_actions_nontrivial.2 a ha haA
  have h3 := paired_head_fixedCodim f hf ρ ρ₁ ρ₂ i hi j hj p hp q hq A
  omega
private theorem borel_not_elementary : ¬ IsElementaryAbelian 2 a6Borel := by
  intro h
  let := h
  let a : A6 := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide⟩
  let b : A6 := ⟨Equiv.swap 2 4 * Equiv.swap 3 5, by decide⟩
  have ha : a ∈ a6Borel := by decide
  have hb : b ∈ a6Borel := by decide
  have he := congrArg (fun x : a6Borel => x.val.val)
    (mul_comm (⟨a,ha⟩ : a6Borel) ⟨b,hb⟩)
  have hn : a.val * b.val ≠ b.val * a.val := by decide
  exact hn he

/-- An elementary subgroup of the marked A₆ has rank at most two. -/
theorem elementary_rank_le_two (A : Subgroup A6) [IsElementaryAbelian 2 A] :
    rank A ≤ 2 := by
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  have hcard : Nat.card (S : Subgroup A6) = 8 :=
    (Nat.card_congr (Sylow.equiv S a6BorelSylow).toEquiv).trans a6Borel_order
  have hlt : Nat.card A < 8 := by
    have hle := Subgroup.card_le_of_le hAS
    rw [hcard] at hle
    apply lt_of_le_of_ne hle
    intro he
    have hEq : A = (S : Subgroup A6) := Subgroup.eq_of_le_of_card_ge hAS (by omega)
    have hS : IsElementaryAbelian 2 (S : Subgroup A6) := hEq ▸ inferInstance
    let := hS
    exact borel_not_elementary (IsElementaryAbelian.of_injective
      (Sylow.equiv S a6BorelSylow).symm.toMonoidHom (Sylow.equiv S a6BorelSylow).symm.injective)
  exact (Nat.log_mono_right (Nat.le_pred_of_lt hlt)).trans (by decide : Nat.log 2 7 ≤ 2)

/-- The paired natural factors exclude every near-maximum budget within
the component quotient, retaining the full kernel of the marking. -/
theorem paired_heads_exceed_near_maximum_budget
    (f : H →* A6) (hf : Function.Surjective f)
    (ρ : Representation (ZMod 2) H M)
    (ρ₁ : Representation (ZMod 2) H M₁) (ρ₂ : Representation (ZMod 2) H M₂)
    [FiniteDimensional (ZMod 2) M]
    (i : ρ₁.IntertwiningMap ρ) (hi : Function.Injective i)
    (j : ρ₂.IntertwiningMap ρ) (hj : Function.Injective j)
    (p : ρ₁.IntertwiningMap (firstAlternating.comp f)) (hp : Function.Surjective p)
    (q : ρ₂.IntertwiningMap (secondAlternating.comp f)) (hq : Function.Surjective q)
    (A : Subgroup H) (hA : IsElementaryTwo (A.map f)) :
    rank (A.map f) + 1 < fixedCodim ρ A := by
  let := hA.2
  obtain ⟨b,hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1
  let a : A6 := b.val
  have ha : a ∈ A.map f := b.property
  have han : a ≠ 1 := fun hh => hb (Subtype.ext hh)
  have ho : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) han
  have hfour := four_le_fixedCodim_of_paired_heads f hf ρ ρ₁ ρ₂ i hi j hj p hp q hq A a ho ha
  have hr := elementary_rank_le_two (A.map f)
  omega
end BinaryAlternatingSix
