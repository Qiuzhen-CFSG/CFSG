module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupAction.Invariant
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!
# Indecomposability from a fixed subgroup of order two

Suppose a finite two-group acts on a finite elementary abelian two-group
`V`, and its fixed subgroup has order two. Two disjoint invariant subgroups
of `V` cannot both be nontrivial. In particular, an invariant complementary
pair has a trivial member.

Orbit counting gives a nonidentity fixed element in each nontrivial
invariant subgroup. The ambient fixed subgroup has a unique nonidentity
element, so the two elements coincide, contradicting disjointness. The
restricted actions use the supplied invariance instances throughout.

This standard modular action observation supplies the invariant-summand
transfer for the sixteen-element exceptional module in Stellmacher (1.6),
journal p.18; see `refs/latex/stellmacher-n-group.tex`.
-/

private theorem exists_nonidentity_fixed_invariant
    {A V : Type*} [Group A] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction A V]
    (hA : IsPGroup 2 A) (D : Subgroup V) [IsInvariant A V D]
    (hD : D ≠ ⊥) :
    ∃ d : V, d ∈ D ∧ d ∈ FixedPoints.subgroup A V ∧ d ≠ 1 := by
  have hDp : IsPGroup 2 D := (IsElementaryAbelian.isPGroup 2 V).to_subgroup D
  have hcard : Nat.card D ≠ 1 := fun hd => hD (Subgroup.card_eq_one.mp hd)
  have hdiv : 2 ∣ Nat.card D := hDp.card_eq_or_dvd.resolve_left hcard
  have hone : (1 : D) ∈ MulAction.fixedPoints A D := by
    simp [MulAction.mem_fixedPoints]
  obtain ⟨d, hd, hne⟩ :=
    hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := D) hdiv hone
  refine ⟨d, d.property, ?_, ?_⟩
  · rw [FixedPoints.mem_subgroup]
    intro a
    exact congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hd) a)
  · intro heq
    exact hne (Subtype.ext heq.symm)

/-- A subgroup of order at most two containing the common fixed points lies
in every nontrivial invariant subgroup of an elementary binary two-group module. -/
public theorem subgroup_le_invariant_of_fixed_le_of_card_le_two
    {A V : Type*} [Group A] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction A V]
    (hA : IsPGroup 2 A) (F : Subgroup V)
    (hF : FixedPoints.subgroup A V ≤ F) (hcard : Nat.card F ≤ 2)
    (D : Subgroup V) [IsInvariant A V D] (hD : D ≠ ⊥) : F ≤ D := by
  obtain ⟨d, hdD, hdF, hdne⟩ := exists_nonidentity_fixed_invariant hA D hD
  have hne : D ⊓ F ≠ ⊥ := by
    intro heq
    have hd : d ∈ D ⊓ F := ⟨hdD, hF hdF⟩
    rw [heq] at hd
    exact hdne hd
  have hc := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have heq : D ⊓ F = F :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
  exact heq ▸ inf_le_left

/-- Disjoint invariant subgroups cannot both be nontrivial when the fixed
subgroup of a two-group action has order two. -/
public theorem eq_bot_or_eq_bot_of_disjoint_of_fixed_card_two
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction A V]
    (hA : IsPGroup 2 A) (hfixed : Nat.card (FixedPoints.subgroup A V) = 2)
    (D E : Subgroup V) [IsInvariant A V D] [IsInvariant A V E]
    (hDE : Disjoint D E) : D = ⊥ ∨ E = ⊥ := by
  by_cases hD : D = ⊥
  · exact Or.inl hD
  right
  by_contra hE
  obtain ⟨d, hdD, hdF, hdne⟩ := exists_nonidentity_fixed_invariant hA D hD
  obtain ⟨e, heE, heF, hene⟩ := exists_nonidentity_fixed_invariant hA E hE
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : FixedPoints.subgroup A V)).mp hfixed
  have hd : (⟨d, hdF⟩ : FixedPoints.subgroup A V) ≠ 1 :=
    fun heq => hdne (congrArg Subtype.val heq)
  have he : (⟨e, heF⟩ : FixedPoints.subgroup A V) ≠ 1 :=
    fun heq => hene (congrArg Subtype.val heq)
  have hde : d = e := congrArg Subtype.val ((hz _ hd).trans (hz _ he).symm)
  have hdin : d ∈ D ⊓ E := ⟨hdD, hde ▸ heE⟩
  rw [hDE.eq_bot] at hdin
  exact hdne hdin

/-- An invariant complementary pair has a trivial member if the fixed
subgroup of a two-group action has order two. -/
public theorem eq_bot_or_eq_bot_of_isCompl_of_fixed_card_two
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction A V]
    (hA : IsPGroup 2 A) (hfixed : Nat.card (FixedPoints.subgroup A V) = 2)
    (D E : Subgroup V) [IsInvariant A V D] [IsInvariant A V E]
    (hDE : IsCompl D E) : D = ⊥ ∨ E = ⊥ :=
  eq_bot_or_eq_bot_of_disjoint_of_fixed_card_two hA hfixed D E hDE.disjoint
