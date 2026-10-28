module

public import Theory.Representation.BinaryOffender.RestrictionComparison
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.OrbitQuotient
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Fixed-space obstruction for a pair of conjugate binary modules

If elementary actors have rank at most three, all involutions displace at
least four dimensions, and an index-two subgroup has rank at most two, a
putative `(F - 1)` offender must have rank three. Its nontrivial intersection
with the index-two subgroup has the same fixed space. A nonzero fixed vector
in one invariant summand then contradicts the interchange of disjoint summands
by an element outside that subgroup.

The final `Pair` structure describes actual representations and complementary
irreducible four-spaces for A₇ inside S₇. It contains none of the parameter
claims. Construction of a pair and the group and fixed-space calculations
remain separate obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.8,
printed p.389, PDF p.400; standing hypotheses on printed p.377.
-/

@[expose] public section

namespace Representation.AlternatingSevenConjugatePair

open BinaryOffender

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [Finite G] in
private theorem codim_mono (ρ : Representation (ZMod 2) G V)
    {A B : Subgroup G} (hBA : B ≤ A) : fixedCodim ρ B ≤ fixedCodim ρ A := by
  have hdim := Submodule.finrank_mono (fixedSpace_antitone ρ hBA)
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ B
  omega

omit [Finite G] in
/-- A common lower bound on involution displacement bounds every nontrivial
 elementary abelian actor. -/
theorem le_fixedCodim_of_involutions (ρ : Representation (ZMod 2) G V)
    {d : ℕ} (hd : ∀ t : G, orderOf t = 2 → d ≤ fixedCodim ρ (Subgroup.zpowers t))
    {A : Subgroup G} (hA : IsElementaryTwo A) : d ≤ fixedCodim ρ A := by
  let _ : IsElementaryAbelian 2 A := hA.2
  obtain ⟨t, htA, ht⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ht2 : orderOf t = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t htA) ht
  exact (hd t ht2).trans (codim_mono ρ (Subgroup.zpowers_le.mpr htA))

omit [Finite G] in
/-- Attaining the involution lower bound forces equality of fixed spaces on
 every nontrivial subgroup of an elementary abelian actor. -/
theorem fixedSpace_eq_of_attaining_involution_bound
    (ρ : Representation (ZMod 2) G V) {d : ℕ}
    (hd : ∀ t : G, orderOf t = 2 → d ≤ fixedCodim ρ (Subgroup.zpowers t))
    {A B : Subgroup G} (hA : IsElementaryTwo A) (hBA : B ≤ A) (hB : B ≠ ⊥)
    (hcodim : fixedCodim ρ A ≤ d) : fixedSpace ρ A = fixedSpace ρ B := by
  have hlow := le_fixedCodim_of_involutions ρ hd (hA.of_le hBA hB)
  have hmono := codim_mono ρ hBA
  apply Submodule.eq_of_le_of_finrank_eq (fixedSpace_antitone ρ hBA)
  have hA' := fixedCodim_add_finrank ρ A
  have hB' := fixedCodim_add_finrank ρ B
  omega

private theorem inf_ne_bot_of_rank_three {A L : Subgroup G}
    (hA : IsElementaryTwo A) (hr : rank A = 3) (hindex : L.index = 2) : A ⊓ L ≠ ⊥ := by
  let _ : L.Normal := L.normal_of_index_eq_two hindex
  have hdiv := L.relIndex_dvd_index_of_normal A
  rw [hindex, ← Subgroup.inf_relIndex_left] at hdiv
  intro he
  rw [he, Subgroup.relIndex_bot_left, hA.card_eq_two_pow_rank, hr] at hdiv
  norm_num at hdiv

omit [Finite G] in
private theorem exists_fixed_in_subspace (ρ : Representation (ZMod 2) G V)
    (B : Subgroup G) (hB : IsElementaryTwo B) (U : Submodule (ZMod 2) V)
    (hU : U ≠ ⊥) (hstable : ∀ b ∈ B, ∀ u ∈ U, ρ b u ∈ U) :
    ∃ u : V, u ∈ U ∧ u ≠ 0 ∧ u ∈ fixedSpace ρ B := by
  let _ : IsElementaryAbelian 2 B := hB.2
  let U' : Subrepresentation (ρ.comp B.subtype) :=
    { toSubmodule := U
      apply_mem_toSubmodule := fun b u hu => hstable b b.property u hu }
  let _ : Nontrivial U' := Submodule.nontrivial_iff_ne_bot.mpr hU
  obtain ⟨u, hu, hfix⟩ :=
    BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector
      U'.toRepresentation (IsElementaryAbelian.isPGroup 2 B)
  refine ⟨u, u.property, ?_, ?_⟩
  · intro h
    exact hu (Subtype.ext h)
  · intro b
    exact congrArg Subtype.val (hfix b)

/-- The summand-interchange argument for the `4 ⊕ 4̄` case. The finite group
 has elementary ranks at most three, its index-two subgroup has ranks at most
 two, and each involution displaces at least four dimensions. If the index-two
 subgroup preserves a nonzero summand and every outside element moves it to
 a disjoint subspace, no elementary actor is an `(F - 1)` offender.

The proof derives the nonzero fixed vector in the inner intersection from the
 two-group fixed-vector theorem; nonexistence of rank-three offenders is not
 an input. -/
theorem rank_add_one_lt_fixedCodim_of_swapped_summands
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) (hindex : L.index = 2)
    (U W : Submodule (ZMod 2) V) (hU : U ≠ ⊥) (hUW : Disjoint U W)
    (hstable : ∀ g ∈ L, ∀ u ∈ U, ρ g u ∈ U)
    (hswap : ∀ g ∉ L, ∀ u ∈ U, ρ g u ∈ W)
    (hrank : ∀ A : Subgroup G, IsElementaryTwo A → rank A ≤ 3)
    (hinner : ∀ A : Subgroup G, IsElementaryTwo A → A ≤ L → rank A ≤ 2)
    (hinv : ∀ t : G, orderOf t = 2 → 4 ≤ fixedCodim ρ (Subgroup.zpowers t))
    {A : Subgroup G} (hA : IsElementaryTwo A) : rank A + 1 < fixedCodim ρ A := by
  by_contra h
  have hcodim : fixedCodim ρ A ≤ rank A + 1 := Nat.le_of_not_gt h
  have hlow := le_fixedCodim_of_involutions ρ hinv hA
  have hr := hrank A hA
  have hr3 : rank A = 3 := by omega
  have hupper : fixedCodim ρ A ≤ 4 := by omega
  have hnot : ¬ A ≤ L := by
    intro hAL
    have := hinner A hA hAL
    omega
  obtain ⟨a, ha, haL⟩ : ∃ a ∈ A, a ∉ L := by
    by_contra hn
    apply hnot
    intro a ha
    by_contra haL
    exact hn ⟨a, ha, haL⟩
  have hB := inf_ne_bot_of_rank_three hA hr3 hindex
  have hfix := fixedSpace_eq_of_attaining_involution_bound ρ hinv hA
    (show A ⊓ L ≤ A from inf_le_left) hB hupper
  obtain ⟨u, hu, hune, hufix⟩ := exists_fixed_in_subspace ρ (A ⊓ L)
    (hA.of_le inf_le_left hB) U hU (fun g hg v hv => hstable g hg.2 v hv)
  have huA : u ∈ fixedSpace ρ A := hfix ▸ hufix
  have hau : ρ a u = u := huA ⟨a, ha⟩
  have huW : u ∈ W := hau ▸ hswap a haL u hu
  exact hune (Submodule.disjoint_def.mp hUW u hu huW)

/-- An actual S₇ action whose restriction is a pair of interchanged
 irreducible binary four-spaces. The two actual A₇ representations must be inequivalent; construction of
 this structure is a theorem obligation, not a parameter assumption. -/
structure Pair (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] where
  representation : Representation (ZMod 2) (Equiv.Perm (Fin 7)) V
  faithful : Function.Injective representation
  first : Subrepresentation (representation.comp (alternatingGroup (Fin 7)).subtype)
  second : Subrepresentation (representation.comp (alternatingGroup (Fin 7)).subtype)
  complementary : IsCompl first.toSubmodule second.toSubmodule
  first_dim : Module.finrank (ZMod 2) first.toSubmodule = 4
  second_dim : Module.finrank (ZMod 2) second.toSubmodule = 4
  first_irreducible : IsIrreducible first.toRepresentation
  second_irreducible : IsIrreducible second.toRepresentation
  inequivalent : ¬ Nonempty (first.toRepresentation.Equiv second.toRepresentation)
  swap_first : ∀ g : Equiv.Perm (Fin 7), g ∉ alternatingGroup (Fin 7) →
    ∀ u ∈ first.toSubmodule, representation g u ∈ second.toSubmodule
  swap_second : ∀ g : Equiv.Perm (Fin 7), g ∉ alternatingGroup (Fin 7) →
    ∀ u ∈ second.toSubmodule, representation g u ∈ first.toSubmodule

/-- Fixed vectors lying in the first summand. This remains meaningful for
 actors outside A₇, which do not preserve that summand. -/
noncomputable def Pair.firstFixedSpace (D : Pair V)
    (A : Subgroup (Equiv.Perm (Fin 7))) : Submodule (ZMod 2) V :=
  D.first.toSubmodule ⊓ fixedSpace D.representation A

/-- Fixed vectors lying in the second summand. -/
noncomputable def Pair.secondFixedSpace (D : Pair V)
    (A : Subgroup (Equiv.Perm (Fin 7))) : Submodule (ZMod 2) V :=
  D.second.toSubmodule ⊓ fixedSpace D.representation A

end Representation.AlternatingSevenConjugatePair
