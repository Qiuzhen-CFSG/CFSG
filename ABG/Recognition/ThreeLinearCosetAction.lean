module

public import ABG.Recognition.ThreeLinearCharacters
public import Theory.Character.PermutationActionCharacter
public import Theory.GroupAction.SimpleCosets

/-!
# The thirteen-coset action in Wong's linear branch

Given an index-thirteen subgroup, its genuine complex permutation character
is `1 + χ₆`. Transitivity gives principal multiplicity one. Any nonprincipal
constituent other than χ₆ would have degree at least thirteen, exceeding the
remaining degree budget of twelve. Evaluating at the identity then gives
multiplicity one for χ₆. The character norm is two, so the action is doubly
transitive; simplicity makes the action faithful.

Source: W. J. Wong, “On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2” (1964), printed p.110, and ordinary permutation character
theory. This module assumes the subgroup and does not construct it.
-/

namespace ABG
open BenderGlauberman
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace ThreeGlobalDegreeData

variable {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)

private theorem identify_degree_thirteen_character (hG : Nat.card G = 5616)
    {φ : ClassFunction G} (hφ : IsCharacter φ) (hd : φ 1 = 13)
    (hprincipal : scalarProduct G φ 1 = 1) : φ = 1 + c.decomposition.χ 5 := by
  classical
  let I := {θ : ClassFunction G // IsIrreducibleCharacter θ}
  let p : I := ⟨1, isLinearCharacter_one.1⟩
  let s : I := ⟨c.decomposition.χ 5, c.decomposition.irreducible 5⟩
  have hps : p ≠ s := by
    intro heq
    have h := congrArg (fun θ : I => θ.1 1) heq
    change 1 = c.decomposition.χ 5 1 at h
    rw [c.sixth_degree_twelve hG] at h
    norm_num at h
  have hnat (θ : I) : ∃ n : ℕ, scalarProduct G φ θ.1 = (n : ℂ) := by
    obtain ⟨n, hn⟩ := scalarProduct_irr_char_nat θ.2 hφ
    refine ⟨n, ?_⟩
    rw [← scalarProduct_conj, ← hn]
    simp
  choose m hm using hnat
  have hmp : m p = 1 := by
    have h := (hm p).symm.trans hprincipal
    exact_mod_cast h
  have hgen : IsGeneralizedCharacter φ :=
    ⟨φ, 0, hφ, isCharacter_zero, (sub_zero φ).symm⟩
  have hexp (g : G) : φ g = ∑ θ : I, (m θ : ℂ) * θ.1 g := by
    simpa only [hm] using classFunction_eq_sum_irr_coeffs hgen g
  let f : I → ℝ := fun θ => (m θ : ℝ) * (θ.1 1).re
  have hf (θ : I) : 0 ≤ f θ :=
    mul_nonneg (Nat.cast_nonneg _) (le_trans (by norm_num) (irreducible_degree_ge_one θ.2))
  have hsum : ∑ θ : I, f θ = 13 := by
    have h := congrArg Complex.re (hexp 1)
    rw [hd] at h
    simpa [f, Complex.mul_re] using h.symm
  have hfp : f p = 1 := by simp [f, hmp, p]
  have hzero (θ : I) (hp : θ ≠ p) (hs : θ ≠ s) : m θ = 0 := by
    by_contra hm0
    have hmpos : (1 : ℝ) ≤ m θ := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm0)
    have hθ1 : θ.1 ≠ 1 := fun h => hp (Subtype.ext h)
    have hθ6 : θ.1 ≠ c.decomposition.χ 5 := fun h => hs (Subtype.ext h)
    have hdeg := c.linear_degree_ge_thirteen_of_ne_sixth hG θ.2 hθ1 hθ6
    have hlarge : 13 ≤ f θ := by dsimp [f]; nlinarith
    have hle : ∑ i ∈ ({p, θ} : Finset I), f i ≤ ∑ i : I, f i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => hf i)
    rw [Finset.sum_pair hp.symm, hfp, hsum] at hle
    linarith
  have hdecomp : φ = 1 + (m s : ℂ) • c.decomposition.χ 5 := by
    funext g
    rw [hexp]
    have hreduce : (∑ θ : I, (m θ : ℂ) * θ.1 g) =
        ∑ θ ∈ ({p, s} : Finset I), (m θ : ℂ) * θ.1 g := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro θ _ hθ
      have hnot : θ ≠ p ∧ θ ≠ s := by simpa using hθ
      rw [hzero θ hnot.1 hnot.2]
      simp
    rw [hreduce, Finset.sum_pair hps]
    simp [hmp, p, s]
  have hms : (m s : ℂ) = 1 := by
    have h := congrFun hdecomp 1
    simp only [Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul,
      c.sixth_degree_twelve hG, hd] at h
    linear_combination -h / 12
  simpa [hms] using hdecomp

/-- The genuine complex permutation representation of the action on `G/K`. -/
public abbrev cosetRepresentation (K : Subgroup G) : Representation ℂ G ((G ⧸ K) → ℂ) :=
  Representation.permutationAction G (G ⧸ K)

/-- The thirteen-coset permutation character is the principal character plus
Wong's sixth irreducible (index 5). -/
public theorem cosetRepresentation_character (hG : Nat.card G = 5616)
    (K : Subgroup G) (hK : K.index = 13) :
    (cosetRepresentation K).character = 1 + c.decomposition.χ 5 := by
  apply c.identify_degree_thirteen_character hG
  · exact Representation.permutationAction_isCharacter G (G ⧸ K)
  · rw [Representation.char_one]
    simp only [Module.finrank_pi, ← Nat.card_eq_fintype_card,
      ← Subgroup.index_eq_card, hK, Nat.cast_ofNat]
  · exact Representation.permutationAction_scalarProduct_one_of_pretransitive G (G ⧸ K)

/-- Every element fixes exactly `1 + χ₆(g)` cosets. -/
public theorem coset_fixedPoint_count (hG : Nat.card G = 5616)
    (K : Subgroup G) (hK : K.index = 13) (g : G) :
    (Nat.card (MulAction.fixedBy (G ⧸ K) g) : ℂ) = 1 + c.decomposition.χ 5 g := by
  rw [← Representation.permutationAction_character]
  exact congrFun (c.cosetRepresentation_character hG K hK) g

omit [Finite G] in
/-- Simplicity makes the thirteen-coset action faithful. -/
public theorem cosetAction_faithful [IsSimpleGroup G]
    (K : Subgroup G) (hK : K.index = 13) : FaithfulSMul G (G ⧸ K) := by
  apply K.faithfulSMul_quotient_of_simple
  intro htop
  simp [htop] at hK

include c in
/-- The thirteen-coset action is doubly transitive. -/
public theorem cosetAction_two_pretransitive (hG : Nat.card G = 5616)
    (K : Subgroup G) (hK : K.index = 13) :
    MulAction.IsMultiplyPretransitive G (G ⧸ K) 2 := by
  apply Representation.permutationAction_two_pretransitive_of_norm_two
  change scalarProduct G (cosetRepresentation K).character (cosetRepresentation K).character = 2
  rw [c.cosetRepresentation_character hG K hK]
  have hne : (1 : ClassFunction G) ≠ c.decomposition.χ 5 := by
    intro h
    have h1 := congrFun h 1
    rw [c.sixth_degree_twelve hG] at h1
    norm_num at h1
  rw [scalarProduct_add_left, scalarProduct_add_right, scalarProduct_add_right,
    irreducible_scalarProduct_self isLinearCharacter_one.1,
    irreducible_scalarProduct_self (c.decomposition.irreducible 5),
    irreducible_scalarProduct_of_ne isLinearCharacter_one.1 (c.decomposition.irreducible 5) hne,
    irreducible_scalarProduct_of_ne (c.decomposition.irreducible 5) isLinearCharacter_one.1 hne.symm]
  norm_num

end ThreeGlobalDegreeData
end
end ABG
