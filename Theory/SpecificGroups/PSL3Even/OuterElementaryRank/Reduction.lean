module
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage

/-!
# Sharp elementary-actor rank from literal fixed subgroups

For an elementary two-subgroup of Aut(PSL₃(2ᶠ)), its inner kernel embeds in
any actor's fixed subgroup. If its outer image has rank at most one, a fixed
rank bound f gives the desired f+1. If that image has rank two, selecting an
actor with nontrivial field and graph parts permits the stronger fixed rank
bound f-1. This avoids losing one rank by using only the uniform fixed bound.
The binary field is discharged by the genuine Aut(PSL₃(2)) calculation.

The fixed-group estimates and rank-two actor selection remain explicit in
this reduction. They are statements about the actual matrix automorphisms
and Aut/Inn map, not about residuals or E-generation.

Source: GLS3, Theorem 2.5.12 and §2.7, `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher–Smith E.1.14(1), printed p.214, and G.9, printed p.356.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3Even.OuterElementaryRank
open Matrix.PSL3.OuterSolvable
variable {F : Type*} [Field F] [Finite F]

/-- An actual linear-field-graph expression with nonidentity coefficient action.
The involution condition is imposed separately when this predicate is used. -/
@[expose] def IsGraphField (a : MulAut PSL(3,F)) : Prop :=
  ∃ g : GL (Fin 3) F, ∃ σ : F ≃+* F,
    σ ≠ 1 ∧ a = linearConj F g * fieldAction F σ * graph F

omit [Finite F] in
private theorem center_eq_bot : center PSL(3,F) = ⊥ := by
  let := Atlas.sl_perfect (F := F) 3 (by decide)
  exact Group.IsPerfect.center_quotient_center_eq_bot (SpecialLinearGroup (Fin 3) F)

private theorem elementary_rank_le_primeRank (E : Subgroup (MulAut PSL(3,F)))
    [IsElementaryAbelian 2 E] : Group.rank E ≤ primeRank 2 E := by
  have h := (⊤ : Subgroup E).rank_le_primeRank 2
    ((IsElementaryAbelian.isPGroup 2 E).to_subgroup ⊤)
  rwa [Group.rank_congr Subgroup.topEquiv] at h

/-- Faithful inner-kernel control in the exact generator-rank convention
used by the E-generation consumer. -/
theorem rank_le_fixed_add_outer (E : Subgroup (MulAut PSL(3,F)))
    [IsElementaryAbelian 2 E] (a : MulAut PSL(3,F)) (ha : a ∈ E) :
    Group.rank E ≤ primeRank 2 a.fixedSubgroup +
      primeRank 2 (E.map (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)))) :=
  (elementary_rank_le_primeRank E).trans
    (elementary_automorphism_two_rank_le center_eq_bot E a ha)

/-- The smallest field allows elementary rank two, including outer actors. -/
theorem rank_le_of_card_two (hF : Nat.card F = 2)
    (E : Subgroup (MulAut PSL(3,F))) [IsElementaryAbelian 2 E] :
    Group.rank E ≤ 2 := by
  have h := E.rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 E)
  rwa [Matrix.PSL3Even.automorphism_two_rank_eq_of_card_two F hF] at h

/-- The sharp bound follows from the outer-image calculation, the two
literal fixed-group bounds, and graph-field selection in a rank-two image.
These model inputs remain explicit; this is not yet the unconditional bound. -/
theorem rank_le_of_fixed_calculations {f : ℕ} (hf : 0 < f)
    (hF : Nat.card F = 2 ^ f)
    (houterRank : primeRank 2 (standardOuter F) ≤ 2)
    (hfixed : ∀ a : MulAut PSL(3,F), a ∈ standard F → a ^ 2 = 1 →
      a ∉ MulAut.innerSubgroup PSL(3,F) → primeRank 2 a.fixedSubgroup ≤ f)
    (hmixedFixed : ∀ a : MulAut PSL(3,F), IsGraphField a → a ^ 2 = 1 →
      primeRank 2 a.fixedSubgroup ≤ f - 1)
    (hselect : ∀ E : Subgroup (MulAut PSL(3,F)), IsElementaryAbelian 2 E →
      E ≤ standard F →
      primeRank 2 (E.map (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)))) = 2 →
      ∃ a ∈ E, IsGraphField a)
    (E : Subgroup (MulAut PSL(3,F))) (hE : IsElementaryAbelian 2 E)
    (hEO : ¬ E ≤ MulAut.innerSubgroup PSL(3,F)) : Group.rank E ≤ f + 1 := by
  let := hE
  by_cases hf1 : f = 1
  · subst f
    exact rank_le_of_card_two (by simpa using hF) E
  have hES : E ≤ standard F := by
    rw [standard_eq_top_of_two_power_card F hf hF]
    exact le_top
  let Q := E.map (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)))
  have hQle : Q ≤ standardOuter F := Subgroup.map_mono hES
  have hQ : primeRank 2 Q ≤ 2 :=
    (primeRank_le_of_injective 2 (Subgroup.inclusion hQle)
      (Subgroup.inclusion_injective hQle)).trans houterRank
  have hsquare (a : MulAut PSL(3,F)) (ha : a ∈ E) : a ^ 2 = 1 :=
    congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p (⟨a, ha⟩ : E))
  by_cases hQ1 : primeRank 2 Q ≤ 1
  · have hex : ∃ a ∈ E, a ∉ MulAut.innerSubgroup PSL(3,F) := by
      by_contra hn
      apply hEO
      intro a ha
      by_contra hn'
      exact hn ⟨a, ha, hn'⟩
    obtain ⟨a, ha, hna⟩ := hex
    exact (rank_le_fixed_add_outer E a ha).trans
      (Nat.add_le_add (hfixed a (hES ha) (hsquare a ha) hna) hQ1)
  · have hQ2 : primeRank 2 Q = 2 := by omega
    obtain ⟨a, ha, hm⟩ := hselect E hE hES hQ2
    have h := rank_le_fixed_add_outer E a ha
    have hfix := hmixedFixed a hm (hsquare a ha)
    change Group.rank E ≤ primeRank 2 a.fixedSubgroup + primeRank 2 Q at h
    omega
end Matrix.PSL3Even.OuterElementaryRank
