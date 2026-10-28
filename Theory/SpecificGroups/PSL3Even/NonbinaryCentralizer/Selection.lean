module
public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.Models
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.GraphConjugacy
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.FieldDescent.Conjugacy

public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.StandardRank

/-!
# Selecting graph or field involutions at exact elementary rank

Let E be an elementary abelian two-subgroup of the standard automorphisms of
PSL₃(2ᶠ), with f > 1, containing outer actors and having rank f + 1. Assuming
the sharp mixed graph-field fixed-rank estimate, E contains an outer actor
actually conjugate to the graph action or a nontrivial involutory field action.

The actual outer image has rank at most two. At outer rank at most one, a
mixed actor would bound E by (f - 1) + 1, contradicting the exact rank. At
outer rank two, lift two distinct nonidentity outer images into E. If both
lifts have a graph factor, their quotient cancels that factor and remains
outer. This selects a field expression in the original E, without choosing a
complement to the inner kernel. The checked graph Gram factorization and
quadratic matrix descent then give actual conjugacy, not merely type labels.

The exported selection has precisely the `hselect` type consumed by
`CentralizerLocals.NonbinaryGeometry.simpleCentralizerGeometry_of_model_calculations`.
The independent mixed fixed-rank estimate remains explicit for that assembly.
No residual is substituted for the whole fixed group, including over GF(4).

Source: GLS3, Theorem 2.5.12 and §2.7, `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher–Smith E.1.1–6 and E.1.14(1), printed pp.209–214.
-/

public section

open scoped MatrixGroups
open Subgroup Theory.GroupTheory Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3Even.NonbinaryCentralizer.Selection
variable {F : Type*} [Field F] [Finite F]

private theorem two_outer_lifts
    (E : Subgroup (MulAut PSL(3,F)))
    (hr : 1 < primeRank 2 (E.map (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))))) :
    ∃ a ∈ E, ∃ b ∈ E,
      a ∉ MulAut.innerSubgroup PSL(3,F) ∧ b ∉ MulAut.innerSubgroup PSL(3,F) ∧
      QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)) a ≠
        QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)) b := by
  classical
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
  let Q := E.map q
  have hnc : ¬ IsCyclic Q := by
    intro hc
    let := hc
    have h := (Classical.choice (inferInstance : Nonempty (Sylow 2 Q))).primeRank_le_one_of_isCyclic
      inferInstance
    exact (not_le_of_gt hr) h
  let := Nontrivial.of_not_isCyclic hnc
  obtain ⟨x, hx⟩ := exists_ne (1 : Q)
  have hex : ∃ y : Q, y ∉ Subgroup.zpowers x := by
    by_contra! h
    apply hnc
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, top_unique (fun y _ => h y)⟩
  obtain ⟨y, hy⟩ := hex
  obtain ⟨a, ha, hax⟩ := x.property
  obtain ⟨b, hb, hby⟩ := y.property
  refine ⟨a, ha, b, hb, ?_, ?_, ?_⟩
  · intro hi
    apply hx
    apply Subtype.ext
    exact hax.symm.trans ((QuotientGroup.eq_one_iff a).mpr hi)
  · intro hi
    apply hy
    have he : y = 1 := Subtype.ext (hby.symm.trans ((QuotientGroup.eq_one_iff b).mpr hi))
    rw [he]
    exact Subgroup.one_mem _
  · intro he
    apply hy
    have he' : y = x := Subtype.ext (hby.symm.trans (he.symm.trans hax))
    rw [he']
    exact Subgroup.mem_zpowers _

omit [Finite F] in
private theorem linearField_factorization (a : MulAut PSL(3,F))
    (ha : a ∈ innerDiagonal F ⊔ (fieldAction F).range) :
    ∃ (g : GL (Fin 3) F) (σ : F ≃+* F), a = linearConj F g * fieldAction F σ := by
  have hn : (fieldAction F).range ≤ normalizer (innerDiagonal F) := by
    rintro _ ⟨σ, rfl⟩
    exact fieldAction_mem_normalizer_innerDiagonal σ
  change a ∈ (↑(innerDiagonal F ⊔ (fieldAction F).range) : Set _) at ha
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at ha
  obtain ⟨_, ⟨g, rfl⟩, _, ⟨σ, rfl⟩, rfl⟩ := ha
  exact ⟨g, σ, rfl⟩

omit [Finite F] in
private theorem standard_two_cosets (a : MulAut PSL(3,F)) (ha : a ∈ standard F) :
    a ∈ innerDiagonal F ⊔ (fieldAction F).range ∨
      ∃ b ∈ innerDiagonal F ⊔ (fieldAction F).range, a = b * graph F := by
  obtain ⟨g, σ, h | h⟩ := Matrix.PSL3.CartanActions.NormalizerForm.standard_factorization F
    field_linearConj graph_linearConj_exists field_commute_graph a ha
  all_goals
    have hm : linearConj F g * fieldAction F σ ∈ innerDiagonal F ⊔ (fieldAction F).range :=
      Subgroup.mul_mem _
        ((le_sup_left : innerDiagonal F ≤ innerDiagonal F ⊔ (fieldAction F).range) ⟨g, rfl⟩)
        ((le_sup_right : (fieldAction F).range ≤ innerDiagonal F ⊔ (fieldAction F).range) ⟨σ, rfl⟩)
  · exact Or.inl (h ▸ hm)
  · exact Or.inr ⟨_, hm, h⟩

/-- A rank-two elementary outer image has a genuinely nontrivial field expression
inside the original actor group. No complement to its inner kernel is chosen. -/
theorem exists_field_expression_of_outer_rank_two
    (E : Subgroup (MulAut PSL(3,F))) (hE : IsElementaryAbelian 2 E)
    (hES : E ≤ standard F)
    (hr : primeRank 2 (E.map (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)))) = 2) :
    ∃ a ∈ E, a ∉ MulAut.innerSubgroup PSL(3,F) ∧
      ∃ (g : GL (Fin 3) F) (σ : F ≃+* F), σ ≠ 1 ∧
        a = linearConj F g * fieldAction F σ := by
  have finish (a : MulAut PSL(3,F)) (ha : a ∈ E)
      (ho : a ∉ MulAut.innerSubgroup PSL(3,F))
      (hK : a ∈ innerDiagonal F ⊔ (fieldAction F).range) :
      ∃ a ∈ E, a ∉ MulAut.innerSubgroup PSL(3,F) ∧
        ∃ (g : GL (Fin 3) F) (σ : F ≃+* F), σ ≠ 1 ∧
          a = linearConj F g * fieldAction F σ := by
    obtain ⟨g, σ, he⟩ := linearField_factorization a hK
    refine ⟨a, ha, ho, g, σ, ?_, he⟩
    intro hσ
    have he' : a = linearConj F g := by simpa [hσ] using he
    have hs : a ^ 2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p (⟨a, ha⟩ : E))
    exact ho (he' ▸ Matrix.PSL3.OddInvolutionFixed.linearConj_involution_inner g (he' ▸ hs))
  obtain ⟨a, ha, b, hb, hao, hbo, hab⟩ := two_outer_lifts E (by omega)
  rcases standard_two_cosets a (hES ha) with hK | ⟨x, hx, hax⟩
  · exact finish a ha hao hK
  rcases standard_two_cosets b (hES hb) with hK | ⟨y, hy, hby⟩
  · exact finish b hb hbo hK
  apply finish (a * b⁻¹) (E.mul_mem ha (E.inv_mem hb))
  · intro hi
    apply hab
    apply mul_inv_eq_one.mp
    rw [← map_inv, ← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hi
  · have he : a * b⁻¹ = x * y⁻¹ := by rw [hax, hby]; group
    rw [he]
    exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hy)

open Matrix.PSL3Even.OuterElementaryRank

private theorem field_expression_isGraphOrField
    (g : GL (Fin 3) F) (σ : F ≃+* F) (hne : σ ≠ 1)
    (hs : (linearConj F g * fieldAction F σ) ^ 2 = 1) :
    IsGraphOrField (linearConj F g * fieldAction F σ) := by
  have hσ := FixedRanks.field_part_sq g σ hs
  obtain ⟨P, hP⟩ := FixedRanks.FieldDescent.exists_linear_conjugate_field
    g σ (orderOf_eq_prime hσ hne) hs
  exact Or.inr ⟨σ, hne, hσ, isConj_iff.mpr ⟨linearConj F P, hP⟩⟩

/-- At rank f+1, a noninner elementary actor contains a graph or field involution,
with actual conjugacy on the same projective group. Only the mixed fixed-rank
estimate remains an explicit model input. -/
theorem exists_graph_or_field_of_exact_rank {f : ℕ} (hf : 1 < f)
    (hF : Nat.card F = 2 ^ f)
    (hGF : ∀ a : MulAut PSL(3,F), IsGraphField a → a ^ 2 = 1 →
      primeRank 2 a.fixedSubgroup ≤ f - 1)
    (E : Subgroup (MulAut PSL(3,F))) (hE : IsElementaryAbelian 2 E)
    (hES : E ≤ standard F) (hEO : ¬ E ≤ MulAut.innerSubgroup PSL(3,F))
    (hr : Group.rank E = f + 1) :
    ∃ a ∈ E, a ∉ MulAut.innerSubgroup PSL(3,F) ∧ IsGraphOrField a := by
  let := hE
  have hsquare (a : MulAut PSL(3,F)) (ha : a ∈ E) : a ^ 2 = 1 :=
    congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p (⟨a, ha⟩ : E))
  let Q := E.map (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)))
  have hQle : Q ≤ standardOuter F := Subgroup.map_mono hES
  have hQ : primeRank 2 Q ≤ 2 :=
    (primeRank_le_of_injective 2 (Subgroup.inclusion hQle)
      (Subgroup.inclusion_injective hQle)).trans
        (standardOuter_two_rank_le_of_two_power_card F (by omega) hF)
  by_cases hQ1 : primeRank 2 Q ≤ 1
  · have hex : ∃ a ∈ E, a ∉ MulAut.innerSubgroup PSL(3,F) := by
      by_contra! h
      exact hEO h
    obtain ⟨a, ha, hao⟩ := hex
    rcases FixedRanks.outer_involution_cases a (hES ha) (hsquare a ha) hao with
      ⟨g, σ, hne, he⟩ | ⟨g, he⟩ | hmixed
    · refine ⟨a, ha, hao, ?_⟩
      rw [he]
      exact field_expression_isGraphOrField g σ hne (he ▸ hsquare a ha)
    · refine ⟨a, ha, hao, Or.inl ?_⟩
      obtain ⟨c, hc⟩ := FixedRanks.graph_involution_conjugate (by omega : 0 < f) hF g
        (he ▸ hsquare a ha)
      rw [he]
      exact isConj_iff.mpr ⟨c, hc⟩
    · have hbound := rank_le_fixed_add_outer E a ha
      have hfix := hGF a hmixed (hsquare a ha)
      change Group.rank E ≤ primeRank 2 a.fixedSubgroup + primeRank 2 Q at hbound
      omega
  · have hQ2 : primeRank 2 Q = 2 := by omega
    obtain ⟨a, ha, hao, g, σ, hne, he⟩ :=
      exists_field_expression_of_outer_rank_two E hE hES hQ2
    refine ⟨a, ha, hao, ?_⟩
    rw [he]
    exact field_expression_isGraphOrField g σ hne (he ▸ hsquare a ha)

end Matrix.PSL3Even.NonbinaryCentralizer.Selection
