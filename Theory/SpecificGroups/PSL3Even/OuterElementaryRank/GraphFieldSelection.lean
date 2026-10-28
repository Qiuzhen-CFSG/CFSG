module

public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.StandardBound
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.NormalForm

/-!
# Selecting graph-field actors in elementary outer planes

Every standard PSL₃ automorphism has a literal linear–field–graph normal form.
In the actual outer group, every diagonal element has cube one. Consequently
the projection modulo the relative diagonal subgroup is injective on any
elementary two-subgroup of the standard outer image.

If that elementary image has rank two, its image in the relative quotient
cannot lie in the union of the cyclic field image and the cyclic graph image:
a subgroup contained in the union of two subgroups lies in one of them.
Lift an element outside this union back to the given actor subgroup. Its
normal form must have a graph factor and a nonidentity coefficient action.
This argument requires neither a splitting nor a bound on the order of the
whole standard outer image.

The last theorem applies this selection to the literal `hselect` premise of
`rank_le_of_fixed_calculations`, through the existing standard-rank adapter.
The two fixed-group estimates remain with the source assembly owner.

Source: GLS3, Theorem 2.5.12(b–e,i) and §2.7,
`refs/KGroup/GLS3/chapter2.tex`; Aschbacher–Smith E.1.14(1), printed p.214.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.PSL3Even.OuterElementaryRank
open Matrix.PSL3.OuterSolvable
variable {F : Type*} [Field F]

private theorem diagonal_quotient_injective
    (Q : Subgroup (MulAut.Outer PSL(3,F))) [IsElementaryAbelian 2 Q]
    (hQ : Q ≤ standardOuter F) :
    Function.Injective ((QuotientGroup.mk'
      ((innerDiagonalOuter F).subgroupOf (standardOuter F))).comp
        (Subgroup.inclusion hQ)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  apply Subtype.ext
  have hxD' : Subgroup.inclusion hQ x ∈
      (innerDiagonalOuter F).subgroupOf (standardOuter F) :=
    (QuotientGroup.eq_one_iff (Subgroup.inclusion hQ x)).mp hx
  have hxD : (x : MulAut.Outer PSL(3,F)) ∈ innerDiagonalOuter F := hxD'
  obtain ⟨g, hg⟩ := hxD
  have hx3 : (x : MulAut.Outer PSL(3,F)) ^ 3 = 1 := by
    rw [← hg]
    change (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (linearConj F g) ^ 3 = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      (Matrix.PSL3.OddInvolutionFixed.linearConj_cube_inner g)
  have hx2 : (x : MulAut.Outer PSL(3,F)) ^ 2 = 1 :=
    congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 Q) x)
  change (x : MulAut.Outer PSL(3,F)) = 1
  simpa only [pow_succ, hx2, one_mul] using hx3

private def linearStandard (g : GL (Fin 3) F) : standard F :=
  ⟨linearConj F g, linearConj_mem_standard F g⟩

private theorem quotient_linearStandard (g : GL (Fin 3) F) :
    standardQuotientMap F (linearStandard g) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨g, rfl⟩

private theorem quotient_factorization (a : standard F) :
    ∃ (g : GL (Fin 3) F) (σ : F ≃+* F),
      ((a : MulAut PSL(3,F)) = linearConj F g * fieldAction F σ ∧
        standardQuotientMap F a = fieldStandardQuotient F σ) ∨
      ((a : MulAut PSL(3,F)) = linearConj F g * fieldAction F σ * graph F ∧
        standardQuotientMap F a = fieldStandardQuotient F σ * graphStandardQuotient F) := by
  obtain ⟨g, σ, ha | ha⟩ := Matrix.PSL3.CartanActions.NormalizerForm.standard_factorization F
    (fun σ g => field_linearConj σ g) (fun g => graph_linearConj_exists g)
    (fun σ => field_commute_graph σ) a a.property
  · refine ⟨g, σ, Or.inl ⟨ha, ?_⟩⟩
    have h : a = linearStandard g * fieldActionStandard F σ := Subtype.ext ha
    rw [h, map_mul, quotient_linearStandard, one_mul]
    rfl
  · refine ⟨g, σ, Or.inr ⟨ha, ?_⟩⟩
    have h : a = linearStandard g * fieldActionStandard F σ * graphStandard F :=
      Subtype.ext ha
    rw [h, map_mul, map_mul, quotient_linearStandard, one_mul]
    rfl

variable [Finite F]

/-- A rank-two elementary outer image contains an actual graph-field actor.
The conclusion uses the literal GL₃ conjugation, coefficient action and inverse
transpose. This holds over every finite field, hence in particular over 2ᶠ. -/
theorem exists_graphField_of_outer_rank_two
    (E : Subgroup (MulAut PSL(3,F))) (hE : IsElementaryAbelian 2 E)
    (hES : E ≤ standard F)
    (hr : primeRank 2 (E.map (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)))) = 2) :
    ∃ a ∈ E, IsGraphField a := by
  classical
  let := hE
  let Q := E.map (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)))
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.map _
  have hQ : Q ≤ standardOuter F := Subgroup.map_mono hES
  let π := (QuotientGroup.mk'
    ((innerDiagonalOuter F).subgroupOf (standardOuter F))).comp
      (Subgroup.inclusion hQ)
  have hi : Function.Injective π := diagonal_quotient_injective Q hQ
  have hnoncyclic : ¬ IsCyclic π.range := by
    intro hc
    let := hc
    let : IsCyclic Q := isCyclic_of_injective π.rangeRestrict
      (fun x y h => hi (congrArg Subtype.val h))
    have hr1 := (Classical.choice (inferInstance : Nonempty (Sylow 2 Q))).primeRank_le_one_of_isCyclic
      inferInstance
    change primeRank 2 Q = 2 at hr
    omega
  let C := (fieldStandardQuotient F).range
  let D := Subgroup.zpowers (graphStandardQuotient F)
  let : IsCyclic C := fieldStandardQuotient_isCyclic F
  have houtside : ¬ (π.range : Set (StandardOuterQuotient F)) ⊆ (C : Set _) ∪ (D : Set _) := by
    intro h
    rcases SubgroupClass.subset_union.mp h with h | h
    · exact hnoncyclic (Subgroup.isCyclic_of_le h)
    · exact hnoncyclic (Subgroup.isCyclic_of_le h)
  obtain ⟨y, hy, hnot⟩ := Set.not_subset.mp houtside
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨a, ha, hax⟩ := x.property
  have hπ : π x = standardQuotientMap F ⟨a, hES ha⟩ := by
    apply congrArg (QuotientGroup.mk' ((innerDiagonalOuter F).subgroupOf (standardOuter F)))
    exact Subtype.ext hax.symm
  obtain ⟨g, σ, ⟨haform, hquot⟩ | ⟨haform, hquot⟩⟩ :=
    quotient_factorization (⟨a, hES ha⟩ : standard F)
  · exact (hnot (Or.inl ⟨σ, (hπ.trans hquot).symm⟩)).elim
  · refine ⟨a, ha, g, σ, ?_, haform⟩
    intro hσ
    apply hnot
    right
    rw [hπ, hquot, hσ, map_one, one_mul]
    exact Subgroup.mem_zpowers _

/-- Discharge the graph-field selection premise in the sharp-rank reduction.
The standard outer-image bound is already proved; only the two literal
fixed-subgroup rank estimates remain for the source assembly owner. -/
theorem rank_le_of_fixed_bounds {f : ℕ} (hf : 0 < f)
    (hF : Nat.card F = 2 ^ f)
    (hfixed : ∀ a : MulAut PSL(3,F), a ∈ standard F → a ^ 2 = 1 →
      a ∉ MulAut.innerSubgroup PSL(3,F) → primeRank 2 a.fixedSubgroup ≤ f)
    (hmixedFixed : ∀ a : MulAut PSL(3,F), IsGraphField a → a ^ 2 = 1 →
      primeRank 2 a.fixedSubgroup ≤ f - 1)
    (E : Subgroup (MulAut PSL(3,F))) (hE : IsElementaryAbelian 2 E)
    (hEO : ¬ E ≤ MulAut.innerSubgroup PSL(3,F)) : Group.rank E ≤ f + 1 :=
  rank_le_of_fixed_and_selection hf hF hfixed hmixedFixed
    exists_graphField_of_outer_rank_two E hE hEO

end Matrix.PSL3Even.OuterElementaryRank
