module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.ClassConstruction.FixedPoints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.ClassConstruction.OddWitnesses
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.ClassConstruction.FreeClasses.AlternatingSix

/-!
# The three normalizer classes without nonidentity fixed vectors

A cyclic two-group acting on the sixteen-element E has a second fixed
point besides the identity. The actual A₆ quotient preserves the order of
an element without nonidentity fixed vectors, so the A₆ power alternatives
leave only orders three and five. The existing order-three fusion result
handles order three; the two internal A₆ classes of order five lift through
the actual quotient to classes represented by μ and μ².

The final theorem supplies exactly the `hfreeClasses` argument of
`nonempty_normalizerClassData_of_class_branches`: injectivity of the three
literal marked classes and coverage of every element in this branch. The
order-three and order-five witnesses remain arbitrary subject to the
three stated premises; no further class-coverage hypothesis is used.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 3 and 5–6, especially printed pp.9–11.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
include L
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Fourth-power-one elements have a nonidentity fixed vector on E. -/
public theorem normalizer_hasFixedVector_of_fourth_power_eq_one (x : normalizer (CaseII.E D k : Set G)) (hx : x ^ 4 = 1) :
    normalizerHasFixedVector D k x := by
  let a := normalizerConjugation D k x
  have ha : a ^ 4 = 1 := by
    dsimp [a]
    rw [← map_pow, hx, map_one]
  have hP : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card_dvd_pow (n := 2) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one ha)
  obtain ⟨v, hv, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := CaseII.E D k) (by rw [L.E_card]; decide)
    (a := (1 : CaseII.E D k)) (by intro g; exact map_one g.val)
  exact ⟨v, Ne.symm hne, hv ⟨a, mem_zpowers a⟩⟩


/-- Only orders three and five occur without nonidentity fixed vectors. -/
public theorem normalizer_noFixedVector_order_three_or_five
    (x : normalizer (CaseII.E D k : Set G))
    (hx : ¬ normalizerHasFixedVector D k x) : orderOf x = 3 ∨ orderOf x = 5 := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := L.normalizer_E
  let q := normalizerQuotient D k K hK eK
  have ho : orderOf x = orderOf (q x) :=
    normalizer_order_eq_quotient_of_noFixedVector D k K hK eK x hx
  have hn : orderOf x ≠ 1 := by
    intro h1
    apply hx
    apply normalizer_hasFixedVector_of_fourth_power_eq_one D k L
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [h1]
    exact one_dvd _
  rcases FreeClassA6.fourth_or_cube_or_fifth_eq_one (q x) with h4 | h3 | h5
  · exact (hx (normalizer_hasFixedVector_of_fourth_power_eq_one D k L x
      (orderOf_dvd_iff_pow_eq_one.mp (ho ▸ orderOf_dvd_of_pow_eq_one h4)))).elim
  · exact Or.inl (((Nat.dvd_prime (by decide : Nat.Prime 3)).mp
      (ho ▸ orderOf_dvd_of_pow_eq_one h3)).resolve_left hn)
  · exact Or.inr (((Nat.dvd_prime (by decide : Nat.Prime 5)).mp
      (ho ▸ orderOf_dvd_of_pow_eq_one h5)).resolve_left hn)

/-- The exact fixed-point-free branch of the twelve-class construction. -/
public theorem normalizer_free_classes
    (c₁ μ : normalizer (CaseII.E D k : Set G))
    (hc₁ : orderOf c₁ = 3) (hc₁free : ¬ normalizerHasFixedVector D k c₁)
    (hμ : orderOf μ = 5) :
    Function.Injective (fun i : Fin 3 =>
      ConjClasses.mk (normalizerFreeRepresentative D k c₁ μ i)) ∧
      ∀ x : normalizer (CaseII.E D k : Set G),
        ¬ normalizerHasFixedVector D k x →
        ∃ i : Fin 3, IsConj x (normalizerFreeRepresentative D k c₁ μ i) := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := L.normalizer_E
  let q := normalizerQuotient D k K hK eK
  have hμfree := normalizer_five_has_noFixedVector D k L μ hμ
  have hμq : orderOf (q μ) = 5 :=
    (normalizer_order_eq_quotient_of_noFixedVector D k K hK eK μ hμfree).symm.trans hμ
  have hμ2 : orderOf (μ ^ 2) = 5 := by
    rw [orderOf_pow' _ (by decide), hμ]
    decide
  have hsep : ¬ IsConj μ (μ ^ 2) := by
    intro h
    apply FreeClassA6.five_not_isConj_square (q μ) hμq
    simpa only [map_pow] using q.map_isConj h
  constructor
  · intro i j hij
    have hc := ConjClasses.mk_eq_mk_iff_isConj.mp hij
    have ho : orderOf (normalizerFreeRepresentative D k c₁ μ i) =
        orderOf (normalizerFreeRepresentative D k c₁ μ j) := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hc
      rw [← hg]
      exact ((MulAut.conj g).orderOf_eq _).symm
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals try
      norm_num [normalizerFreeRepresentative, hc₁, hμ, hμ2] at ho
    · exact (hsep hc).elim
    · exact (hsep hc.symm).elim
  · intro x hx
    rcases normalizer_noFixedVector_order_three_or_five D k L x hx with hx3 | hx5
    · exact ⟨0, normalizer_fixedPointFree_three_conjugate D k L c₁ hc₁ hc₁free x hx3 hx⟩
    · have hxq : orderOf (q x) = 5 :=
        (normalizer_order_eq_quotient_of_noFixedVector D k K hK eK x hx).symm.trans hx5
      rcases FreeClassA6.five_isConj_or_square (q x) (q μ) hxq hμq with h | h
      · exact ⟨1, (normalizer_isConj_iff_quotient_of_noFixedVector D k K hK eK x μ hx).mpr h⟩
      · refine ⟨2, (normalizer_isConj_iff_quotient_of_noFixedVector D k K hK eK x (μ ^ 2) hx).mpr ?_⟩
        simpa only [map_pow] using h

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
