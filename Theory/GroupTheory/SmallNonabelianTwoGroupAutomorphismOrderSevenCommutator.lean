module

public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.CentralQuotientBinaryForm

/-!
# Commutator-form reductions for order-seven automorphisms of small two-groups

A characteristic order-two subgroup containing the derived group supplies a
nonzero invariant alternating form on the elementary quotient. This is the
specialization of the general central-quotient scalar commutator construction.
The Frattini linear-action count leaves quotient orders eight and sixteen;
only the latter forces the Frattini subgroup to have order two. In that case,
Cauchy's theorem and faithfulness of odd Frattini actions give an actual
nonidentity order-seven isometry of the nonzero form. The rank-three branch
is deliberately retained as a separate obligation.

These are the form-extraction steps in Stellmacher's small-core automorphism
argument, printed p.42. No nondegeneracy or classification conclusion is assumed.
-/

open scoped commutatorElement IsMulCommutative

namespace SmallNonabelianTwoGroup

variable {Q : Type*} [Group Q]

private theorem fixes_characteristic_card_two
    (N : Subgroup Q) [N.Characteristic] (hcard : Nat.card N = 2)
    (aut : MulAut Q) (point : N) : aut point = point := by
  obtain ⟨nonidentity, hne, hunique⟩ := (Nat.card_eq_two_iff' (1 : N)).mp hcard
  let restricted := MulAut.characteristic N aut
  have hfix : restricted point = point := by
    by_cases hpoint : point = 1
    · simp [hpoint]
    · exact (hunique _ (by simpa using hpoint)).trans (hunique _ hpoint).symm
  exact congrArg Subtype.val hfix

public theorem exists_nonzero_invariant_quotient_form
    (N : Subgroup Q) [N.Characteristic] [IsElementaryAbelian 2 (Q ⧸ N)]
    (hderived : commutator Q ≤ N) (hnoncomm : ¬ IsMulCommutative Q)
    (hcard : Nat.card N = 2) :
    ∃ form : LinearMap.BilinForm (ZMod 2) (Additive (Q ⧸ N)),
      form ≠ 0 ∧ form.IsAlt ∧
      ∀ (aut : MulAut Q) (left right : Q ⧸ N),
        form (Additive.ofMul (Subgroup.quotientAut N aut left))
            (Additive.ofMul (Subgroup.quotientAut N aut right)) =
          form (Additive.ofMul left) (Additive.ofMul right) := by
  let : IsCyclic N := isCyclic_of_prime_card hcard
  let coordinates : N ≃* Multiplicative (ZMod 2) :=
    mulEquivOfCyclicCardEq (by simpa using hcard)
  have hexists : ∃ left right : Q, left * right ≠ right * left := by
    by_contra hnot
    push Not at hnot
    exact hnoncomm ⟨⟨hnot⟩⟩
  obtain ⟨left, right, hne⟩ := hexists
  have hcommNe : ⁅left, right⁆ ≠ 1 :=
    (commutatorElement_eq_one_iff_mul_comm).not.mpr hne
  let scalar : commutator Q →* Multiplicative (ZMod 2) :=
    coordinates.toMonoidHom.comp (Subgroup.inclusion hderived)
  have hscalarNe : scalar ⟨⁅left, right⁆, Subgroup.commutator_mem_commutator
      (Subgroup.mem_top left) (Subgroup.mem_top right)⟩ ≠ 1 := by
    intro heq
    apply hcommNe
    exact congrArg Subtype.val (coordinates.injective (heq.trans coordinates.map_one.symm))
  obtain ⟨form, hform, halt, hpreserve⟩ :=
    Subgroup.exists_nonzero_invariant_central_quotient_form N
      (Subgroup.central_of_normal_card_two N hcard) hderived scalar left right hscalarNe
  refine ⟨form, hform, halt, ?_⟩
  intro aut first second
  apply hpreserve aut ?_ first second
  intro point
  exact fixes_characteristic_card_two N hcard aut ⟨point, hderived point.property⟩

public theorem frattini_quotient_card_eight_or_sixteen_of_seven_dvd
    [Finite Q] (htwo : IsPGroup 2 Q) (hnoncomm : ¬ IsMulCommutative Q)
    (hbound : Nat.card Q ≤ 32)
    (actor : Subgroup (MulAut Q)) (hodd : Odd (Nat.card actor))
    (hseven : 7 ∣ Nat.card actor) :
    Nat.card (Q ⧸ frattini Q) = 8 ∨ Nat.card (Q ⧸ frattini Q) = 16 := by
  let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  obtain ⟨dimension, hdim, hdimension⟩ :=
    exists_frattini_quotient_dimension_le_four htwo hnoncomm hbound
  have hdiv := hseven.trans (Subgroup.card_dvd_of_injective
    ((Subgroup.quotientAut (frattini Q)).comp actor.subtype)
    (odd_frattini_action_injective htwo actor hodd))
  rw [card_mulAut_elementary_two_pow (Q ⧸ frattini Q) dimension hdimension] at hdiv
  have hcases : dimension = 3 ∨ dimension = 4 := by
    interval_cases dimension <;> norm_num [Fin.prod_univ_succ] at hdiv <;> omega
  rcases hcases with hthree | hfour
  · exact Or.inl (by simpa [hthree] using hdimension)
  · exact Or.inr (by simpa [hfour] using hdimension)

public theorem exists_nonzero_invariant_frattini_form_of_quotient_sixteen
    [Finite Q] [IsElementaryAbelian 2 (Q ⧸ frattini Q)]
    (htwo : IsPGroup 2 Q) (hnoncomm : ¬ IsMulCommutative Q)
    (hbound : Nat.card Q ≤ 32) (hquotient : Nat.card (Q ⧸ frattini Q) = 16) :
    ∃ form : LinearMap.BilinForm (ZMod 2) (Additive (Q ⧸ frattini Q)),
      form ≠ 0 ∧ form.IsAlt ∧
      ∀ (aut : MulAut Q) (left right : Q ⧸ frattini Q),
        form (Additive.ofMul (Subgroup.quotientAut (frattini Q) aut left))
            (Additive.ofMul (Subgroup.quotientAut (frattini Q) aut right)) =
          form (Additive.ofMul left) (Additive.ofMul right) := by
  let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  obtain ⟨_, hcard, _⟩ :=
    frattini_structure_of_quotient_sixteen htwo hnoncomm hbound hquotient
  exact exists_nonzero_invariant_quotient_form (frattini Q)
    (commutator_le_frattini_of_isPGroup (p := 2)) hnoncomm hcard


public theorem exists_nontrivial_seven_isometry_of_quotient_sixteen
    [Finite Q] [IsElementaryAbelian 2 (Q ⧸ frattini Q)]
    (htwo : IsPGroup 2 Q) (hnoncomm : ¬ IsMulCommutative Q)
    (hbound : Nat.card Q ≤ 32) (hquotient : Nat.card (Q ⧸ frattini Q) = 16)
    (actor : Subgroup (MulAut Q)) (hodd : Odd (Nat.card actor))
    (hseven : 7 ∣ Nat.card actor) :
    Module.finrank (ZMod 2) (Additive (Q ⧸ frattini Q)) ≤ 4 ∧
    ∃ (form : LinearMap.BilinForm (ZMod 2) (Additive (Q ⧸ frattini Q)))
      (aut : Additive (Q ⧸ frattini Q) ≃ₗ[ZMod 2] Additive (Q ⧸ frattini Q)),
      form ≠ 0 ∧ form.IsAlt ∧ aut ≠ 1 ∧ aut ^ 7 = 1 ∧
      ∀ left right, form (aut left) (aut right) = form left right := by
  have hsize := Module.natCard_eq_pow_finrank
    (K := ZMod 2) (V := Additive (Q ⧸ frattini Q))
  change Nat.card (Q ⧸ frattini Q) = _ at hsize
  have hpower : 2 ^ Module.finrank (ZMod 2) (Additive (Q ⧸ frattini Q)) = 2 ^ 4 := by
    simpa only [Nat.card_zmod, hquotient, show (2 : ℕ) ^ 4 = 16 by decide] using hsize.symm
  have hdim := Nat.pow_right_injective (by decide : 1 < 2) hpower
  obtain ⟨form, hform, halt, hpreserve⟩ :=
    exists_nonzero_invariant_frattini_form_of_quotient_sixteen htwo hnoncomm hbound hquotient
  let linearize : MulAut (Q ⧸ frattini Q) ≃*
      (Additive (Q ⧸ frattini Q) ≃ₗ[ZMod 2] Additive (Q ⧸ frattini Q)) :=
    { toFun := fun aut =>
        { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
      invFun := fun aut => MulEquiv.toAdditive.symm aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }
  let action := linearize.toMonoidHom.comp
    ((Subgroup.quotientAut (frattini Q)).comp actor.subtype)
  have hinjective : Function.Injective action :=
    linearize.injective.comp (odd_frattini_action_injective htwo actor hodd)
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨element, horder⟩ := exists_prime_orderOf_dvd_card' 7 hseven
  have hne : element ≠ 1 := by
    intro heq
    simp [heq] at horder
  have hpow : element ^ 7 = 1 := by
    simpa only [horder] using pow_orderOf_eq_one element
  refine ⟨by omega, form, action element, hform, halt, ?_, ?_, ?_⟩
  · intro heq
    exact hne (hinjective (heq.trans action.map_one.symm))
  · rw [← map_pow, hpow, map_one]
  · intro left right
    exact hpreserve (element : MulAut Q) left.toMul right.toMul

end SmallNonabelianTwoGroup
