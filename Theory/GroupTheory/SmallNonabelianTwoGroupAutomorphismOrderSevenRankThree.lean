module
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderSevenCommutator
public import Theory.LinearAlgebra.BinaryAlternatingSevenLinear
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Excluding order seven on the rank-three Frattini quotient

For a nonabelian two-group of order at most 32 whose Frattini quotient has
order eight, no odd automorphism subgroup has order divisible by seven.
This is the missing rank-three branch of the small-core automorphism bound
used in Stellmacher, printed p.42. The Frattini subgroup is not assumed to
have order two or to be central.

Choose an actual order-seven actor. Orbit counting makes it fix the
Frattini subgroup, whose order is at most four, while odd Frattini
faithfulness makes its quotient action nontrivial and hence fixed-point-free.
The quotient displacement map is surjective. The Frattini subgroup is abelian
by its order, so its conjugation action factors through the quotient; fixed
pointwise action and displacement surjectivity then make it central.

Centrality makes each generating commutator have square one, because every
square lies in the Frattini subgroup. Thus the derived group is elementary.
A dual functional detecting an actual nontrivial commutator supplies a
nonzero invariant alternating form on the quotient through the shared scalar
commutator construction. The dimension-at-most-four linear obstruction forces
the quotient actor to be trivial, contradicting odd Frattini faithfulness.
-/

namespace SmallNonabelianTwoGroup

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
open MonoidHom
open scoped IsMulCommutative commutatorElement

private theorem order_seven_fixes_card_lt_seven
    {F : Type*} [Group F] [Finite F] (hcard : Nat.card F < 7)
    (aut : MulAut F) (hpow : aut ^ 7 = 1) : aut = 1 := by
  let line := Subgroup.zpowers aut
  have hp : IsPGroup 7 line := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [line, Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hpow)
  let fixed := FixedPoints.subgroup line F
  have hmod := hp.card_modEq_card_fixedPoints F
  change Nat.card F % 7 = Nat.card fixed % 7 at hmod
  have hle : Nat.card fixed ≤ Nat.card F := Nat.card_le_card_of_injective (Subtype.val : fixed → F) Subtype.val_injective
  have hfixedCard : Nat.card fixed = Nat.card F := by
    rw [Nat.mod_eq_of_lt hcard, Nat.mod_eq_of_lt (by omega : Nat.card fixed < 7)] at hmod
    exact hmod.symm
  have htop : fixed = ⊤ := fixed.eq_top_of_card_eq hfixedCard
  apply MulEquiv.ext
  intro point
  have hmem : point ∈ fixed := htop ▸ Subgroup.mem_top point
  exact ((FixedPoints.mem_subgroup (M := line) (a := point)).mp hmem) ⟨aut, Subgroup.mem_zpowers aut⟩

private theorem nontrivial_order_seven_fixedPointFree_card_eight
    {F : Type*} [Group F] [Finite F] (hcard : Nat.card F = 8)
    (aut : MulAut F) (hpow : aut ^ 7 = 1) (hne : aut ≠ 1) : FixedPointFree aut := by
  let line := Subgroup.zpowers aut
  have hp : IsPGroup 7 line := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [line, Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hpow)
  let fixed := FixedPoints.subgroup line F
  have hmod := hp.card_modEq_card_fixedPoints F
  change Nat.card F % 7 = Nat.card fixed % 7 at hmod
  have hle : Nat.card fixed ≤ 8 := (Nat.card_le_card_of_injective (Subtype.val : fixed → F) Subtype.val_injective).trans_eq hcard
  have hlt : Nat.card fixed < 8 := by
    by_contra hnot
    have htop : fixed = ⊤ := fixed.eq_top_of_card_eq (by omega)
    apply hne
    apply MulEquiv.ext
    intro point
    have hmem : point ∈ fixed := htop ▸ Subgroup.mem_top point
    exact ((FixedPoints.mem_subgroup (M := line) (a := point)).mp hmem) ⟨aut, Subgroup.mem_zpowers aut⟩
  have hbot : fixed = ⊥ := Subgroup.card_eq_one.mp (by rw [hcard] at hmod; omega)
  intro point hpoint
  have hmem : point ∈ fixed := by
    rw [FixedPoints.mem_subgroup]
    intro actor
    exact smul_eq_self_of_mem_zpowers actor.property hpoint
  simpa [hbot] using hmem


private theorem central_of_fixed_automorphism_and_fixedPointFree_quotient
    {Q : Type*} [Group Q] [Finite Q]
    (N : Subgroup Q) [N.Characteristic] [IsMulCommutative N]
    (aut : MulAut Q) (hfix : ∀ point : N, aut point = point)
    (hfree : FixedPointFree (Subgroup.quotientAut N aut)) : N ≤ Subgroup.center Q := by
  let conj : Q →* MulAut N := MulAut.conjNormal
  have hconj (point : Q) : conj (aut point) = conj point := by
    apply MulEquiv.ext
    intro member
    apply Subtype.ext
    change aut point * member * (aut point)⁻¹ = point * member * point⁻¹
    have heq := hfix ⟨point * member * point⁻¹,
      (inferInstance : N.Normal).conj_mem member member.property point⟩
    simpa only [map_mul, map_inv, hfix member] using heq
  have hker : N ≤ conj.ker := by
    intro point hpoint
    apply MulEquiv.ext
    intro member
    apply Subtype.ext
    change point * member * point⁻¹ = member
    have hcomm := congrArg Subtype.val (mul_comm (⟨point, hpoint⟩ : N) member)
    change point * (member : Q) = (member : Q) * point at hcomm
    rw [hcomm]
    simp [mul_assoc]
  let quotientConj := QuotientGroup.lift N conj hker
  have hinvariant (point : Q ⧸ N) :
      quotientConj (Subgroup.quotientAut N aut point) = quotientConj point := by
    refine QuotientGroup.induction_on point ?_
    intro representative
    change quotientConj (Subgroup.quotientAut N aut (QuotientGroup.mk' N representative)) =
      quotientConj (QuotientGroup.mk' N representative)
    rw [Subgroup.quotientAut_apply_mk]
    exact hconj representative
  have htrivial (point : Q ⧸ N) : quotientConj point = 1 := by
    obtain ⟨representative, rfl⟩ := hfree.commutatorMap_surjective point
    change quotientConj (representative / Subgroup.quotientAut N aut representative) = 1
    rw [map_div, hinvariant, div_self']
  intro member hmember
  rw [Subgroup.mem_center_iff]
  intro point
  have heq := congrArg (fun a : MulAut N => (a ⟨member, hmember⟩ : Q))
    (htrivial (QuotientGroup.mk' N point))
  change point * member * point⁻¹ = member at heq
  calc
    point * member = (point * member * point⁻¹) * point := by simp [mul_assoc]
    _ = member * point := by rw [heq]


private theorem frattini_central_of_order_seven_and_quotient_eight
    {Q : Type*} [Group Q] [Finite Q]
    (htwo : IsPGroup 2 Q) (hbound : Nat.card Q ≤ 32)
    (hquotient : Nat.card (Q ⧸ frattini Q) = 8)
    (aut : MulAut Q) (horder : orderOf aut = 7) : frattini Q ≤ Subgroup.center Q := by
  have hcount := (frattini Q).index_mul_card
  change Nat.card (Q ⧸ frattini Q) * Nat.card (frattini Q) = Nat.card Q at hcount
  rw [hquotient] at hcount
  have hPhiBound : Nat.card (frattini Q) ≤ 4 := by omega
  let : IsMulCommutative (frattini Q) := by
    obtain ⟨exponent, hexponent⟩ := (htwo.to_subgroup (frattini Q)).exists_card_eq
    have hsmall : exponent ≤ 2 := by
      by_contra hnot
      have hbad : 2 ^ 3 ≤ 2 ^ exponent := Nat.pow_le_pow_right (by decide) (by omega)
      rw [← hexponent] at hbad
      norm_num at hbad
      omega
    interval_cases exponent
    · let : IsCyclic (frattini Q) := isCyclic_of_card_dvd_prime (p := 2) (by
        rw [hexponent]; norm_num)
      infer_instance
    · let : IsCyclic (frattini Q) := isCyclic_of_card_dvd_prime (p := 2) (by
        rw [hexponent]; norm_num)
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hexponent
  have hpow : aut ^ 7 = 1 := by simpa only [horder] using pow_orderOf_eq_one aut
  have hfixPhi := order_seven_fixes_card_lt_seven (by omega : Nat.card (frattini Q) < 7)
    (MulAut.characteristic (frattini Q) aut) (by rw [← map_pow, hpow, map_one])
  have hfix (point : frattini Q) : aut point = point :=
    congrArg (fun a : MulAut (frattini Q) => (a point : Q)) hfixPhi
  let line := Subgroup.zpowers aut
  have hlineOdd : Odd (Nat.card line) := by
    change Odd (Nat.card (Subgroup.zpowers aut))
    rw [Nat.card_zpowers, horder]
    decide
  have hinj := odd_frattini_action_injective htwo line hlineOdd
  have hquotNe : Subgroup.quotientAut (frattini Q) aut ≠ 1 := by
    intro heq
    have hsub : (⟨aut, Subgroup.mem_zpowers aut⟩ : line) = 1 := hinj (by simpa using heq)
    have haut : aut = 1 := congrArg Subtype.val hsub
    simp [haut] at horder
  have hfree := nontrivial_order_seven_fixedPointFree_card_eight hquotient
    (Subgroup.quotientAut (frattini Q) aut) (by rw [← map_pow, hpow, map_one]) hquotNe
  exact central_of_fixed_automorphism_and_fixedPointFree_quotient (frattini Q) aut hfix hfree


private theorem elementary_derived_of_central_frattini
    {Q : Type*} [Group Q] [Finite Q] (htwo : IsPGroup 2 Q)
    (hcentral : frattini Q ≤ Subgroup.center Q) : IsElementaryAbelian 2 (commutator Q) := by
  let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  have hderived : commutator Q ≤ Subgroup.center Q :=
    (commutator_le_frattini_of_isPGroup (p := 2)).trans hcentral
  let : IsMulCommutative (commutator Q) := ⟨⟨fun left right => Subtype.ext
    ((Subgroup.mem_center_iff.mp (hderived left.property) right).symm)⟩⟩
  let K := (powMonoidHom 2 : Subgroup.center Q →* Subgroup.center Q).ker.map
    (Subgroup.center Q).subtype
  have hle : commutator Q ≤ K := by
    change ⁅(⊤ : Subgroup Q), ⊤⁆ ≤ K
    apply Subgroup.commutator_le.mpr
    intro left _ right _
    have hmem := hderived (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top left) (Subgroup.mem_top right))
    have hcomm := Subgroup.mem_center_iff.mp hmem left
    have hbracket : ⁅left ^ 2, right⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_center_iff.mp
          (hcentral (pth_power_mem_frattini_of_isPGroup (p := 2) left)) right).symm)
    have hpow : ⁅left, right⁆ ^ 2 = 1 := by
      rw [pow_two, commutatorElement_mul_left_eq_conj_mul, hcomm] at hbracket
      simpa only [mul_inv_cancel_right, ← pow_two] using hbracket
    refine ⟨⟨⁅left, right⁆, hmem⟩, ?_, rfl⟩
    change (⟨⁅left, right⁆, hmem⟩ : Subgroup.center Q) ^ 2 = 1
    exact Subtype.ext hpow
  refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
  intro element
  obtain ⟨member, hmember, heq⟩ := hle element.property
  change member ^ 2 = 1 at hmember
  apply Subtype.ext
  have hpow := congrArg Subtype.val hmember
  change (member : Q) = (element : Q) at heq
  change (member : Q) ^ 2 = 1 at hpow
  rw [heq] at hpow
  exact hpow


/-- Seven does not divide an odd automorphism subgroup in the rank-three
Frattini quotient branch of the small nonabelian two-group bound. -/
public theorem not_seven_dvd_odd_actor_card_of_quotient_eight
    {Q : Type*} [Group Q] [Finite Q]
    (htwo : IsPGroup 2 Q) (hnoncomm : ¬ IsMulCommutative Q)
    (hbound : Nat.card Q ≤ 32) (hquotient : Nat.card (Q ⧸ frattini Q) = 8)
    (actor : Subgroup (MulAut Q)) (hodd : Odd (Nat.card actor)) :
    ¬ 7 ∣ Nat.card actor := by
  intro hseven
  obtain ⟨element, horder⟩ := exists_prime_orderOf_dvd_card' 7 hseven
  let aut : MulAut Q := element
  have horderAut : orderOf aut = 7 := by
    simpa only [aut, Subgroup.orderOf_coe] using horder
  have hpow : aut ^ 7 = 1 := by simpa only [horderAut] using pow_orderOf_eq_one aut
  have hcentral := frattini_central_of_order_seven_and_quotient_eight
    htwo hbound hquotient aut horderAut
  let : Fact (IsPGroup 2 Q) := ⟨htwo⟩
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  let : IsElementaryAbelian 2 (commutator Q) := elementary_derived_of_central_frattini htwo hcentral
  have hderived : commutator Q ≤ frattini Q := commutator_le_frattini_of_isPGroup (p := 2)
  have hexists : ∃ left right : Q, left * right ≠ right * left := by
    by_contra hnot
    push Not at hnot
    exact hnoncomm ⟨⟨hnot⟩⟩
  obtain ⟨left, right, hne⟩ := hexists
  let bracket : commutator Q := ⟨⁅left, right⁆, Subgroup.commutator_mem_commutator
    (Subgroup.mem_top left) (Subgroup.mem_top right)⟩
  have hbracketNe : (Additive.ofMul bracket : Additive (commutator Q)) ≠ 0 := by
    intro heq
    have hone : bracket = 1 := congrArg Additive.toMul heq
    exact hne (commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val hone))
  obtain ⟨functional, hfunctional⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) hbracketNe
  let scalar : commutator Q →* Multiplicative (ZMod 2) :=
    { toFun := fun point => Multiplicative.ofAdd (functional (Additive.ofMul point))
      map_one' := congrArg Multiplicative.ofAdd (map_zero functional)
      map_mul' := fun first second => congrArg Multiplicative.ofAdd
        (map_add functional (Additive.ofMul first) (Additive.ofMul second)) }
  have hscalarNe : scalar bracket ≠ 1 := by
    intro heq
    exact hfunctional (congrArg Multiplicative.toAdd heq)
  obtain ⟨form, hform, halt, hpreserve⟩ :=
    Subgroup.exists_nonzero_invariant_central_quotient_form (frattini Q)
      hcentral hderived scalar left right hscalarNe
  have hcount := (frattini Q).index_mul_card
  change Nat.card (Q ⧸ frattini Q) * Nat.card (frattini Q) = Nat.card Q at hcount
  rw [hquotient] at hcount
  have hfixPhi := order_seven_fixes_card_lt_seven (by omega : Nat.card (frattini Q) < 7)
    (MulAut.characteristic (frattini Q) aut) (by rw [← map_pow, hpow, map_one])
  have hfix (point : commutator Q) : aut point = point :=
    congrArg (fun a : MulAut (frattini Q) => (a ⟨point, hderived point.property⟩ : Q)) hfixPhi
  let linearize : MulAut (Q ⧸ frattini Q) ≃*
      (Additive (Q ⧸ frattini Q) ≃ₗ[ZMod 2] Additive (Q ⧸ frattini Q)) :=
    { toFun := fun a => { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
      invFun := fun a => MulEquiv.toAdditive.symm a.toAddEquiv
      left_inv := by intro a; ext; rfl
      right_inv := by intro a; ext; rfl
      map_mul' := by intro a b; ext; rfl }
  have hsize := Module.natCard_eq_pow_finrank
    (K := ZMod 2) (V := Additive (Q ⧸ frattini Q))
  change Nat.card (Q ⧸ frattini Q) = _ at hsize
  have hdim : Module.finrank (ZMod 2) (Additive (Q ⧸ frattini Q)) ≤ 4 := by
    have hpower : 2 ^ Module.finrank (ZMod 2) (Additive (Q ⧸ frattini Q)) = 2 ^ 3 := by
      simpa only [Nat.card_zmod, hquotient, show (2 : ℕ) ^ 3 = 8 by decide] using hsize.symm
    have heq := Nat.pow_right_injective (by decide : 1 < 2) hpower
    omega
  have hquotPow : Subgroup.quotientAut (frattini Q) aut ^ 7 = 1 := by
    rw [← map_pow, hpow, map_one]
  have hlinear := BinaryAlternatingFour.nonzero_alternating_form_order_seven_eq_one
    hdim form hform halt (linearize (Subgroup.quotientAut (frattini Q) aut))
    (by rw [← map_pow, hquotPow, map_one])
    (fun first second => hpreserve aut hfix first.toMul second.toMul)
  have hquotOne : Subgroup.quotientAut (frattini Q) aut = 1 :=
    linearize.injective (hlinear.trans linearize.map_one.symm)
  have helementOne : element = 1 := (odd_frattini_action_injective htwo actor hodd)
    (by simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_one] using hquotOne)
  simp [helementOne] at horder

end SmallNonabelianTwoGroup
