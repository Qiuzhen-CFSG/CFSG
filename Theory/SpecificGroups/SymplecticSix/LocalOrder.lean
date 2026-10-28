module
public import Theory.SpecificGroups.SymplecticSix.FixedRadical
public import Theory.Representation.SymplecticConjugatePair.OddOrder.Linear
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility

/-!
# Odd prime divisors of binary symplectic six-space locals

An order-seven matrix has zero fixed space: its displacement is a positive
multiple of three and its fixed space is nondegenerate alternating, hence even.
An order-five matrix fixes at most two dimensions. A prime-order actor fixes
any invariant subspace smaller than its binary irreducible degree. Thus a
stabilizer of a nonzero space of dimension at most three cannot have both five
and seven dividing its order. The actual isotropic-space construction applies
this to every two-local in Sp₆(2).

This is the local model calculation for Aschbacher--Smith 4.4.12 and 12.1.9,
printed pp.621--622,793. It uses the literal symplectic representation and the
coprime averaging theorem, without a parabolic classification assumption.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Module
namespace Theory.SpecificGroups.SymplecticSix
open TwoLocalCover
local notation "F" => ZMod 2
local notation "V" => Vector F

private theorem natural_injective : Function.Injective (symplecticNatural 3 (k := F)) := by
  intro g h he
  apply Subtype.ext
  exact Matrix.toLin'.injective he

private theorem fixed_even (g : Sp F) (ho : Odd (orderOf g)) :
    Even (finrank F (fixedSpace (symplecticNatural 3) (zpowers g))) := by
  let : Fintype (zpowers g) := Fintype.ofFinite _
  have hc : (Fintype.card (zpowers g) : F) = 1 := by
    rw [←Nat.card_eq_fintype_card,Nat.card_zpowers]
    exact natCast_eq_one_of_odd_of_two_eq_zero ho (CharP.cast_eq_zero F 2)
  let : Invertible (Fintype.card (zpowers g) : F) :=
    invertibleOfNonzero (by rw [hc]; exact one_ne_zero)
  exact SymplecticConjugatePair.OddOrder.even_finrank_of_nondegenerate
    ((form F).restrict (fixedSpace (symplecticNatural 3) (zpowers g)))
    (fun v => form_alternating.self_eq_zero v.val)
    (SymplecticConjugatePair.OddOrder.invariants_nondegenerate
      ((symplecticNatural 3).comp (zpowers g).subtype)
      (form F) form_alternating form_nondegenerate
      (fun a x y => preserves_form a.val x y))

/-- Order-seven matrices fix no nonzero vector on the literal binary six-space. -/
theorem fixedSpace_seven_eq_bot (g : Sp F) (hg : orderOf g = 7) :
    fixedSpace (symplecticNatural 3) (zpowers g) = ⊥ := by
  have hlo := prime_order_le_fixedCodim (symplecticNatural 3) natural_injective
    (by decide : Nat.Prime 7) (by decide) g hg
  have hd := orderOf_two_dvd_fixedCodim_of_isPGroup (symplecticNatural 3)
    (by decide : Nat.Prime 7) (by decide) (zpowers g)
    (IsPGroup.of_card (p := 7) (n := 1) (by simpa only [Nat.card_zpowers,pow_one] using hg))
  rw [BinaryPrimeDegree.orderOf_two_mod_seven] at hlo hd
  have he := fixedCodim_add_finrank (symplecticNatural 3 (k := F)) (zpowers g)
  have hev := fixed_even g (hg ▸ (by decide : Odd 7))
  simp only [finrank_pi,Fintype.card_sum,Fintype.card_fin] at he
  apply Submodule.finrank_eq_zero.mp
  obtain ⟨k,hk⟩ := hev
  omega

/-- Order-five matrices have at most two fixed dimensions. -/
theorem fixedSpace_five_finrank_le_two (g : Sp F) (hg : orderOf g = 5) :
    finrank F (fixedSpace (symplecticNatural 3) (zpowers g)) ≤ 2 := by
  have hlo := prime_order_le_fixedCodim (symplecticNatural 3) natural_injective
    (by decide : Nat.Prime 5) (by decide) g hg
  rw [BinaryPrimeDegree.orderOf_two_mod_five] at hlo
  have he := fixedCodim_add_finrank (symplecticNatural 3 (k := F)) (zpowers g)
  simp only [finrank_pi,Fintype.card_sum,Fintype.card_fin] at he
  omega

private theorem small_invariant_fixed
    (W : Submodule F V) (g : Sp F) (hW : g ∈ stabilizer W)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : orderOf g = p)
    (hd : finrank F W < orderOf (2 : ZMod p)) :
    W ≤ fixedSpace (symplecticNatural 3) (zpowers g) := by
  let ρ : Representation F (zpowers g) V :=
    (symplecticNatural 3 (k := F)).comp (zpowers g).subtype
  have hstable : ∀ a : zpowers g, ∀ x ∈ W, ρ a x ∈ W := by
    intro a x hx
    have ha : a.val ∈ stabilizer W := zpowers_le.mpr hW a.property
    exact (mem_stabilizer_iff W a.val).mp ha x hx
  let σ := ρ.subrepresentation W hstable
  have hdvd := orderOf_two_dvd_fixedCodim_of_isPGroup σ hp hp2 ⊤
    ((IsPGroup.of_card (p := p) (n := 1)
      (by simpa only [Nat.card_zpowers,pow_one] using hg)).to_subgroup ⊤)
  have he := fixedCodim_add_finrank σ ⊤
  have hzero : fixedCodim σ ⊤ = 0 := by
    by_contra hz
    have hh := Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hdvd
    omega
  have htop : fixedSpace σ ⊤ = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  intro x hx a
  have hf := (show (⟨x,hx⟩ : W) ∈ fixedSpace σ ⊤ from htop ▸ Submodule.mem_top) ⟨a,mem_top a⟩
  exact congrArg Subtype.val hf

/-- A nonzero subspace of dimension at most three cannot have both five and seven
dividing the order of its full symplectic stabilizer. -/
theorem not_five_seven_dvd_stabilizer
    (W : Submodule F V) (hW : W ≠ ⊥) (hd : finrank F W ≤ 3) :
    ¬ (5 ∣ Nat.card (stabilizer W) ∧ 7 ∣ Nat.card (stabilizer W)) := by
  rintro ⟨h5,h7⟩
  by_cases hdim : finrank F W < 3
  · let : Fact (Nat.Prime 7) := ⟨by decide⟩
    obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := stabilizer W) 7 h7
    have hg' : orderOf (g : Sp F) = 7 := (Subgroup.orderOf_coe g).trans hg
    have hf := small_invariant_fixed W g.val g.property (by decide : Nat.Prime 7)
      (by decide) hg' (by rwa [BinaryPrimeDegree.orderOf_two_mod_seven])
    exact hW (bot_unique ((fixedSpace_seven_eq_bot g.val hg') ▸ hf))
  · let : Fact (Nat.Prime 5) := ⟨by decide⟩
    obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := stabilizer W) 5 h5
    have hg' : orderOf (g : Sp F) = 5 := (Subgroup.orderOf_coe g).trans hg
    have hf := small_invariant_fixed W g.val g.property (by decide : Nat.Prime 5)
      (by decide) hg' (by rw [BinaryPrimeDegree.orderOf_two_mod_five]; omega)
    have hh := (Submodule.finrank_mono hf).trans (fixedSpace_five_finrank_le_two g.val hg')
    omega

/-- No actual binary symplectic two-local has order divisible by 35. -/
theorem twoLocal_not_dvd_thirtyFive (M : Subgroup (Sp F)) (hM : IsTwoLocal M) :
    ¬ 35 ∣ Nat.card M := by
  obtain ⟨W,hW,hd,_,hMW⟩ := TwoLocalCover.twoLocal_stabilizes_isotropic M hM
  intro h35
  have hh := h35.trans (card_dvd_of_le hMW)
  exact not_five_seven_dvd_stabilizer W hW hd
    ⟨(by decide : 5 ∣ 35).trans hh,(by decide : 7 ∣ 35).trans hh⟩

end Theory.SpecificGroups.SymplecticSix
