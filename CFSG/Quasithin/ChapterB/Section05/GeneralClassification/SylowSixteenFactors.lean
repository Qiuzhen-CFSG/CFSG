module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenSixSpace
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorModels
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorPermutation

/-!
# The product and hyperplane B.5 rows with Sylow order at most sixteen

The original faithful binary six-space rules out a factor with an element
of order seventeen and rules out two factors divisible by five. Together
with the actual Sylow-sixteen bound, the two-factor source has only A₅ or
S₅ on one side and S₃ on the other. The hyperplane source has an SL₃(2)
factor, whose two-part is already eight, and cannot contain five.
The outer A₆–C₃ alternative is not excluded by this order argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
open QuasisimpleSource
variable {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}

private theorem power_bound (small : ∀ S : Sylow 2 D, Nat.card S ≤ 16)
    {n : ℕ} (hd : 2 ^ n ∣ Nat.card D) : n ≤ 4 := by
  let S : Sylow 2 D := default
  have hh := S.pow_dvd_card_of_pow_dvd_card hd
  have hb : 2 ^ n ≤ 2 ^ 4 :=
    (Nat.le_of_dvd (Nat.card_pos (α := S)) hh).trans (small S)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb

private theorem no_twentyFive (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 6) : ¬25 ∣ Nat.card D := by
  intro h
  have hh := h.trans (Representation.card_dvd_card_GL_of_injective ρ hf)
  interval_cases d : Module.finrank (ZMod 2) V <;>
    rw [Matrix.card_GL_field] at hh <;>
    norm_num [Fin.prod_univ_succ] at hh

private theorem no_seventeen_factor (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 6) (A : Subgroup D)
    (h : 17 ∣ Nat.card A) : False := by
  have hh := BinaryPrimeDegree.orderOf_le_finrank ρ hf
    (by decide : Nat.Prime 17) (by decide) (h.trans A.card_subgroup_dvd_card)
  rw [BinaryPrimeDegree.orderOf_two_mod_seventeen] at hh
  omega

private def degreeOneField (F : BinaryField) (h : F.degree=1) :
    F.Carrier ≃+* ZMod 2 := by
  let : Fintype F.Carrier := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,F.card_eq,h]; simp)

private theorem linearTwo_factor_card (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 6)
    (small : ∀ S : Sylow 2 D, Nat.card S ≤ 16)
    (A : Subgroup D) (F : BinaryField) (e : A≃*SL(2,F.Carrier)) :
    Nat.card A=6 ∨ Nat.card A=60 ∨ Nat.card A=504 := by
  have hu : F.degree≤4 := by
    apply power_bound small
    apply dvd_trans _ A.card_subgroup_dvd_card
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula,F.card_eq]
    exact dvd_mul_right _ _
  have hl := F.degree_pos
  have hc : Nat.card A=2^F.degree*((2^F.degree)^2-1) := by
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula,F.card_eq]
  have hn : F.degree≠4 := by
    intro hF
    exact no_seventeen_factor hf hd A (by rw [hc,hF]; decide)
  interval_cases hF : F.degree <;> norm_num [hF] at hc ⊢ <;> omega

private theorem linearThree_factor_card
    (small : ∀ S : Sylow 2 D, Nat.card S ≤ 16)
    (A : Subgroup D) (F : BinaryField) (e : A≃*SL(3,F.Carrier)) : Nat.card A=168 := by
  have hu := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL,F.card_eq,←pow_mul] at hu
  have hb := power_bound small (hu.trans (by
    rw [←Nat.card_congr e.toEquiv]
    exact A.card_subgroup_dvd_card))
  have hF : F.degree=1 := by have := F.degree_pos; omega
  let a := e.trans (Atlas.fieldEquivSL 3 (degreeOneField F hF))
  exact (Nat.card_congr a.toEquiv).trans Matrix.PSL3Two.card_SL

private theorem factor_card (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 6)
    (small : ∀ S : Sylow 2 D, Nat.card S ≤ 16)
    {A : Subgroup D} {W : Subrepresentation ρ} (c : SourceFactorCase ρ A W) :
    Nat.card A=6 ∨ Nat.card A=60 ∨ Nat.card A=120 ∨ Nat.card A=504 ∨ Nat.card A=168 := by
  have rankOne (F : BinaryField) (e : A≃*SL(2,F.Carrier)) :=
    linearTwo_factor_card hf hd small A F e
  cases c with
  | natural _ hn =>
    cases hn with
    | linearTwo F he =>
      obtain ⟨e⟩ := he
      rcases rankOne F e.groupEquiv with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    | symmetricFive he =>
      obtain ⟨e⟩ := he
      exact Or.inr (Or.inr (Or.inl (by
        rw [Nat.card_congr e.groupEquiv.toEquiv]
        norm_num [Nat.card_eq_fintype_card,Fintype.card_perm])))
    | linearThree F _ he =>
      obtain ⟨e⟩ := he
      exact Or.inr (Or.inr (Or.inr (Or.inr (linearThree_factor_card small A F e.groupEquiv))))
  | doubleNatural F _ _ he =>
    obtain ⟨e⟩ := he
    exact Or.inr (Or.inr (Or.inr (Or.inr (linearThree_factor_card small A F e.groupEquiv))))
  | exceptional _ he =>
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (linearThree_factor_card small A BinaryField.two he.natural.groupEquiv))))

/-- Five-divisibility selects the original order-60 or order-120 factor and
the original order-six factor. No factor is replaced by an abstract model. -/
theorem twoFactor_card_rows (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 6)
    (small : ∀ S : Sylow 2 D, Nat.card S ≤ 16) (hfive : 5 ∣ Nat.card D)
    (c : SourceTwoFactorCase ρ) :
    ((Nat.card c.first=60 ∨ Nat.card c.first=120) ∧ Nat.card c.second=6) ∨
      (Nat.card c.first=6 ∧ (Nat.card c.second=60 ∨ Nat.card c.second=120)) := by
  have h25 := no_twentyFive hf hd
  have h32 : ¬32 ∣ Nat.card D := by
    intro hh
    have hb := power_bound small (n := 5) hh
    omega
  have he := c.product.card_eq
  rcases factor_card hf hd small c.firstCase with h1 | h1 | h1 | h1 | h1 <;>
    rcases factor_card hf hd small c.secondCase with h2 | h2 | h2 | h2 | h2
  all_goals first
    | exact Or.inl ⟨Or.inl h1,h2⟩
    | exact Or.inl ⟨Or.inr h1,h2⟩
    | exact Or.inr ⟨h1,Or.inl h2⟩
    | exact Or.inr ⟨h1,Or.inr h2⟩
    | norm_num [he,h1,h2] at *

/-- The hyperplane row cannot contain five under the actual Sylow-sixteen
bound: its literal SL₃(2) factor already contributes a two-part of eight. -/
theorem not_hyperplane (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 6)
    (small : ∀ S : Sylow 2 D, Nat.card S ≤ 16) (hfive : 5 ∣ Nat.card D)
    (c : HyperplaneCase ρ) : False := by
  have h1 : Nat.card c.first=168 :=
    (Nat.card_congr c.firstEquiv.toEquiv).trans Matrix.PSL3Two.card_SL
  have he := c.product.card_eq
  have h32 : ¬32 ∣ Nat.card D := by
    intro hh
    have hb := power_bound small (n := 5) hh
    omega
  cases c.secondCase with
  | linearThree _ _ hn =>
    obtain ⟨e⟩ := hn
    have h2 := linearThree_factor_card small c.second BinaryField.two e.groupEquiv
    norm_num [he,h1,h2] at hfive
  | linearTwo F hn =>
    obtain ⟨e⟩ := hn
    rcases linearTwo_factor_card hf hd small c.second F e.groupEquiv with h2 | h2 | h2
    · norm_num [he,h1,h2] at hfive
    · apply h32
      rw [he,h1,h2]
      decide
    · norm_num [he,h1,h2] at hfive

end CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
