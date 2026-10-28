module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ProductComparison.Obstruction
/-!
# Comparing the product FF branches with the solvable Goldschmidt row

Every B.5.6 direct factor has order at least six. In a group of order 108,
the product makes each factor's order at most eighteen, forcing each to
have order six. The actual offender subgroup would therefore have order 36,
and its quotient in the ambient group would have order three, contradicting
the given two-group quotient. The outer and hyperplane cases already contain
A₆ and SL₃(2), respectively, too large to embed in that ambient group.

Thus F.6.18(2) gives the actual S₃ × S₃ equivalence for all three branches.
No recognition is inferred from order alone; the equivalence is precisely
the one in the retained source row.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(3)–(5), pp.105–110; F.6.18(2), p.309; 15.4.18, p.1163.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace ProductComparison
open FFAlternatives

private theorem linearThree_card_lower (F : BinaryField) : 168 ≤ Nat.card SL(3,F.Carrier) := by
  let f := Matrix.SpecialLinearGroup.map (n := Fin 3) (ZMod.castHom (dvd_refl 2) F.Carrier)
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    ext i j
    apply (ZMod.castHom (dvd_refl 2) F.Carrier).injective
    exact congrArg (fun c : SL(3,F.Carrier) => c.val i j) h
  rw [← Matrix.PSL3Two.card_SL]
  exact Nat.card_le_card_of_injective f hf

private theorem factor_card_lower {A : Type*} [Group A] (h : FactorModel A) : 6 ≤ Nat.card A := by
  cases h with
  | linearTwo F e =>
    rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two]
    have hq : 2 ≤ Nat.card F.Carrier := Finite.one_lt_card
    have hh : 3 ≤ Nat.card F.Carrier ^ 2 - 1 := by
      have hs : 4 ≤ Nat.card F.Carrier ^ 2 := by nlinarith
      omega
    exact (by decide : 6 ≤ 2 * 3).trans (Nat.mul_le_mul hq hh)
  | symmetricFive e =>
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  | linearThree F _ e =>
    rw [Nat.card_congr e.toEquiv]
    exact (by decide : 6 ≤ 168).trans (linearThree_card_lower F)

private theorem factor_card_eq_six {A : Type*} [Group A] (h : FactorModel A)
    (hc : Nat.card A ≤ 18) : Nat.card A = 6 := by
  cases h with
  | linearTwo F e =>
    rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two] at hc ⊢
    have hsmall : Nat.card F.Carrier < 4 := by
      by_contra h
      have hq : 4 ≤ Nat.card F.Carrier := by omega
      have hh : 15 ≤ Nat.card F.Carrier ^ 2 - 1 := by
        have hs : 16 ≤ Nat.card F.Carrier ^ 2 := by nlinarith
        omega
      have hd := Nat.mul_le_mul hq hh
      omega
    have hn : F.degree = 1 := by
      have hp := F.degree_pos
      by_contra h
      have htwo : 2 ≤ F.degree := by omega
      have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) htwo
      rw [← F.card_eq] at hpow
      norm_num at hpow
      omega
    norm_num [F.card_eq, hn]
  | symmetricFive e =>
    rw [Nat.card_congr e.toEquiv] at hc
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hc
  | linearThree F _ e =>
    have hh := linearThree_card_lower F
    rw [Nat.card_congr e.toEquiv] at hc
    omega

private theorem product_card_eq_thirtySix {A : Type*} [Group A]
    {B C : Subgroup A} (c : InternalProduct B C) (hB : FactorModel B) (hC : FactorModel C)
    (hc : Nat.card A ≤ 108) : Nat.card A = 36 := by
  have he : Nat.card B * Nat.card C = Nat.card A := by
    rw [← Nat.card_prod, Nat.card_congr c.equiv.toEquiv]
  have hb := factor_card_lower hB
  have hd := factor_card_lower hC
  have hBsmall : Nat.card B ≤ 18 := by nlinarith
  have hCsmall : Nat.card C ≤ 18 := by nlinarith
  rw [factor_card_eq_six hB hBsmall, factor_card_eq_six hC hCsmall] at he
  exact he.symm

universe u v
variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D} {K : GroupClass.{u}}
attribute [local instance] offenderSubgroup_normal

/-- The extraspecial alternative in F.6.18(2) is incompatible with an actual
two-factor FF offender. Its order 108 would give the quotient D/N order three. -/
theorem sourceTwoFactor_not_card_108 (h : ClassifiedAction K ρ G₁ G₂)
    (c : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype)) : Nat.card D ≠ 108 := by
  intro hd
  let N := offenderSubgroup ρ
  have hn : Nat.card N = 36 := product_card_eq_thirtySix c.product
    (c.firstCase.factorModel _) (c.secondCase.factorModel _)
    (by simpa [hd] using Nat.card_le_card_of_injective N.subtype N.subtype_injective)
  obtain ⟨k, hk⟩ := h.quotient_twoGroup.exists_card_eq
  have he : Nat.card N * 2 ^ k = Nat.card D := by
    rw [← hk, ← Subgroup.index_eq_card, Subgroup.card_mul_index]
  rw [hn, hd] at he
  have heq : 2 ^ k = 3 := by omega
  have hdiv : 3 ∣ 2 ^ k := by rw [heq]
  have := (by decide : Nat.Prime 3).dvd_of_dvd_pow hdiv
  norm_num at this

/-- The actual A₆ subgroup already exceeds the order of F.6.18(2)'s
extraspecial extension, independently of whether the outer extension splits. -/
theorem outerSixThree_not_card_108
    (c : OuterSixThreeCase (ρ.comp (offenderSubgroup ρ).subtype)) : Nat.card D ≠ 108 := by
  intro hd
  have hh := (Nat.card_le_card_of_injective c.first.subtype c.first.subtype_injective).trans
    (Nat.card_le_card_of_injective (offenderSubgroup ρ).subtype (offenderSubgroup ρ).subtype_injective)
  rw [Nat.card_congr c.firstEquiv.toEquiv, nat_card_alternatingGroup, Nat.card_fin, hd] at hh
  norm_num [Nat.factorial] at hh

/-- The actual SL₃(2) subgroup excludes the extraspecial extension also
for the exceptional hyperplane module. -/
theorem hyperplane_not_card_108
    (c : HyperplaneCase (ρ.comp (offenderSubgroup ρ).subtype)) : Nat.card D ≠ 108 := by
  intro hd
  have hh := (Nat.card_le_card_of_injective c.first.subtype c.first.subtype_injective).trans
    (Nat.card_le_card_of_injective (offenderSubgroup ρ).subtype (offenderSubgroup ρ).subtype_injective)
  rw [Nat.card_congr c.firstEquiv.toEquiv, Matrix.PSL3Two.card_SL, hd] at hh
  omega

/-- All three explicit branches exclude the extraspecial order 108. -/
theorem branch_not_card_108 (h : ClassifiedAction K ρ G₁ G₂)
    (hb : Branch (ρ.comp (offenderSubgroup ρ).subtype)) : Nat.card D ≠ 108 := by
  unfold Branch at hb
  rcases hb with hb | hb | hb <;> obtain ⟨hb⟩ := hb
  · exact sourceTwoFactor_not_card_108 h hb
  · exact outerSixThree_not_card_108 hb
  · exact hyperplane_not_card_108 hb

/-- Complete comparison with F.6.18(2), on the actual ambient group,
for every B.5.6(3)–(5) branch and every retained module extension. -/
theorem case2_equiv (h : ClassifiedAction K ρ G₁ G₂)
    (hb : Branch (ρ.comp (offenderSubgroup ρ).subtype))
    (hr : GoldschmidtAlternatives.Case2 D) :
    Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  rcases hr with he | he
  · exact he
  · apply (branch_not_card_108 h hb ?_).elim
    rw [he.card, HeisenbergPrime.card]
    norm_num [GoldschmidtAlternatives.E4, GoldschmidtAlternatives.C, Nat.card_prod]

end ProductComparison
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
