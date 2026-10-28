module

public import Theory.SpecificGroups.PSL2.QuinticWholeFusion
public import Theory.SpecificGroups.PSL2.QuadraticFieldFixedAllOdd
public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups

/-!
# Quadratic semilinear whole-subgroup fusion in every odd characteristic

The fixed-field calculation includes characteristic three. The actual conjugation action of a marked quadratic field involution supplies
both its inner centralizer model and odd index. The elementary subgroup is
then simultaneously placed and fused by an element of the original normal
PSL₂ component. Neither a fixed-centralizer model nor a fusion statement is
assumed as an additional callback.

This is the field-generated model case of the final paragraph of
Aschbacher--Smith 6.1.4, printed p.666. The ambient group is N⟨a⟩; passage
from a larger automorphism overgroup retains a separate Sylow/core restriction.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

/-- The actual normal-component centralizer has odd index and the fixed-field
PGL₂ model when its marked action is a quadratic field involution. -/
private theorem quadratic_field_inner_centralizer_all_odd
    {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2)
    (N : Subgroup G) [N.Normal] (e : N ≃* PSL(2,F)) (a : G)
    (x : PGammaL2 F) (hx : orderOf x = 2) (hf : x.right ≠ 1)
    (hmark : MulAut.congr e (MulAut.conjNormal a) =
      pGammaL2ToMulAutPSL2 F
        ⟨p, 2, Fact.out, ho, by decide, hF⟩ (by have hp := (Fact.out : p.Prime).two_le; rw [hF]; nlinarith) x) :
    Odd ((centralizer ({a} : Set G)).subgroupOf N).index ∧
      Nonempty ((centralizer ({a} : Set G)).subgroupOf N ≃*
        PGL2 (FixedPoints.subfield (zpowers x.right) F)) := by
  let b : MulAut N := MulAut.conjNormal a
  have hb : b.fixedSubgroup = (centralizer ({a} : Set G)).subgroupOf N := by
    ext n
    rw [MulAut.mem_fixedSubgroup]
    change b n = n ↔ (n : G) ∈ centralizer ({a} : Set G)
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hn
      have hh : a * (n : G) * a⁻¹ = n := congrArg Subtype.val hn
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hn
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr hn.symm)
  obtain ⟨hi, ⟨d⟩⟩ := quadratic_semilinear_involution_fixed_all_odd ho hF x hx hf
  let e₀ := MulAut.fixedSubgroupCongr e b
  have hm : Nonempty (b.fixedSubgroup ≃*
      (pGammaL2ToMulAutPSL2 F
        ⟨p, 2, Fact.out, ho, by decide, hF⟩ (by have hp := (Fact.out : p.Prime).two_le; rw [hF]; nlinarith) x).fixedSubgroup) := by
    rw [← hmark]
    exact ⟨e₀⟩
  obtain ⟨e₁⟩ := hm
  have hi' : b.fixedSubgroup.index =
      (pGammaL2ToMulAutPSL2 F
        ⟨p, 2, Fact.out, ho, by decide, hF⟩ (by have hp := (Fact.out : p.Prime).two_le; rw [hF]; nlinarith) x).fixedSubgroup.index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := b.fixedSubgroup))
    rw [b.fixedSubgroup.card_mul_index, Nat.card_congr e₁.toEquiv,
      Subgroup.card_mul_index, Nat.card_congr e.toEquiv]
  rw [← hb]
  exact ⟨hi' ▸ hi, ⟨e₁.trans d⟩⟩


/-- A literal marked quadratic field action gives whole elementary-subgroup
fusion by the normal component, against the originally supplied quintic core. -/
theorem quintic_quadratic_all_odd_whole_fusion
    {G : Type*} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2)
    (N : Subgroup G) [N.Normal] (e : N ≃* PSL(2,F))
    (hC : centralizer (N : Set G) = ⊥)
    (T : Sylow 2 G) (X : Subgroup G) (hXN : X ≤ N) (hfive : Nat.card X = 5)
    (hTX : (T : Subgroup G) ≤ normalizer X)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (a : G) (haA : a ∈ A) (hgen : N ⊔ zpowers a = ⊤)
    (x : PGammaL2 F) (hx : orderOf x = 2) (hf : x.right ≠ 1)
    (hmark : MulAut.congr e (MulAut.conjNormal a) =
      pGammaL2ToMulAutPSL2 F
        ⟨p, 2, Fact.out, ho, by decide, hF⟩ (by have hp := (Fact.out : p.Prime).two_le; rw [hF]; nlinarith) x) :
    ∃ g ∈ N, A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      ¬ A.map (MulAut.conj g).toMonoidHom ≤ (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, 2, Fact.out, ho, by decide, hF⟩
  have h8 : 8 ∣ Nat.card PSL(2,F) := by
    by_contra hnot
    have hm := mod_eight_of_not_eight_dvd_card (hF ▸ ho.pow) hnot
    rw [hF] at hm
    have hoddmod : p % 2 = 1 := Nat.odd_iff.mp ho
    have hb : p % 8 < 8 := Nat.mod_lt _ (by decide)
    have hr : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    rcases hr with hh | hh | hh | hh <;> norm_num [Nat.pow_mod, hh] at hm
  obtain ⟨hi, ⟨eC⟩⟩ := quadratic_field_inner_centralizer_all_odd ho hF N e a x hx hf hmark
  have hs : orderOf x.right = 2 := orderOf_eq_prime_iff.mpr ⟨by
    have hh := congrArg SemidirectProduct.right (pow_orderOf_eq_one x)
    simpa only [hx, pow_two, SemidirectProduct.mul_right, SemidirectProduct.one_right] using hh,
    hf⟩
  let E := FixedPoints.subfield (zpowers x.right) F
  have hE : IsOddPrimePower (Nat.card E) :=
    ⟨p, 1, Fact.out, ho, by decide, by
      simpa only [pow_one] using OddSquareFieldFixed.fixed_subfield_card hF x.right hs⟩
  exact odd_quintic_whole_fusion_of_inner_centralizer hodd h8 hE N e hC T X hXN hfive hTX
    A hA hAne a haA hgen hi eC

end Theory.PSL2
