module

public import Theory.SpecificGroups.PSL2.QuinticWholeFusion
public import Theory.SpecificGroups.PSL2.QuadraticFieldCentralizer
public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups

/-!
# Marked quadratic semilinear whole-subgroup fusion

The actual conjugation action of a marked quadratic field involution supplies
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

/-- A literal marked quadratic field action gives whole elementary-subgroup
fusion by the normal component, against the originally supplied quintic core. -/
theorem quintic_quadratic_marked_whole_fusion
    {G : Type*} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 3 < p) (hF : Nat.card F = p ^ 2)
    (N : Subgroup G) [N.Normal] (e : N ≃* PSL(2,F))
    (hC : centralizer (N : Set G) = ⊥)
    (T : Sylow 2 G) (X : Subgroup G) (hXN : X ≤ N) (hfive : Nat.card X = 5)
    (hTX : (T : Subgroup G) ≤ normalizer X)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAne : A ≠ ⊥)
    (a : G) (haA : a ∈ A) (hgen : N ⊔ zpowers a = ⊤)
    (x : PGammaL2 F) (hx : orderOf x = 2) (hf : x.right ≠ 1)
    (hmark : MulAut.congr e (MulAut.conjNormal a) =
      pGammaL2ToMulAutPSL2 F
        ⟨p, 2, Fact.out, ho, by decide, hF⟩ (by rw [hF]; nlinarith) x) :
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
  obtain ⟨hi, ⟨eC⟩⟩ := quadratic_field_inner_centralizer ho hp hF N e a x hx hf hmark
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
