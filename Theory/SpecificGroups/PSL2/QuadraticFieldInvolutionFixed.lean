module

public import Theory.SpecificGroups.PSL2.OddSquareFieldFixedIndex
public import GorensteinWalter.PGammaL2PureSemilinear
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Full fixed subgroups of arbitrary quadratic field involutions

Projective Hilbert90 transports an arbitrary semilinear involution with
nontrivial field coordinate to the pure coefficient involution. Transport
of the actual PSL₂ action preserves its whole fixed subgroup and its index.
Thus the fixed group is PGL₂ of the actual fixed prime field and has odd
index in the original PSL₂. No choice of a PSL₂ conjugacy class is assumed.

This is a model ingredient for the whole-subgroup fusion step in the final
paragraph of Aschbacher--Smith 6.1.4, printed p.666.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

/-- Every involution with nontrivial quadratic field part fixes a full Sylow
of the inner group; its whole fixed subgroup has the actual fixed-field
PGL₂ model. -/
theorem quadratic_semilinear_involution_fixed
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 3 < p) (hF : Nat.card F = p ^ 2)
    (x : PGammaL2 F) (hx : orderOf x = 2) (hf : x.right ≠ 1) :
    let hodd : IsOddPrimePower (Nat.card F) := ⟨p, 2, Fact.out, ho, by decide, hF⟩
    let hc : 3 < Nat.card F := by rw [hF]; nlinarith
    let a := pGammaL2ToMulAutPSL2 F hodd hc x
    Odd a.fixedSubgroup.index ∧ Nonempty
      (a.fixedSubgroup ≃* PGL2 (FixedPoints.subfield (zpowers x.right) F)) := by
  intro hodd hc a
  have hs : orderOf x.right = 2 := orderOf_eq_prime_iff.mpr ⟨by
    have hh := congrArg SemidirectProduct.right (pow_orderOf_eq_one x)
    simpa only [hx, pow_two, SemidirectProduct.mul_right, SemidirectProduct.one_right] using hh,
    hf⟩
  let f := pGammaL2ToMulAutPSL2 F hodd hc
  obtain ⟨c, hc⟩ := projective_semilinear_involution_conj_inr hodd x hx hf
  let b : MulAut PSL(2,F) := f (SemidirectProduct.inl c)
  have he : b⁻¹ * a * b = psl2FieldAut F x.right := by
    have hh := congrArg f hc
    simpa only [map_mul, map_inv, f, pGammaL2ToMulAutPSL2_inr] using hh
  have he' : MulAut.congr b.symm a = psl2FieldAut F x.right := by
    change b⁻¹ * a * b = _
    exact he
  have hm : Nonempty (a.fixedSubgroup ≃* (psl2FieldAut F x.right).fixedSubgroup) := by
    rw [← he']
    exact ⟨MulAut.fixedSubgroupCongr b.symm a⟩
  obtain ⟨e⟩ := hm
  obtain ⟨d⟩ := OddSquareFieldFixed.coefficient_fixed_equiv ho hF x.right hs
  have hi : a.fixedSubgroup.index = (psl2FieldAut F x.right).fixedSubgroup.index := by
    have hcard : Nat.card a.fixedSubgroup = Nat.card (psl2FieldAut F x.right).fixedSubgroup :=
      Nat.card_congr e.toEquiv
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := a.fixedSubgroup))
    rw [a.fixedSubgroup.card_mul_index, hcard,
      (psl2FieldAut F x.right).fixedSubgroup.card_mul_index]
  exact ⟨hi ▸ (OddSquareFieldFixed.coefficient_fixed_odd_index_nonsolvable ho hp hF x.right hs).1,
    ⟨e.trans d⟩⟩

end Theory.PSL2
