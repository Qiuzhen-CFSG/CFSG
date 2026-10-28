module

public import Theory.SpecificGroups.PSL2.QuadraticFieldInvolutionFixed
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Actual inner centralizers of quadratic field involutions

A marked semilinear action on a normal PSL₂ subgroup identifies the actual
inner centralizer with the fixed subgroup of that same automorphism. The
proved quadratic fixed-subgroup calculation therefore supplies both odd
index and the full PGL₂ fixed-field model on the original centralizer.

This retains the component and involution used in the whole-subgroup fusion
step of Aschbacher--Smith 6.1.4, printed p.666.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

/-- The actual normal-component centralizer has odd index and the fixed-field
PGL₂ model when its marked action is a quadratic field involution. -/
theorem quadratic_field_inner_centralizer
    {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 3 < p) (hF : Nat.card F = p ^ 2)
    (N : Subgroup G) [N.Normal] (e : N ≃* PSL(2,F)) (a : G)
    (x : PGammaL2 F) (hx : orderOf x = 2) (hf : x.right ≠ 1)
    (hmark : MulAut.congr e (MulAut.conjNormal a) =
      pGammaL2ToMulAutPSL2 F
        ⟨p, 2, Fact.out, ho, by decide, hF⟩ (by rw [hF]; nlinarith) x) :
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
  obtain ⟨hi, ⟨d⟩⟩ := quadratic_semilinear_involution_fixed ho hp hF x hx hf
  let e₀ := MulAut.fixedSubgroupCongr e b
  have hm : Nonempty (b.fixedSubgroup ≃*
      (pGammaL2ToMulAutPSL2 F
        ⟨p, 2, Fact.out, ho, by decide, hF⟩ (by rw [hF]; nlinarith) x).fixedSubgroup) := by
    rw [← hmark]
    exact ⟨e₀⟩
  obtain ⟨e₁⟩ := hm
  have hi' : b.fixedSubgroup.index =
      (pGammaL2ToMulAutPSL2 F
        ⟨p, 2, Fact.out, ho, by decide, hF⟩ (by rw [hF]; nlinarith) x).fixedSubgroup.index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := b.fixedSubgroup))
    rw [b.fixedSubgroup.card_mul_index, Nat.card_congr e₁.toEquiv,
      Subgroup.card_mul_index, Nat.card_congr e.toEquiv]
  rw [← hb]
  exact ⟨hi' ▸ hi, ⟨e₁.trans d⟩⟩

end Theory.PSL2
