module

public import Theory.Mathieu.M12.A5Fixer.Inputs
public import Theory.Mathieu.M12.A5Fixer.Automorphisms.OuterIndex

/-!
# Full automorphism inputs for the M₁₂–A₅ fixer

The imported `Automorphisms.outerIndexBound` proves the outer-index bound for
all abstract automorphisms of the actual Witt-design carrier. Its proof uses
two finite Sylow fusion tests, the known pointwise Sylow fixer, and Sylow
conjugacy.

The order-four exclusion below remains conditional on `FiveFixerExponent`.
Cauchy's theorem extracts a fixed element of order five. Since the Sylow
five-subgroups have order five, conjugacy transports its entire cyclic group
to the marked one. The conjugated automorphism would then have order four
and exponent dividing ten, which is impossible. This module does not yet
assert the remaining exponent calculation or the unconditional exclusion.

Source context: Aschbacher–Smith 16.1.5(4), 16.1.7(3f), and 16.3.5,
combined manuscript of 1 March 2004, printed pp.1171–1173 and 1178–1179.
-/

public section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M12A5Fixer.Automorphisms

private noncomputable def fiveSylow (x : M12) (hx : orderOf x = 5) : Sylow 5 M12 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact Sylow.ofCard (zpowers x) (by rw [Nat.card_zpowers, hx, m12_order]; decide +kernel)

/-- Cauchy's theorem and Sylow-five conjugacy reduce the full order-four
fixed-subgroup exclusion to the marked five-element fixer calculation. -/
theorem orderFourFixedFiveExclusion_of_fiveFixerExponent
    (hexp : FiveFixerExponent) : OrderFourFixedFiveExclusion := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro a ha hfive
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := a.fixedSubgroup) 5 hfive
  have hx' : orderOf (x : M12) = 5 := (Subgroup.orderOf_coe x).trans hx
  let P := fiveSylow x hx'
  let Q := fiveSylow fiveElement fiveElement_order
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 P Q
  let e : MulAut M12 := MulAut.conj g
  let b : MulAut M12 := MulAut.congr e a
  have hmem : e.symm fiveElement ∈ zpowers (x : M12) := by
    have hm : fiveElement ∈ (g • P : Sylow 5 M12) := by
      rw [hg]
      exact mem_zpowers fiveElement
    change fiveElement ∈ (zpowers (x : M12)).map e.toMonoidHom at hm
    obtain ⟨y, hy, hey⟩ := hm
    have hye : y = e.symm fiveElement := (e.eq_symm_apply).mpr hey
    rwa [hye] at hy
  have hle : zpowers (x : M12) ≤ a.fixedSubgroup := zpowers_le.mpr x.property
  have hb : b fiveElement = fiveElement := by
    change e (a (e.symm fiveElement)) = fiveElement
    rw [(MulAut.mem_fixedSubgroup a _).mp (hle hmem), e.apply_symm_apply]
  have hd := orderOf_dvd_of_pow_eq_one (hexp b hb)
  have ho : orderOf b = 4 := ((MulAut.congr e).orderOf_eq a).trans ha
  rw [ho] at hd
  norm_num at hd

end Sporadic.Mathieu.M12A5Fixer.Automorphisms
