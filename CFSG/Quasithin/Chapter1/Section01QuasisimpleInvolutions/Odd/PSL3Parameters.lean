module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Common
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.CharacteristicTwo
public import Theory.SpecificGroups.PSL3.SylowFixedActions.OddPrimeInner

/-!
# The odd-prime PSL₃ parameter exclusion

The marked quotient action has order two, fixes a Sylow two-subgroup pointwise,
and has a full fixed subgroup of characteristic two. Over an odd prime field
with more than three elements, Sylow fixation forces the action to be inner.
Its actual centralizer then contains a normal SL₂ component, contradicting
the self-centralizing two-core. This uses the field and quotient isomorphism
from the source family, retaining the projective scalar kernel.

The final adapter proves precisely the `hlinear` conclusion consumed by
`MarkedInvolution.odd_of_parameters_and_centers`. The uniform matrix-action
theorem discharges the Sylow-fixer premise for every odd prime greater than
three, so the final parameter exclusion has no additional premise.

Source: Aschbacher--Smith, proof of 1.1.5(3), printed p.503 (PDF p.520).
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
variable {α : MulAut L} {P : Sylow 2 L}

/-- An inner quotient action is impossible over any odd field of order
larger than three. The component is in the full fixed group transported
by the marked central-quotient action. -/
theorem MarkedInvolution.linear_three_large_quotient_not_inner
    (d : MarkedInvolution α P) {F : Type*} [Field F] [Finite F]
    (ho : Odd (Nat.card F)) (hlarge : 3 < Nat.card F)
    (e : L ⧸ center L ≃* PSL(3,F)) :
    MulAut.centralQuotientAction e α ∉ MulAut.innerSubgroup PSL(3,F) := by
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  let : Group.IsPerfect PSL(3,F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨ha, hchar, _⟩ := d.centralQuotient_model_inputs e
  intro hi
  exact Matrix.PSL3.OddInvolutionFixed.inner_fixed_not_selfCentralizing_twoCore
    hlarge (GorensteinWalter.two_ne_zero_of_odd_card F ho)
    (MulAut.centralQuotientAction e α) ha hi hchar

/-- The precise `hlinear` adapter for the odd-family assembly. Its remaining
premise is uniform Sylow-fixer innerness on the actual simple perfect model,
which is independent of the characteristic-two component exclusion. -/
theorem MarkedInvolution.linear_three_parameters_of_sylow_fixers
    (d : MarkedInvolution α P)
    (hfix : ∀ (F : Type) [Field F] [Finite F]
      [IsSimpleGroup PSL(3,F)] [Group.IsPerfect PSL(3,F)]
      (p : ℕ), p.Prime → Odd p → 3 < p → Nat.card F = p →
      ∀ (Q : Sylow 2 PSL(3,F)) (a : MulAut PSL(3,F)),
        orderOf a = 2 → (∀ x ∈ Q, a x = x) → a ∈ MulAut.innerSubgroup PSL(3,F)) :
    ∀ p : ℕ, p.Prime → Odd p → ClassicalGroup.IsPSL (L ⧸ center L) 3 p → p = 3 := by
  intro p hp ho hmodel
  by_contra hp3
  have hlarge : 3 < p := by
    have ht := hp.two_le
    have hodd := Nat.odd_iff.mp ho
    omega
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  let : Group.IsPerfect PSL(3,F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨ha, _, Q, hQ⟩ := d.centralQuotient_model_inputs e
  exact d.linear_three_large_quotient_not_inner (hcard ▸ ho) (hcard ▸ hlarge) e
    (hfix F p hp ho hlarge hcard Q (MulAut.centralQuotientAction e α) ha hQ)

/-- The PSL₃ branch of the source parameter exclusion: the marked involution
forces the odd prime to be three. This discharges `hlinear` in
`MarkedInvolution.odd_of_parameters_and_centers`. -/
theorem MarkedInvolution.linear_three_parameters (d : MarkedInvolution α P) :
    ∀ p : ℕ, p.Prime → Odd p → ClassicalGroup.IsPSL (L ⧸ center L) 3 p → p = 3 := by
  apply d.linear_three_parameters_of_sylow_fixers
  intro F _ _ _ _ p hp ho hlarge hcard Q a ha hfix
  exact Matrix.PSL3.SylowFixedActions.OddPrime.involution_mem_inner_of_fixes_sylow
    p hp ho hlarge hcard Q a ha hfix

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
