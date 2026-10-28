module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.OtherModels.Covers
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.OtherModels.AlternatingSeven
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.OtherModels.LinearThree
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.OtherModels.UnitaryThree
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.OtherModels.MathieuTwelve

/-!
# Fixed-action obstructions for the non-PSL₂ component alternatives

This module assembles the intrinsic model facts used to eliminate the non-PSL₂
components in F.6.18. For a faithful elementary four-group acting on the actual
component and fixing a Sylow two-subgroup pointwise, some nonidentity actor has
a fixed subgroup whose two-core is not self-centralizing. Both the centralizer
and the two-core in this conclusion are internal to that fixed subgroup.

The complete correspondence with the source alternatives is:

* (6), (8): the actual triple-covered A₆ component is excluded by
  `center_three_fixed_action_obstruction`, or by
  `triple_cover_fixed_action_obstruction` for a supplied covering map.
* (7), (9): `alternating_seven_fixed_action_obstruction` handles A₇ in both
  A₇ and S₇. Their triple-covered components use the same odd-center result.
* (10), (11), linear sign: `linearThree_projective_fixed_action_obstruction`
  and `linearThree_special_fixed_action_obstruction` treat PSL₃(p) and SL₃(p),
  with precisely `p ≡ 5 mod 8`.
* (10), (11), unitary sign: `projective_unitary_fixed_action_obstruction`
  and `special_unitary_fixed_action_obstruction` treat PSU₃(p) and SU₃(p),
  with precisely `p ≡ 3 mod 8`, matrix field of order p², and fixed field of
  order p. Their perfectness and simplicity inputs come from the component.
* (12), (13): `mathieuTwelve_fixed_action_obstruction_unconditional` handles
  the actual Witt-design M₁₂ component in both M₁₂ and Aut(M₁₂).

The covered symmetric and graph extensions require no assumption about the
center or fixed subgroups of the whole extension: these theorems quantify over
every action on the component itself. The covers are those of Notation A.3.5,
with center of order three. In the special classical groups a nontrivial odd
center supplies the obstruction; otherwise the actual projective projection
is an isomorphism. The centerless classical and M₁₂ arguments already exclude
faithfulness, whereas the A₇ calculation produces an actual S₅ fixed subgroup.

The PSL₂ cases, including the surviving unextended A₆ ≅ PSL₂(9), belong to
`LinearModels`. The universal F.6.18 classification, its application to the
component, compatible extension actions and quotient transport remain with
`ComponentBranch`. No classification or model-identification premise is proved
merely by this collection of intrinsic calculations.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.6.18, printed pp.309–310, and the component paragraph
of 15.4.18, printed pp.1162–1163.
-/

open Subgroup

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels

/-- The unitary sign in the source selects exactly the residue three modulo eight. -/
public theorem unitaryThree_prime_restrictions_iff (p : ℕ) :
    ((p % 8 = 3 ∨ p % 8 = 5) ∧ p % 4 = 3) ↔ p % 8 = 3 := by omega

/-- The M₁₂ component obstruction with no automorphism-center premise.
The pointwise automorphism stabilizer of its Sylow subgroup has order at most
two, so the faithful order-four action is itself impossible. This applies to
the component of both F.6.18(12) and (13). -/
public theorem mathieuTwelve_fixed_action_obstruction_unconditional
    {A : Type*} [Group A] (P : Sylow 2 Sporadic.Mathieu.M12)
    (hA : Nat.card A = 4) (ρ : A →* MulAut Sporadic.Mathieu.M12)
    (hinj : Function.Injective ρ) (hfixed : ∀ a : A, ∀ x : P, ρ a x = x) :
    ∃ a : A, a ≠ 1 ∧
      ¬ centralizer (pCore 2 (ρ a).fixedSubgroup : Set (ρ a).fixedSubgroup) ≤
        pCore 2 (ρ a).fixedSubgroup :=
  (mathieuTwelve_no_faithful_sylow_fixed_action P hA ρ hfixed hinj).elim

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels
