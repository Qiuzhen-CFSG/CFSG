module

public import CFSG.Quasithin.MainConverse.ReeSections.MaximalCover.Exhaustion.Branches

/-!
# Finite-group reduction of Malle exhaustion

A solvable maximal subgroup already satisfies the list's solvability clause.
Otherwise, a nontrivial solvable radical supplies a characteristic abelian
subgroup. If the radical is trivial, either there is a nonabelian simple normal
subgroup, or conjugating a component produces two distinct commuting components.

The theorem below assembles the three corresponding intrinsic classification
inputs. It is conditional: this module does not yet prove Malle exhaustion.
All three inputs must be proved for the genuine exceptional fixed-point group
before an unconditional `MalleMaximalAlternatives` theorem can be exported.

Source: Malle, J. Algebra 139 (1991), 52–69, and the list in the proof of
Theorem 5 of Himstedt–Nguyen–Tiep, arXiv:0910.4758, pp.2–3. The reduction here
uses the elementary solvable-radical argument and Aschbacher–Smith A.3.3.
-/

public section

namespace CFSG.Quasithin.MainConverse.ReeSections

open Subgroup

/-- Assemble the local, simple-normal, and multiple-component branches.
Their hypotheses are discharged by finite-group theory; the three intrinsic
Ree classification statements remain explicit obligations. -/
theorem malleMaximalAlternatives_of_three_branches
    (hlocal : AbelianCharacteristicMaximals)
    (hsimple : SimpleNormalMaximals)
    (hpair : CommutingComponentMaximals) : MalleMaximalAlternatives := by
  classical
  intro m hm M hM
  by_cases hsolv : Group.IsSolvable M
  · exact .torusNormalizer hsolv
  by_cases hR : solvableRadical M = ⊥
  · by_cases hS : ∃ S : Subgroup M,
        S.Normal ∧ IsSimpleGroup S ∧ ¬ IsMulCommutative S
    · obtain ⟨S, hSn, hSs, hSa⟩ := hS
      exact hsimple m hm M hM hsolv hR S hSn hSs hSa
    · obtain ⟨L, K, hL, hK, hne, hcomm⟩ :=
        exists_commuting_components_of_no_simple_normal hsolv hR
          (fun S hn hs ha => hS ⟨S, hn, hs, ha⟩)
      exact hpair m hm M hM hsolv hR L K hL hK hne hcomm
  · obtain ⟨A, hAchar, hAcomm, hAne⟩ :=
      exists_abelian_characteristic_of_solvableRadical_ne_bot hR
    exact hlocal m hm M hM hsolv A hAchar hAcomm hAne

end CFSG.Quasithin.MainConverse.ReeSections
