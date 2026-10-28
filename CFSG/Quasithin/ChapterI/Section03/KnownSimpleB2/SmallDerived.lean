module

public import Theory.SpecificGroups.SU3.BinaryG2Comparison
public import Theory.SpecificGroups.SU3.TernaryInvolutoryTwoComponents
public import Theory.SpecificGroups.PSL2.OddBinaryInvolutoryTwoComponents
public import Theory.SpecificGroups.ReeG2.TernaryDerivedEquiv
public import Theory.SpecificGroups.ReeG2.TernaryDerivedEquiv.MatrixHom
public import Theory.SpecificGroups.Tits.InvolutoryTwoComponents

/-!+# Small-derived carriers and the B₂ condition

The genuine exceptional isomorphism G₂(2)′ ≃ PSU₃(3) proves the binary
octonion case. For the ternary Ree carrier, the checked deleted permutation
representation supplies the matrix map; only its nine-point projective
identification remains an explicit input. Odd-degree binary PSL₂ has solvable
involution fixed groups, so the resulting equivalence proves B₂.

For the Tits carrier, the concrete binary Ree action on its derived subgroup
is already bijective and both root parabolics are solvable. The two remaining
source calculations are stated explicitly: full binary involution coverage
and containment of the two representative centralizers in root parabolics.
The conditional exports are not assertions that these inputs have been proved.

Sources: GLS II Definition 2.4; GLS III §2.2 (the exceptional isomorphisms),
Theorem 2.5.15 and §4.3; Aschbacher–Smith 16.1.4, printed p.1171.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterI.Section03.KnownSimpleB2

/-- The B₂ condition for the literal binary split-octonion derived group. -/
theorem binaryG2 : HasInvolutoryB2 (commutator (Atlas.G2.Model (ZMod 2))) := by
  let e := Classical.choice Atlas.G2.nonempty_commutator_binary_equiv_psu3
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
    Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup (ABG.PSU3 3 1 one_ne_zero) := e.symm.isSimpleGroup
  exact Matrix.SU3.ternary_hasInvolutoryB2.of_mulEquiv e

/-- The actual matrix homomorphism discharges the Ree side of the comparison.
The outstanding input identifies the specified nine-point permutation group. -/
theorem ternaryRee_of_projectiveEquiv
    (e : Atlas.ReeG2.TernaryDerived.PermutationModel ≃*
      Theory.PSL2.BinaryGroup 3) :
    HasInvolutoryB2 (commutator (Atlas.ReeG2.Model (ZMod 3) 0)) :=
  (Theory.PSL2.odd_binary_hasInvolutoryB2 (by decide : 2 ≤ 3) (by decide)).of_mulEquiv
    (Atlas.ReeG2.TernaryDerived.equivOfPermutationModel e
      Atlas.ReeG2.TernaryDerived.toRee Atlas.ReeG2.TernaryDerived.toRee_ne_one)

/-- The Tits case consumes precisely the two outstanding concrete root-table
calculations. Full automorphism coverage and parabolic solvability are discharged. -/
theorem tits_of_root_coverage
    (hcover : Tits.InvolutionRootGeometry.BinaryInvolutionCoverage)
    (hlong : ∃ P : Subgroup Tits.ParrottGroup,
      Tits.InvolutionRootGeometry.IsRootParabolic P ∧ P < ⊤ ∧
        centralizer {Tits.parrottGenerator .s1} ≤ P)
    (hshort : ∃ P : Subgroup Tits.ParrottGroup,
      Tits.InvolutionRootGeometry.IsRootParabolic P ∧ P < ⊤ ∧
        centralizer {Tits.parrottGenerator .s4} ≤ P) :
    HasInvolutoryB2 Tits.ParrottGroup :=
  Tits.InvolutionRootGeometry.hasInvolutoryB2_of_root_coverage hcover hlong hshort

end CFSG.Quasithin.ChapterI.Section03.KnownSimpleB2
