module

public import BenderSuzuki.SE.Models
public import Theory.SpecificGroups.PSL2.OuterSolvable.BinaryCyclic
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage
public import Theory.SpecificGroups.Suzuki.CyclicOuter
public import Theory.SpecificGroups.SU3.OuterSolvable
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Coverage

/-!
# Solvable outer groups of the actual simple Bender models

The binary PSL₂ and Suzuki outer groups are cyclic by the proved inner-field
coverage. For projective SU₃ the proved unitary-semilinear coverage makes the
outer quotient metabelian. Transport through the original model equivalences
therefore gives solvability for every member of the native three-family
Bender predicate, without a coverage or classification premise.

Source: GLS3, Theorem 2.5.12 and §2.7; the automizer step in
Aschbacher--Smith I.8.5(2), printed p.430.
-/

namespace BenderSuzuki
open _root_.BenderSuzuki.MatrixGroups

/-- The actual outer group of every native simple Bender model is solvable. -/
public theorem IsSimpleBenderGroup.outer_isSolvable
    {G : Type*} [Group G] [Finite G] (hG : IsSimpleBenderGroup G) :
    Group.IsSolvable (MulAut.Outer G) := by
  rcases hG with ⟨⟨n, _hn, ⟨e⟩⟩⟩ | ⟨⟨m, hm, ⟨e⟩⟩⟩ |
      ⟨⟨n, hn, E, hfield, hfinite, J, hJ, hcard, hfixed, ⟨e⟩⟩⟩
  · let : IsCyclic (MulAut.Outer (PSL2BinaryMatrixGroup n)) :=
      Theory.PSL2.OuterSolvable.outer_isCyclic_of_field_coverage
        ZD.Linear.semilinear_coverage
    let : CommGroup (MulAut.Outer (PSL2BinaryMatrixGroup n)) :=
      IsMulCommutative.instCommGroup
    exact MulAut.isSolvable_outer_of_mulEquiv e
  · let : IsCyclic (MulAut.Outer (SuzukiMatrixGroup m)) := suzuki_outer_isCyclic m hm
    let : CommGroup (MulAut.Outer (SuzukiMatrixGroup m)) := IsMulCommutative.instCommGroup
    exact MulAut.isSolvable_outer_of_mulEquiv e
  · let : Field E := hfield
    let : Finite E := hfinite
    let : Group.IsSolvable (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J)) :=
      J.outer_isSolvable_of_semilinear_coverage hJ (J.semilinear_coverage n hn hJ hcard hfixed)
    exact MulAut.isSolvable_outer_of_mulEquiv e

end BenderSuzuki
