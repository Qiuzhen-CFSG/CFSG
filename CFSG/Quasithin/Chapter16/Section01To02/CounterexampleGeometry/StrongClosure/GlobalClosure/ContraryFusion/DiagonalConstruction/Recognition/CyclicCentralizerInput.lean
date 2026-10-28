module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import Theory.GroupTheory.PGroup.CentralSquareCyclicCentralizerRecognition

/-!
# The cyclic-centralizer input in Aschbacher's diagonal argument

The Sylow containment supplies the two-group hypothesis, and the source's
left rank hypothesis supplies the elementary four-group. The general
central-square recognition theorem then gives the actual dihedral or
semidihedral model required by the diagonal centralizer-rank argument.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, the sentence beginning “If C_A(u) is cyclic”.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

/-- The cyclic-centralizer alternative in the diagonal argument, using the
source's Sylow containment and elementary rank hypotheses. -/
theorem cyclicCentralizerRecognition
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}
    (h : Hypotheses S A₁ A₂) (u : A₁)
    (hu : orderOf u = 4) (huZ : u ^ 2 ∈ center A₁)
    (hC : IsCyclic (centralizer ({u} : Set A₁))) : DihedralOrSemidihedral A₁ := by
  obtain ⟨E, hE, hs⟩ := h.left_rank
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := BenderSuzuki.PFchapter1section1.isMulCommutative_of_forall_sq_one hs
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hs }
  have hP := S.isPGroup'.to_le h.left_le
  exact hP.exists_dihedral_or_semidihedral_of_cyclic_centralizer_of_central_square
    E hE u hu huZ hC

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
