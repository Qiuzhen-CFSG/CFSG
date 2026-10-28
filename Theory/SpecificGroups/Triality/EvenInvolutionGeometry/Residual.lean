module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.RootElements
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Embedded fixed two-residuals inside triality parabolics

A root parabolic means a conjugate of one of the two subgroups constructed
from the pinned D4 curves, with the actual elementary and central-quotient
conventions. Once a fixed subgroup is contained in such an overgroup, its
relative fixed subgroup has exactly the same embedded two-residual. The
embedding on the right passes through both subgroup inclusions.

This is the transfer step in Aschbacher–Smith 16.1.4(1), printed p.1171
(`refs/quasithin.pdf`). The residual is O² (quotient a two-group), not O₂ or
O^{2′}. Properness and centralizer containment must still be established
by the root geometry; neither is incorporated into the definitions here.
-/

@[expose] public section
namespace Triality.Standard.EvenInvolutionGeometry
open Parabolics Subgroup
variable (n : ℕ) (hn : 0 < n)

/-- Conjugates of the actual descended root parabolics. -/
def IsRootParabolic (Q : Subgroup (BinaryCarrier n hn)) : Prop :=
  ∃ a : Node, ∃ g : BinaryCarrier n hn,
    Q = (parabolic (binaryParameters n hn) a).map (MulAut.conj g).toMonoidHom

/-- Equality in the original carrier, keeping both inclusions on the relative
side. The geometric containment is an explicit, still necessary premise. -/
theorem fixedResidual_eq_in_subgroup (r : MulAut (BinaryCarrier n hn))
    (Q : Subgroup (BinaryCarrier n hn)) (h : r.fixedSubgroup ≤ Q) :
    (pResidual 2 r.fixedSubgroup).map r.fixedSubgroup.subtype =
      ((pResidual 2 (r.fixedSubgroup.subgroupOf Q)).map
        (r.fixedSubgroup.subgroupOf Q).subtype).map Q.subtype := by
  have transfer {G : Type} [Group G] [Finite G] (C Q : Subgroup G) (hC : C ≤ Q) :
      (pResidual 2 C).map C.subtype =
        ((pResidual 2 (C.subgroupOf Q)).map (C.subgroupOf Q).subtype).map Q.subtype := by
    symm
    rw [map_embedded_pResidual, map_subgroupOf_eq_of_le hC]
  exact transfer r.fixedSubgroup Q h

end Triality.Standard.EvenInvolutionGeometry
