module

public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.MarkedModel
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Actual root parabolics and embedded centralizer residuals for the Tits group

The parabolics are inverse images of the fixed F₄ root parabolics under the
marked embedding into the full binary Ree group. Thus their definition retains
the derived-subgroup intersection. It neither asserts properness nor replaces
these groups by arbitrarily tagged subgroups.

If a centralizer is contained in such a parabolic, its intrinsic centralizer
inside that parabolic has the same image in the ambient group. Functoriality
of O² gives the equality of embedded residuals required by Aschbacher–Smith
16.1.4(1), printed p.1171. Properness and containment remain separate concrete
root calculations.
-/

@[expose] public section
namespace Tits.InvolutionRootGeometry
open Subgroup ReeF4 ReeF4.LargeLocalSeeds

/-- The intersection of the full root parabolic with the derived Tits carrier,
written on the presentation through its actual marked embedding. -/
noncomputable def rootParabolic (s : Side) : Subgroup ParrottGroup :=
  (Parabolics.parabolic 0 s).comap embedding

/-- A conjugate of one of the two root-defined standard parabolics. -/
def IsRootParabolic (P : Subgroup ParrottGroup) : Prop :=
  ∃ (s : Side) (g : ParrottGroup), P = (rootParabolic s).map (MulAut.conj g).toMonoidHom

/-- O² of the automorphism centralizer, as a subgroup of the ambient group. -/
def fixedResidual {G : Type*} [Group G] (a : MulAut G) : Subgroup G :=
  (pResidual 2 a.fixedSubgroup).map a.fixedSubgroup.subtype

/-- O²(C_P(a)), embedded first into P and then into the ambient group. -/
def parabolicFixedResidual {G : Type*} [Group G] (a : MulAut G) (P : Subgroup G) :
    Subgroup G :=
  ((pResidual 2 (a.fixedSubgroup.subgroupOf P)).map
    (a.fixedSubgroup.subgroupOf P).subtype).map P.subtype

/-- Containment of the entire centralizer gives equality in the ambient subgroup
lattice; no ambient normality of P or of C_P(a) is asserted. -/
theorem fixedResidual_eq_of_le {G : Type*} [Group G] [Finite G]
    (a : MulAut G) (P : Subgroup G) (h : a.fixedSubgroup ≤ P) :
    fixedResidual a = parabolicFixedResidual a P := by
  unfold parabolicFixedResidual
  rw [map_embedded_pResidual, map_subgroupOf_eq_of_le h]
  rfl

end Tits.InvolutionRootGeometry
