module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PlaneClosure
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.Normalizers
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.CoreMovement
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointJoin
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointOrder
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.MatchingBinary
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.MixedBinary
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.MixedKernel
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.Movement
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.QuadraticBound
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.SevenCore
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointModels
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointCentralizer
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointMultiplicity
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointBound
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointControl
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PlaneReduction
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PlaneResidual
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.FivePlane

/-!
# Local-control assembly for the natural branch of 12.9

PointCentralizer and PointMultiplicity construct the original escaping
minimal parabolic and its faithful multiplicity action, preserving the
F.9 actor, literal quotient and exact O₂(L₁) kernel. PointBound splits
the local quotient over the natural factor and shows that the original
H₁ surjects onto its centralizer. This reduced image inherits minimal
parabolicity and the actual SQTK cover. B.6.9 excludes its strong offender,
proving the original point-quotient centralizer bound in both degrees.

PointControl then proves K₁T ∈ Hz. Containment in M would force K₁=L₁;
the small binary-linear outer-group theorem and point bound would imply
G₁ ≤ M, contrary to the original escape. PointModels applies F.9.18 and
the seven-core exclusion to this actual join, giving A₇, PSL₄(2), or
PSL₅(2). In degree five the nested-component comparison leaves PSL₅(2).

PointOrder, MatchingBinary and Movement prove that O₂(K₁) moves V₂ in
all three rows. PlaneClosure and CoreMovement then establish the actual
minimal-parabolic and rank assertions of 12.9.6. Normalizers reduces the
intermediate flag-normalizer bounds to C_G(V₂) ≤ M.

PlaneReduction proves that the quotient-action kernel fixes U/V₁ and lies
in O₂(G₁), giving G₁=K₁T. Its literal Y=C_{K₁T}(V₂)T is the original
point/plane intersection, proper in K₁T and of three-rank at most one.
Failure of the plane bound gives the actual escaping join YL₁ in Hz;
containment Y≤L₁T supplies the plane bound and LocalControl. The source
overgroup and module argument must still establish that containment.

PlaneResidual proves that the original I₂ normalizes the literal O²(Y),
without a model assumption on Y. If the plane bound fails, its V-span is
strictly between V₂ and U_H. The same module constructs the actual binary
quotient U_H/V₂ and proves that O²(Y) acts reducibly. The remaining source
overgroup and four-space argument must force irreducibility there.

FivePlane completes degree five: L₂T is a nonsolvable Sylow overgroup
inside Y, and the literal point quotient is GL₅(2). The binary flag lattice
and three-rank bound force Y=L₂T. This proves the plane-centralizer bound
and all LocalControl clauses on the original flag, retaining the actual
solvable residual L₂ and quotient maps.

The final consumer applies these results to the unchanged LocalControl
record on the original flag. The plane-centralizer bound remains open in
degree four; this source 12.9.7 obligation remains with
qt-d-1291-natural-source. LocalControlInput in both degrees is not yet proved.

Source: Aschbacher--Smith, 12.9.5--7, printed pp.860--862 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Application to the literal LocalControl consumed by the completed fusion
and terminal arguments. The plane-centralizer bound replaces the family of
flag-normalizer premises; the other inputs are exactly 12.9.5 and 12.9.6(1). -/
theorem localControl_of_plane_centralizer
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hcentral : pointQuotientCentralizer C ≤ normalizer (L : Set G))
    (hcover : C.K1 ⊔ (T : Subgroup G) ∈ F.Hz L (normalizer (L : Set G)))
    (hmodels : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
      ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2)
    (hmove : ⁅F.Vi 2, C.K1.pCoreIn 2⁆ ≠ ⊥)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) : LocalControl C :=
  ⟨hcentral, hcover, hmodels, hmove, flag_normalizers_of_plane_centralizer h earlier F hplane⟩

/-- Apply the genuine quadratic actor and complete model sieve to the original
local-control record. Only the source centralizer bounds and the preceding
K₁T membership remain; no model or plane-movement premise is required. -/
theorem localControl_of_centralizers_and_abelian_join
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hcentral : pointQuotientCentralizer C ≤ normalizer (L : Set G))
    (hjoin : C.K1 ⊔ (T : Subgroup G) ∈ F.Hz L (normalizer (L : Set G)))
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) : LocalControl C :=
  localControl_of_centralizers_and_models h hn earlier F C hcentral
    (point_models_of_abelian_join h hn earlier F hab C hjoin) hplane

/-- Apply the proved original point bound to the unchanged local-control
consumer. The source join membership and plane bound remain to be discharged. -/
theorem localControl_of_abelian_join_and_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hjoin : C.K1 ⊔ (T : Subgroup G) ∈ F.Hz L (normalizer (L : Set G)))
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) : LocalControl C :=
  localControl_of_centralizers_and_abelian_join h hn earlier F hab C
    (point_quotient_centralizer_le_normalizer h hn earlier F hab C) hjoin hplane

/-- All point-control and plane-movement premises are discharged on the
original flag. Only the source plane-centralizer bound remains explicit. -/
theorem localControl_of_abelian_and_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) : LocalControl C :=
  localControl_of_abelian_join_and_plane h hn earlier F hab C
    (point_join_mem_Hz_of_abelian h hn earlier F hab C) hplane

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
