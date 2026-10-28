module

public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.GraphPlacement
public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.GroupTheory.PResidual.Defs

/-!
# Original hypotheses of the exceptional binary unitary branch

The model is the literal graph extension of U₄(2), with its marked point,
plane and overlap maps. A faithful completion embeds in the ambient finite
group. The two normalizer equalities use the centers of the two-cores of the
ordinary parabolics, while the root element lies in the center of their
prime-to-two residual. The ambient residual condition is O²(M)=M.

These are precisely the applicable hypotheses of Aschbacher--Smith F.4.31,
printed pp.290--291. `Exceptional` expresses failure of F.4.37(4)(i) using
relative subgroups of the actual graph-involution centralizer. The definitions
assert no recognition result. The proved graph/root nonfusion is the existing
F.4.36 argument applied to these literal source maps.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.ChapterF.Section05.Source

open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open UnitaryTwo.GraphCentralizer

local notation "hn" => Nat.le_refl 1
local notation "P" => pointParabolic 1 hn
local notation "Q" => planeParabolic 1 hn
local notation "B" => Extension.overlap 1 hn

/-- Inclusion of the ordinary point parabolic in the marked graph extension. -/
def pointInclusion : P →* Extension.point 1 hn :=
  ((SemidirectProduct.inl : ProjectiveGroup 1 hn →* Extension.ProjectiveExtension 1 hn).comp
    (pointParabolic 1 hn).subtype).codRestrict _
      (fun x => (Extension.mem_point 1 hn _).mpr x.property)

/-- Inclusion of the ordinary plane parabolic in the marked graph extension. -/
def planeInclusion : Q →* Extension.plane 1 hn :=
  ((SemidirectProduct.inl : ProjectiveGroup 1 hn →* Extension.ProjectiveExtension 1 hn).comp
    (planeParabolic 1 hn).subtype).codRestrict _
      (fun x => (Extension.mem_plane 1 hn _).mpr x.property)

/-- The exact root condition Z(O^{2'}(G₁)) in F.4.31. -/
def rootSubgroup : Subgroup P :=
  (center (primeToResidual 2 P)).map (primeToResidual 2 P).subtype

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

def pointRootImage : Subgroup G :=
  (center (pCore 2 P)).map
    (((i.comp c.left).comp pointInclusion).comp (pCore 2 P).subtype)

def planeRootImage : Subgroup G :=
  (center (pCore 2 Q)).map
    (((i.comp c.right).comp planeInclusion).comp (pCore 2 Q).subtype)

/-- The image of the literal extended upper subgroup. It is not defined as
the two-core of the overlap, which would change the source subgroup. -/
def sylowImage : Subgroup G :=
  ((Extension.extendedUpper 1 hn).subgroupOf B).map (i.comp c.middle)

/-- The actual marked graph involution in the ambient group. -/
def graphElement : G := i (c.middle graphInvolution)

/-- Applicable clauses of original F.4.31 in the Aut(U₄(2)) case.
The ambient finiteness assumption accompanies the source theorems. -/
structure Hypotheses (z : P) : Prop where
  embedding_injective : Function.Injective i
  root_order : orderOf z = 2
  root_mem : z ∈ rootSubgroup
  point_normalizer : normalizer (pointRootImage c i : Set G) = (i.comp c.left).range
  plane_normalizer : normalizer (planeRootImage c i : Set G) = (i.comp c.right).range
  root_centralizer : centralizer ({i (c.left (pointInclusion z))} : Set G) ≤
    (i.comp c.left).range
  two_residual : pResidual 2 G = ⊤

/-- Failure of F.4.37(4)(i), with C_T(f) viewed inside C_M(f). -/
def Exceptional : Prop :=
  ¬ ∃ R : Sylow 2 (centralizer ({graphElement c i} : Set G)),
    (R : Subgroup (centralizer ({graphElement c i} : Set G))) =
      (sylowImage c i).subgroupOf (centralizer ({graphElement c i} : Set G))

/-- F.4.36 for the marked source involution, with all maps supplied by the
original completion. It applies in both the exceptional and ordinary cases. -/
theorem graph_not_conjugate_root (z : P) (h : Hypotheses c i z) :
    ¬ IsConj (graphElement c i) (i (c.left (pointInclusion z))) :=
  UnitaryTwo.GraphFusion.source_marked_graph_not_conjugate_root c i
    h.embedding_injective (pointInclusion z) h.root_centralizer

/-- The same source exclusion for every graph-class element of the marked
extended upper subgroup, without an assumed global model embedding. -/
theorem upper_graph_class_not_conjugate_root (z : P) (h : Hypotheses c i z)
    (f : B) (hfU : f.val ∈ Extension.extendedUpper 1 hn)
    (hf : IsConj (Extension.sigma 1 hn) f.val) :
    ¬ IsConj (i (c.middle f)) (i (c.left (pointInclusion z))) :=
  UnitaryTwo.GraphPlacement.source_graph_involution_not_conjugate_root c i
    h.embedding_injective (pointInclusion z) h.root_centralizer f hfU hf

end CFSG.Quasithin.ChapterF.Section05.Source
