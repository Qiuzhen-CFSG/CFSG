module

public import CFSG.Quasithin.Chapter14.Section03.CaseOneSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.ModuleCover
public import CFSG.Quasithin.ChapterF.Section07.Track

/-!
# Source data for 14.7.66–70

This is separate from the legacy `CriticalFusion.Setup.Input`. That older
conditional API assumes normalizer, fusion, rank and intersection conclusions;
its component, Sylow and maximal-local predicates do not express the source.
It is retained for compatibility and is not used here.

The original full-known-simple counterexample, natural L₃(2) action and flag
are retained. H, U, K, Q and R₁ are actual subgroup constructions. Star is
H → H/O₂(H), and the S₅ marking is an isomorphism of this quotient. The action
on U/V₁ is recorded before passing to the actor quotient. In particular no
identification O₂(K)=O₂(H), nor factorization of the whole module action
through S₅, is assumed. U₀ is defined as the preimage of the K-fixed space.

`Data` records 14.7.63. `ModuleSeparation` is the precise earlier 14.7.2(1)
implication used to place the original flag in the natural quotient, owned by
qt-14-07-solvable. `CriticalPath` retains the actual coset graph, geodesic,
critical vertex, and the rechoice in Notation 14.7.1. It contains no conclusion
of 14.7.67–70. Its construction and the earlier source implications remain
with qt-14-07 and its component/solvable producers.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.1–4, pp.1042–1043; 14.7.63–70, pp.1069–1075.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation
open Chapter12.Section08
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

/-- The two-residual of H, included in the original ambient group. -/
def K (F : InvariantFlag T V 3) : Subgroup G :=
  (pResidual 2 F.H).map F.H.subtype

/-- The two-core of LT. -/
def Q (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  (L ⊔ (T : Subgroup G)).pCoreIn 2

/-- The actual star map has domain H, not G. -/
def starMap (F : InvariantFlag T V 3) : F.H →* HStar F.H :=
  QuotientGroup.mk' (pCore 2 F.H)

/-- Images retain the inclusion in H. Containment in H is supplied at use sites. -/
def star (F : InvariantFlag T V 3) (A : Subgroup G) : Subgroup (HStar F.H) :=
  (A.subgroupOf F.H).map (starMap F)

/-- The original 14.3.1(1)/14.5.1 configuration and the precise 14.7.63 data. -/
structure Data (T : Sylow 2 G) (L V : Subgroup G) (F : InvariantFlag T V 3)
    (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] where
  counterexample : Counterexample T L
  natural : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3
  abelian : IsMulCommutative F.U
  z : G
  z_ne_one : z ≠ 1
  point : F.Vi 1 = zpowers z
  centralizer_eq : F.H = Subgroup.centralizer ({z} : Set G)
  unique_Hz : F.Hz L (normalizer (L : Set G)) = {F.H}
  residual_product : F.H = K F ⊔ (T : Subgroup G)
  component : ((K F).subgroupOf F.H).IsCComponent
  model : HStar F.H ≃* ChapterJ.S5
  action : Representation (ZMod 2) F.H W
  conjugationSection : BinaryConjugationSection F.H F.U (F.Vi 1) action
  naturalQuotient : ChapterJ.L2FourAction
  projection : action.IntertwiningMap
    (naturalQuotient.action.comp (model.toMonoidHom.comp (starMap F)))
  projection_onto : Function.Surjective projection
  fixed_kernel : projection.toLinearMap.ker =
    Representation.invariants (action.comp ((K F).subgroupOf F.H).subtype)
  indecomposable : ∀ A B : Submodule (ZMod 2) W,
    (∀ k : (K F).subgroupOf F.H, ∀ w ∈ A, action k w ∈ A) →
    (∀ k : (K F).subgroupOf F.H, ∀ w ∈ B, action k w ∈ B) →
    IsCompl A B → A = ⊥ ∨ B = ⊥

namespace Data
variable {F : InvariantFlag T V 3} {W : Type u}
  [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

/-- The S₅ coordinates of the original quotient map. -/
def qH : F.H →* ChapterJ.S5 := d.model.toMonoidHom.comp (starMap F)

/-- The literal fixed-space preimage, as an ambient subgroup. -/
def U₀ : Subgroup G :=
  (((Representation.invariants
    (d.action.comp ((K F).subgroupOf F.H).subtype)).toAddSubgroup.toSubgroup).comap
      d.conjugationSection.coordinates).map F.U.subtype

/-- Earlier 14.7.2(1), universally over proper H-submodules of this section.
This is not hyperplane fusion or a normalizer assertion. -/
def ModuleSeparation : Prop :=
  ∀ A : Submodule (ZMod 2) W,
    (∀ h : F.H, ∀ w ∈ A, d.action h w ∈ A) → A ≠ ⊤ →
    ∀ v : F.U, (v : G) ∈ V →
      ((d.conjugationSection.coordinates v).toAdd ∈ A ↔ (v : G) ∈ F.Vi 1)

end Data

/-- The actual generated group and its two coset families. -/
abbrev GeometryGroup (T : Sylow 2 G) (L : Subgroup G) (F : InvariantFlag T V 3) :=
  (L ⊔ (T : Subgroup G)) ⊔ F.H

def geometryFamily (F : InvariantFlag T V 3) : Bool → Subgroup (GeometryGroup T L F) :=
  ChapterF.Section07.Geometry.family (L ⊔ (T : Subgroup G)) F.H

/-- The geodesic and the H-rechoice of Notation 14.7.1. The integer b is
characterized by the actual ball kernels, not an unconstrained rank/distance tag. -/
structure CriticalPath (F : InvariantFlag T V 3) where
  b : ℕ
  radius : ∀ n, V.subgroupOf (GeometryGroup T L F) ≤
    Subgroup.CosetGeometry.RankTwo.ballKernel (geometryFamily (L := L) F)
      (Subgroup.CosetGeometry.RankTwo.base (geometryFamily (L := L) F) false) n ↔ n ≤ b
  gammaConjugator : GeometryGroup T L F
  path : (Subgroup.CosetGeometry.RankTwo.graph (geometryFamily (L := L) F)).Walk
    (Subgroup.CosetGeometry.RankTwo.base (geometryFamily (L := L) F) false)
    (gammaConjugator⁻¹ • Subgroup.CosetGeometry.RankTwo.base (geometryFamily (L := L) F) true)
  geodesic : path.length =
    (Subgroup.CosetGeometry.RankTwo.graph (geometryFamily (L := L) F)).dist
      (Subgroup.CosetGeometry.RankTwo.base (geometryFamily (L := L) F) false)
      (gammaConjugator⁻¹ • Subgroup.CosetGeometry.RankTwo.base (geometryFamily (L := L) F) true)
  length : path.length = b
  first : path.getVert 1 =
    Subgroup.CosetGeometry.RankTwo.base (geometryFamily (L := L) F) true
  critical : ¬ V.subgroupOf (GeometryGroup T L F) ≤
    Subgroup.CosetGeometry.RankTwo.ballKernel (geometryFamily (L := L) F)
      (gammaConjugator⁻¹ • Subgroup.CosetGeometry.RankTwo.base (geometryFamily (L := L) F) true) 1
  rechoice : F.H
  alignment : (Subgroup.inclusion (le_sup_right : F.H ≤ GeometryGroup T L F) rechoice)⁻¹ •
    path.getVert 2 = Subgroup.CosetGeometry.RankTwo.base (geometryFamily (L := L) F) false

namespace CriticalPath
variable {F : InvariantFlag T V 3} (c : CriticalPath (L := L) F)

/-- Right-conjugation convention, consistently for Uα and Zα. -/
def conjugator : G := (c.gammaConjugator : G) * (c.rechoice : G)
def Uα : Subgroup G := conjugate F.U c.conjugator
def Zα : Subgroup G := conjugate (F.Vi 1) c.conjugator
def Qα : Subgroup G := (conjugate F.H c.conjugator).pCoreIn 2

/-- The two earlier inputs used in 14.7.66, with a genuine relative Sylow.
The containment comes from Notation 14.7.1; the image equality is 14.7.4(4).
The Sylow fact precedes 14.7.65 and follows from 14.7.63 and 14.3.3(6). -/
structure EarlierImages : Prop where
  placement : c.Uα ≤ F.Ri L 1
  image_eq : star F (Q T L) = star F (F.Ri L 1)
  sylow : Chapter1.IsSylowIn 2 (star F (F.Ri L 1)) (star F (K F))

end CriticalPath
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
