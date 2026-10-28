module

public import CFSG.Quasithin.ChapterD.Section01.Configuration
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupAction.NormalPChiefSeries
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.GroupTheory.PResidual.Defs
public import Stellmacher.ElementaryAbelianMaxDefs

/-!
# Universal D.1 inputs for the inside-core application

The five alternatives of D.1.5 use the faithful conjugation image on the
original embedded elementary subgroup. Chief factors are the actual intervals
of a chief series from 1 to the conjugate span, with centrality tested by
conjugation. All normality assertions are relative to the second group.

`EarlierD14Sylow` is precisely the solvable characteristic-two consequence
of D.1.4: its dual-FF alternative or R ∈ Syl₂(O²(G₂)R). The later A₃-block
assertion is not needed here. These definitions are universal source inputs,
not proofs of D.1.4 or D.1.5; their producers remain qt-d-01 and
qt-d-01-unique-factor. The consumer in `InsideCore` proves their application.
Nontriviality is explicit because the displayed D.1.1 admits V = 1.

Source: Aschbacher–Smith, D.1.1, D.1.4–5, printed pp.171–177, and the
inside-core branch of 15.4.2(4), printed p.1156, refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource.InsideCore
universe u
variable {G : Type u} [Group G]

/-- The faithful linear action of the actual conjugation image on V. -/
noncomputable def imageRepresentation (A V : Subgroup G)
    (hn : A ≤ normalizer (V : Set G)) [IsElementaryAbelian 2 V] :
    Representation (ZMod 2) (ChapterD.internalActionImage A V hn) (Additive V) where
  toFun a := a.val.toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by ext v; rfl
  map_mul' a b := by ext v; rfl

/-- One noncentral factor on U, in an actual H-chief series from 1 to U. -/
def HasUniqueNoncentralFactor (H U : Subgroup G) : Prop :=
  U ≤ H ∧ ∃ hn : (U.subgroupOf H).Normal,
    ∃ s : @NoncentralChiefRefinement.SeriesOn H _ (U.subgroupOf H) hn,
      s.noncentralCount = 1

/-- More than one noncentral factor in an actual H-chief series on U. -/
def HasMultipleNoncentralFactors (H U : Subgroup G) : Prop :=
  U ≤ H ∧ ∃ hn : (U.subgroupOf H).Normal,
    ∃ s : @NoncentralChiefRefinement.SeriesOn H _ (U.subgroupOf H) hn,
      1 < s.noncentralCount

/-- All five clauses of the genuine universal D.1.5 implication.
The fifth clause keeps O²(G₂) distinct from O₂(G₂), and uses the elementary
Thompson subgroup J, rather than the all-abelian Thompson subgroup. -/
def EarlierD15 : Prop :=
  ∀ (X : Type u) [Group X] (G₁ G₂ T V : Subgroup X)
    (d : ChapterD.QRCConfiguration G₁ G₂ T V), V ≠ ⊥ →
    letI := d.module_elementary
    let ρ := imageRepresentation G₁ V d.module_normalized
    let R := ChapterD.twoCoreIn G₁
    let R₂ := ChapterD.twoCoreIn G₂
    let U := ChapterD.conjugateSpan G₂ V
    let L := (pResidual 2 G₂).map G₂.subtype
    (¬ V ≤ R₂) ∨
    (quadraticRatio ρ ≤ 1 ∧ IsFFModule ρ) ∨
    IsFFModule ρ.dual ∨
    (quadraticRatio ρ ≤ 2 ∧ IsMulCommutative U ∧ HasMultipleNoncentralFactors G₂ U) ∨
    (G₂ ≤ normalizer (R ⊓ R₂ : Set X) ∧ IsElementaryAbelian 2 U ∧
      HasUniqueNoncentralFactor G₂ U ∧
      ⁅U, L⁆ ≤ (center R₂).map R₂.subtype ∧
      L = ⁅L, Stellmacher.elementaryAbelianMaxJ R⁆ ∧
      Stellmacher.elementaryAbelianMaxJ R = Stellmacher.elementaryAbelianMaxJ T)

/-- The genuine universal solvable characteristic-two Sylow implication
of D.1.4, retaining its dual-FF alternative. No local conclusion is assumed. -/
def EarlierD14Sylow : Prop :=
  ∀ (X : Type u) [Group X] (G₁ G₂ T V : Subgroup X)
    (d : ChapterD.QRCConfiguration G₁ G₂ T V), V ≠ ⊥ →
    V ≤ ChapterD.twoCoreIn G₂ →
    HasUniqueNoncentralFactor G₂ (ChapterD.conjugateSpan G₂ V) →
    Group.IsSolvable G₂ → generalizedFitting G₂ = pCore 2 G₂ →
    letI := d.module_elementary
    IsFFModule (imageRepresentation G₁ V d.module_normalized).dual ∨
    Chapter1.IsSylowIn 2 (ChapterD.twoCoreIn G₁)
      ((pResidual 2 G₂).map G₂.subtype ⊔ ChapterD.twoCoreIn G₁)

end CFSG.Quasithin.Chapter15.Section04.RatioSource.InsideCore
