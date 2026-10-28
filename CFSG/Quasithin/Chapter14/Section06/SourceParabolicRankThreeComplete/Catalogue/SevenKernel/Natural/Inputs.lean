module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.NaturalThompsonBaumann
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Natural.Seed

/-!
# Remaining relative transposition geometry

These are independent premises for the relative C.1.24 assembly. The first
identifies the actual Thompson image, allowing one, two or three disjoint
transpositions. The second is finite natural-module geometry for those three
literal permutation subgroups. Neither premise includes a block or a source
selection conclusion. `Natural.Source` owns their final discharge.

Source: Aschbacher--Smith B.3.2(4) and C.1.24(a), pp.84 and 131.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Natural
open ChapterB.Offenders BinaryPermutation
open Theory.SpecificGroups.SymmetricSeven.ThreePairsCubic
universe u

/-- The relative local Thompson image, without a Sylow assumption on R. -/
def RelativeThompsonInput : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (V R : Subgroup J)
    [V.Normal] [IsElementaryAbelian 2 V], IsPGroup 2 R → V ≤ R →
    ∀ (q : J →* Sym) (hq : Function.Surjective q)
      (hk : q.ker = centralizer (V : Set J)),
    (∀ A, fixedCodim (NormalElementaryQuotient.representation V q hq hk) A =
      fixedCodim (naturalRepresentation (Fin 7)) A) →
    ¬elementaryAbelianMaxJ R ≤ q.ker →
    ∃ (a : Sym) (k : ℕ), 1 ≤ k ∧ k ≤ 3 ∧
      (elementaryAbelianMaxJ R).map q =
        (disjointTranspositions 7 k).map (MulAut.conj a).toMonoidHom

/-- Pointwise fixed-space stabilizers and cubic generation in all three rows. -/
def PairGeometryInput : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ 3 →
    (∀ g : Sym,
      (∀ v ∈ fixedSpace (naturalRepresentation (Fin 7)) (disjointTranspositions 7 k),
        naturalRepresentation (Fin 7) g v = v) → g ∈ disjointTranspositions 7 k) ∧
    normalizer (disjointTranspositions 7 k : Set Sym) ⊔ zpowers cubic = ⊤

end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Natural
