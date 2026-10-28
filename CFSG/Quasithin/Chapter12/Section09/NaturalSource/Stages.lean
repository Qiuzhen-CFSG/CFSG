module

public import CFSG.Quasithin.Chapter12.Section09.SourceInputs
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.ChapterE.Section03.WeakClosure
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.CComponent.Basic

/-!
# Interfaces between the local and fusion arguments of Section 12.9

The component stage constructs the actual normal component of the point
normalizer, proves the other local components are the literal Lᵢ, and eliminates
the nonabelian point span. The next stage supplies the smaller component list,
its quotient-action centralizer, the nontrivial action of its two-core on the
plane, and the intermediate flag normalizer bounds. Fusion then supplies the
two weak-closure assertions and the Sylow hyperplane assertion of 12.9.9.
The final stage must construct the actual S₃ overgroup and moving conjugate.

These are specifications of independent conditional proof obligations. None
is an added hypothesis of the source theorem or an asserted classification.
The assembly owner must prove all four inputs for the full known-simple class.
The original chosen seed, relative normality, quotient maps, right conjugation,
and the exceptional solvable-residual convention for n=5 remain unchanged.

Source: Aschbacher--Smith, 12.9.3--9 and the proof of 12.9.1,
printed pp.858--864 of `refs/quasithin.pdf`.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
open Chapter1.Section02.LocalModels
universe u

/-- The three larger point quotients in 12.9.3(2), with actual model isomorphisms. -/
def LargePointModel (X : Type u) [Group X] : Prop :=
  ClassicalGroup.IsPSL X 5 2 ∨ Nonempty (X ≃* Sporadic.Mathieu.M24) ∨
    Nonempty (X ≃* Janko4.Model)

/-- The additional n=4 point quotients in 12.9.3(3). The hat denotes the
source's central three-cover. The final extension has kernel E₄₉ and quotient
SL₂(7); as in A.3.12, no splitting is imposed by slash notation. -/
def FourPointModel (X : Type u) [Group X] : Prop :=
  ClassicalGroup.IsPSL X 4 2 ∨ IsAlternating X 7 ∨ IsAlternatingCover X 7 ∨
    Nonempty (X ≃* Sporadic.Mathieu.M23) ∨
    Nonempty (X ≃* Sporadic.LeechRelated.HS.Carrier) ∨
    Nonempty (X ≃* Held.He) ∨ Nonempty (X ≃* Rudvalis.Model) ∨
    HasExtension X (ElementaryModel 7 2) (fun Y _ => IsSL Y 2 7)

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The actual components constructed in 12.9.3. For i>1 the component is
Lᵢ itself. There is no claim that K₁ is normal in the ambient simple group. -/
structure ComponentGeometry (F : InvariantFlag T V n) (L : Subgroup G) where
  K1 : Subgroup G
  point_le : K1 ≤ F.H
  contains : F.Li L 1 ≤ K1
  component : (K1.subgroupOf F.H).IsCComponent
  normal : (K1.subgroupOf F.H).Normal
  alternatives : K1 = F.Li L 1 ∨ LargePointModel (K1 ⧸ pCore 2 K1) ∨
    n = 4 ∧ FourPointModel (K1 ⧸ pCore 2 K1)
  other_components : ∀ i, (n = 5 ∧ 1 < i ∧ i < 5) ∨ (n = 4 ∧ i = 3) →
    ((F.Li L i).subgroupOf (F.Gi i)).IsCComponent ∧
      ((F.Li L i).subgroupOf (F.Gi i)).Normal

/-- Conjugation by the point normalizer on the literal quotient K₁/O₂(K₁). -/
def pointQuotientAction {F : InvariantFlag T V n} (C : ComponentGeometry F L) :
    F.H →* MulAut (C.K1 ⧸ pCore 2 C.K1) :=
  (quotientAut (pCore 2 C.K1)).comp
    (C.K1.normalizerMonoidHom.comp
      (inclusion ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal)))

/-- The ambient image of the kernel of the actual point quotient action. -/
def pointQuotientCentralizer {F : InvariantFlag T V n} (C : ComponentGeometry F L) :
    Subgroup G := (pointQuotientAction C).ker.map F.H.subtype

/-- The portion of 12.9.5--7 consumed by fusion and the S₃ construction.
The transvection-centralizer case and the new I₂ of 12.9.6 are intermediate
obligations of its producer, rather than additional assumptions here. -/
structure LocalControl {F : InvariantFlag T V n} (C : ComponentGeometry F L) : Prop where
  quotient_centralizer : pointQuotientCentralizer C ≤ normalizer (L : Set G)
  overgroup : C.K1 ⊔ (T : Subgroup G) ∈ F.Hz L (normalizer (L : Set G))
  models : IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7 ∨
    ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 4 2 ∨
    ClassicalGroup.IsPSL (C.K1 ⧸ pCore 2 C.K1) 5 2
  core_moves_plane : ⁅F.Vi 2, C.K1.pCoreIn 2⁆ ≠ ⊥
  normalizers : ∀ i, 1 < i → i < n →
    F.Gi i ≤ seedNormalizer (normalizer (L : Set G)) V

/-- Both clauses of 12.9.9, including the stated weak-closure normalizer bound. -/
structure FusionControl (T : Sylow 2 G) (L V : Subgroup G) : Prop where
  weakClosure_centralizes : ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤
    centralizer (V : Set G)
  weakClosure_normalizer :
    normalizer (ChapterE.indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
      normalizer (L : Set G)
  hyperplanes : SylowHyperplaneControl T L V

/-- The local-component and nonabelian-elimination obligation, 12.9.3--4. -/
def ComponentInput (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X) (n : ℕ),
    HigherRankHypothesis K T L V n → n = 4 ∨ n = 5 →
    PreferredDimension K T n → EarlierSetupResults K → NaturalReduction K 4 →
    ∀ F : InvariantFlag T V n, IsMulCommutative F.U ∧ Nonempty (ComponentGeometry F L)

/-- The 12.9.5--7 obligation conditional on the independently constructed
component and abelian span. It does not wait for that producer to elaborate. -/
def LocalControlInput (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X) (n : ℕ),
    HigherRankHypothesis K T L V n → n = 4 ∨ n = 5 →
    PreferredDimension K T n → EarlierSetupResults K →
    ∀ F : InvariantFlag T V n, IsMulCommutative F.U →
    ∀ C : ComponentGeometry F L, LocalControl C

/-- The 12.9.9 obligation conditional on the preceding local geometry. -/
def FusionInput (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X) (n : ℕ),
    HigherRankHypothesis K T L V n → n = 4 ∨ n = 5 → EarlierSetupResults K →
    ∀ F : InvariantFlag T V n, IsMulCommutative F.U →
    ∀ C : ComponentGeometry F L, LocalControl C → FusionControl T L V

/-- The remaining part of 12.9.9(1). `FusionConsequences` derives the
normalizer bound and the full Sylow hyperplane assertion from this input. -/
def WeakClosureInput (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X) (n : ℕ),
    HigherRankHypothesis K T L V n → n = 4 ∨ n = 5 → EarlierSetupResults K →
    ∀ F : InvariantFlag T V n, IsMulCommutative F.U →
    ∀ C : ComponentGeometry F L, LocalControl C →
      ChapterE.indexedWeakClosure V (T : Subgroup X) 0 ≤ centralizer (V : Set X)

/-- The last source construction, including an actual S₃ quotient and moving
conjugate. TerminalConfiguration is the output of this obligation. -/
def TerminalInput (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X) (n : ℕ),
    HigherRankHypothesis K T L V n → n = 4 ∨ n = 5 → EarlierSetupResults K →
    ∀ F : InvariantFlag T V n, IsMulCommutative F.U →
    ∀ C : ComponentGeometry F L, LocalControl C → FusionControl T L V →
      Nonempty (TerminalConfiguration F L)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
