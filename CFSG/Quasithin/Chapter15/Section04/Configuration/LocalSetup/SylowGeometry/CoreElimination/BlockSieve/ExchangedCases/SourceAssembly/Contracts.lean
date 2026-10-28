module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceExclusion
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2
public import Stellmacher.CentralizerQuotientRepresentation

/-!
# The complete universal C.2.7 input to the exchanged sieve

The star quotient is the literal local group LR modulo the centralizer of
Ω₁(Z(O₂(LR))). The contract retains clauses (1) and (2), the four χ-block
subcases, and every alternative (b)--(h). Borel and parabolic subgroups are
specified by Sylow normalizers; the permutation cases retain their actual
partitions and conjugation actions. The SL₃ case reuses the complete MS-pair
contract and its actual starred component and intersection.

This file defines an earlier-source implication, not a proof of C.2.7 or a
classification specialized to Chapter 15. The existing source owner is
qt-c-02-offender-cases. C.1.34 retains its separate full universal contract.
Source: Aschbacher--Smith, C.2.7(1)--(3), pp.145--147,
combined manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup Stellmacher Representation
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
open SL3Geometry.SourceCases
universe u

/-- A Borel in the source's characteristic-two Lie groups. -/
def IsBorel {A : Type*} [Group A] (B : Subgroup A) : Prop :=
  ∃ S : Sylow 2 A, normalizer (S : Set A) = B

/-- A maximal proper parabolic, retaining its Sylow-normalizer Borel. -/
def IsMaximalParabolic {A : Type*} [Group A] (P : Subgroup A) : Prop :=
  IsCoatom P ∧ ∃ S : Sylow 2 A, normalizer (S : Set A) ≤ P

/-- In L₄(2) and L₅(2), positive semisimple rank means a proper
parabolic strictly larger than its Borel. -/
def IsPositiveRankParabolic {A : Type*} [Group A] (P : Subgroup A) : Prop :=
  P ≠ ⊤ ∧ ∃ S : Sylow 2 A, normalizer (S : Set A) < P

/-- Literal setwise stabilization of a partition of the permutation domain. -/
def partitionStabilizer {n : ℕ} (partition : Set (Set (Fin n))) :
    Subgroup (Equiv.Perm (Fin n)) :=
  MulAction.stabilizer (Equiv.Perm (Fin n)) partition

/-- The actual partition sizes, not just the index of its stabilizer. -/
def HasPartitionType {n k : ℕ} (partition : Set (Set (Fin n))) (sizes : Fin k → ℕ) : Prop :=
  ∃ parts : Fin k → Set (Fin n), Set.range parts = partition ∧
    Pairwise (fun a b => Disjoint (parts a) (parts b)) ∧
    (⋃ a, parts a) = Set.univ ∧ ∀ a, Nat.card (parts a) = sizes a

variable {A : Type u} [Group A]

noncomputable def starProjection (L R : Subgroup A) : localGroup L R →* Star L R :=
  QuotientGroup.mk' (starKernel L R)
noncomputable def starRadical (L R : Subgroup A) : Subgroup (Star L R) :=
  (R.subgroupOf (L ⊔ R)).map (starProjection L R)
noncomputable def starThompson (L R : Subgroup A) : Subgroup (Star L R) :=
  (elementaryAbelianMaxJ (R.subgroupOf (L ⊔ R))).map (starProjection L R)
noncomputable def starIntersectionIn (L R M : Subgroup A) : Subgroup (starComponent L R) :=
  (starIntersection L R M).subgroupOf (starComponent L R)

/-- The faithful action on the actual local omega module. -/
noncomputable def starRepresentation (L R : Subgroup A) :
    Representation (ZMod 2) (Star L R) (Additive (omegaCoreModule (localGroup L R))) :=
  NormalElementaryQuotient.representation _ (starProjection L R)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

/-- C.2.7(1), including genuine two-reducedness of the actual omega module. -/
def CoreConclusion (L R : Subgroup A) : Prop :=
  pCore 2 (localGroup L R) ≤ starKernel L R ∧
  starKernel L R ≤ pCore 2 (localGroup L R) ⊔
    (centralPreimage (pCore 2 L)).map
      (inclusion (show L ≤ L ⊔ R from le_sup_left)) ∧
  IsElementaryAbelian 2 (omegaCoreModule (localGroup L R)) ∧
  pCore 2 (Star L R) = ⊥

/-- C.2.7(2), with FF and FF-star offenders for the faithful star action. -/
def OffenderConclusion (L R : Subgroup A) : Prop :=
  ¬ elementaryAbelianMaxJ (R.subgroupOf (L ⊔ R)) ≤
    elementaryAbelianMaxJ (pCore 2 (localGroup L R)) ∧
  BinaryOffender.IsFFModule (starRepresentation L R) ∧
  ∃ B : Subgroup (Star L R), B ≤ starRadical L R ∧
    BinaryOffender.IsBestOffender (starRepresentation L R) B

/-- The A-hat₆ clause retains the actual 3-dimensional F₄ realization of U(L)
and its 2-space stabilizer. Conjugation on U(L) is the specified linear action. -/
def AhatPlaneStabilizer (L M : Subgroup A) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    ∃ c : ChapterC.blockU L ≃* Multiplicative (Fin 3 → F),
      ∃ W : Submodule F (Fin 3 → F), Module.finrank F W = 2 ∧
      (∀ l : L, ∃ e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F),
        ∀ v : ChapterC.blockU L,
          (c (MulAut.conjNormal l v)).toAdd = e (c v).toAdd) ∧
      ∀ l : L, (l : A) ∈ M ↔
        ∀ v : ChapterC.blockU L, (c v).toAdd ∈ W ↔
          (c (MulAut.conjNormal l v)).toAdd ∈ W

/-- The complete four subcases in C.2.7(3)(a). -/
inductive ChiCases (L R M : Subgroup A) : Prop
  | rankOne (n : ℕ) (block : ChapterC.IsL2EvenBlock L n)
      (sylow : Chapter1.IsSylowIn 2 (starThompson L R) (starComponent L R))
      (borel : IsBorel (starIntersectionIn L R M))
  | alternatingFive (block : ChapterC.IsAlternatingBlock L 5)
      (sylow : ∃ S : Sylow 2 (localGroup L R), (S : Subgroup _) = R.subgroupOf (L ⊔ R))
      (model : Nonempty (Star L R ≃* Equiv.Perm (Fin 5)))
      (borel : IsBorel (starIntersectionIn L R M))
  | alternatingSevenDihedral (block : ChapterC.IsAlternatingBlock L 7)
      (radical : Nonempty (starRadical L R ≃* DihedralGroup 4))
      (model : ∃ e : Star L R ≃* Equiv.Perm (Fin 7),
        ∃ P : Set (Set (Fin 7)), HasPartitionType P (![4,3] : Fin 2 → ℕ) ∧
          (starIntersection L R M).map e.toMonoidHom =
            alternatingGroup (Fin 7) ⊓ partitionStabilizer P)
  | alternatingSevenElementary (block : ChapterC.IsAlternatingBlock L 7)
      (radical : IsElementaryAbelian 2 (starRadical L R))
      (order : Nat.card (starRadical L R) = 8)
      (model : ∃ e : Star L R ≃* Equiv.Perm (Fin 7),
        ∃ P : Set (Set (Fin 7)), HasPartitionType P (![2,2,2,1] : Fin 4 → ℕ) ∧
          (starIntersection L R M).map e.toMonoidHom =
            alternatingGroup (Fin 7) ⊓ partitionStabilizer P)

/-- The exact transposition assertion in C.2.7(3)(b), with both the
component and the actor represented in the same symmetric group. -/
def TranspositionCase (L R M : Subgroup A) (n : ℕ) : Prop :=
  ∃ e : Star L R ≃* Equiv.Perm (Fin n),
    (starComponent L R).map e.toMonoidHom = alternatingGroup (Fin n) ∧
    ∃ a b : Fin n, a ≠ b ∧
      (starRadical L R).map e.toMonoidHom = zpowers (Equiv.swap a b) ∧
      starIntersection L R M = starComponent L R ⊓ centralizer (starRadical L R : Set (Star L R))

/-- All eight alternatives of C.2.7(3), uniformly before any source
configuration or swapped model is supplied. -/
inductive Alternatives (κ : GroupClass.{u}) (L R M : Subgroup A) : Prop
  | chi (block : ChapterC.IsChiBlock L) (cases : ChiCases L R M)
  | alternating (n : ℕ) (lower : 5 ≤ n) (upper : n ≤ 8)
      (block : ChapterC.IsAlternatingBlock L n) (action : TranspositionCase L R M n)
  | ahatSix (block : ChapterC.IsExceptionalAhat6Block L)
      (index : (M ⊓ L).relIndex L = 15) (stabilizer : AhatPlaneStabilizer L M)
  | exceptionalSeven (block : ChapterC.IsExceptionalA7Block L)
      (index : (M ⊓ L).relIndex L = 35)
  | symplectic (block : ChapterC.IsAlternatingBlock L 6 ∨ ChapterC.IsSp4FourBlock L)
      (parabolic : IsMaximalParabolic (starIntersectionIn L R M))
  | gTwo (block : ChapterC.IsG2TwoBlock L)
      (model : ∃ e : Star L R ≃* Atlas.G2.Model (ZMod 2),
        G2MaximalParabolic ((starIntersection L R M ⊔ starRadical L R).map e.toMonoidHom))
  | linearThree (branch : SL3Branch κ L R M)
  | linearHigher (n : ℕ) (degree : n = 4 ∨ n = 5)
      (model : ClassicalGroup.IsPSL (starComponent L R) n 2)
      (parabolic : IsPositiveRankParabolic (starIntersectionIn L R M))

/-- The complete earlier theorem, with no specialized conclusion or radical
restriction smuggled into its premises. Its proof retains its Chapter C owner. -/
def UniversalC27 : Prop :=
  ∀ (κ : GroupClass.{u}) (A : Type u) [Group A] [Finite A] (R M L : Subgroup A),
    ComponentHypotheses κ A R M L →
      CoreConclusion L R ∧ OffenderConclusion L R ∧ Alternatives κ L R M

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
