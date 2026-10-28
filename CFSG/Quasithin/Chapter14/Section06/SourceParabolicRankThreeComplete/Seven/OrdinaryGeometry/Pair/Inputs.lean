module
public import CFSG.Quasithin.ChapterF.Section06.Basic
public import Theory.Representation.BinaryPermutation.SevenParabolic.Ordinary
public import Theory.GroupAction.FourPerfectOrbit

/-!
# Finite recognition contracts for the ordinary seven-letter pair

The subgroup problem retains both original cubic vertices and their ambient
homomorphism. It asks for simultaneous conjugacy, allowing interchange.
The separate module problem classifies a transitive binary plane and its
common fixed point once those subgroup images are labelled. Neither contract
asserts the source theorem; its assembly must supply both finite results.

`LocalData` records only the source inputs to this calculation: a genuine
Goldschmidt triple, a moved four-group, and its fixed central point.
Source: Aschbacher--Smith, original14.6.10(5), printed p.1029.
-/

@[expose] public section
open Subgroup BinaryPermutation.SevenParabolic
open BinaryPermutation.SevenParabolic.Ordinary
namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair
universe u

def CubicPairRecognition : Prop :=
  ∀ (K : Type u) [Group K] [Finite K] (A B : Subgroup K),
    ChapterF.IsGoldschmidtTriple A B →
    ∀ f : K →* Equiv.Perm (Fin 7), alternatingGroup (Fin 7) ≤ f.range →
    ∃ g : Equiv.Perm (Fin 7),
      let f' := (MulAut.conj g).toMonoidHom.comp f
      (A.map f' = f'.range ⊓ lambda ∧ B.map f' = f'.range ⊓ theta) ∨
      (A.map f' = f'.range ⊓ theta ∧ B.map f' = f'.range ⊓ lambda)

def TransitivePlane (A : Subgroup (Equiv.Perm (Fin 7)))
    (P : Submodule (ZMod 2) Space) : Prop :=
  (∀ a ∈ A, ∀ v ∈ P, action a v ∈ P) ∧
  ∀ v ∈ P, v ≠ 0 → ∀ w ∈ P, w ≠ 0 → ∃ a ∈ A, action a v = w

structure PlaneRecognition : Prop where
  lambda_plane : ∀ (J : Subgroup (Equiv.Perm (Fin 7)))
    (P : Submodule (ZMod 2) Space) (z : Space),
    alternatingGroup (Fin 7) ≤ J → Nat.card P = 4 →
    TransitivePlane (J ⊓ lambda) P → z ∈ P → z ≠ 0 →
    J ⊓ lambda ⊓ theta ≤ pointStabilizer z →
    P = Submodule.span (ZMod 2) {firstFour,secondFour} ∧ z = firstFour
  theta_point : ∀ (J : Subgroup (Equiv.Perm (Fin 7)))
    (P : Submodule (ZMod 2) Space) (z : Space),
    alternatingGroup (Fin 7) ≤ J → Nat.card P = 4 →
    TransitivePlane (J ⊓ theta) P → z ∈ P → z ≠ 0 →
    J ⊓ lambda ⊓ theta ≤ pointStabilizer z → z = pair56
  stabilizer : ∀ g : Equiv.Perm (Fin 7),
    (∀ v ∈ Submodule.span (ZMod 2) {firstFour,secondFour},
      action g v ∈ Submodule.span (ZMod 2) {firstFour,secondFour}) ↔ g ∈ lambda

variable {G : Type*} [Group G] [Finite G]

structure LocalData (J P Q V Z M Mc : Subgroup G) : Prop where
  first_le : P ≤ J
  second_le : Q ≤ J
  triple : ChapterF.IsGoldschmidtTriple (P.subgroupOf J) (Q.subgroupOf J)
  plane_card : Nat.card V = 4
  point_card : Nat.card Z = 2
  point_le : Z ≤ V
  first_le_M : P ≤ M
  normalizer_eq : M = normalizer (V : Set G)
  centralizer_eq : Mc = centralizer (Z : Set G)
  second_fixes : Q ≤ centralizer (Z : Set G)
  seed : ∃ R : Subgroup G, R ≤ P ∧ IsPPerfect 2 R ∧ ⁅V,R⁆ = V

end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair
