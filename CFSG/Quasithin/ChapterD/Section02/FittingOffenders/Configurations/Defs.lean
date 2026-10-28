module

public import CFSG.Quasithin.ChapterD.Section02.Inheritance
public import Mathlib.GroupTheory.Perm.Basic

/-!
# The reduced D.2.14 configuration problem

The hypotheses are the elementary-core and fixed-space reductions on the
literal local group `PA` and its original binary module `[V,P]`. They do not
include any of the remaining classification conclusions. The output records
the actual multiplication and addition maps. In the two-factor case the
same factors must be diagonal under the group isomorphism and exchanged by
the given actor. These are specifications, not assertions of existence.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.2.14(3),(6),(7), printed pp.186--187.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
open Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The exact conditional input after the earlier D.2.14 reductions. -/
structure Reduced (ρ : Representation (ZMod 2) G V) (P A : Subgroup G)
    (s : ℕ) : Prop where
  faithful : Function.Injective ρ
  normal : P.Normal
  elementary : IsElementaryAbelian 3 P
  card_core : Nat.card P = 3 ^ s
  rank_cases : s = 2 ∨ s = 3
  card_actor : Nat.card A = 4
  starred : A ∈ QhatStar ρ
  generated : P ⊔ A = ⊤
  actor_faithful : A ⊓ Subgroup.centralizer (P : Set G) = ⊥
  common_centralizer : P ⊓ Subgroup.centralizer (A : Set G) = ⊥
  core_commutator : ⁅P, A⁆ = P
  moved : subspaceCommutator ρ ⊤ P = ⊤
  hyperplane_support : ∀ B : Subgroup G, B ≤ A → rank B = 1 →
    P ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ →
    Nat.card (P ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ (fixedSpace ρ B)
        (P ⊓ Subgroup.centralizer (B : Set G))) = 2

/-- An invariant central line, with centrality supplied by the elementary core. -/
def IsInvariantLine (P A Z : Subgroup G) : Prop :=
  Z ≤ P ∧ Nat.card Z = 3 ∧ A ≤ Subgroup.normalizer (Z : Set G)

/-- The first branch on printed p.187: an invariant line moves all of the
original four-dimensional module. -/
def FullSupport (ρ : Representation (ZMod 2) G V) (P A : Subgroup G) : Prop :=
  ∃ Z : Subgroup G, IsInvariantLine P A Z ∧
    subspaceCommutator ρ ⊤ Z = ⊤ ∧ Module.finrank (ZMod 2) V = 4

/-- The remaining branch, after excluding a proper four-dimensional support. -/
def SmallInvariantSupports (ρ : Representation (ZMod 2) G V)
    (P A : Subgroup G) : Prop :=
  ∀ Z : Subgroup G, IsInvariantLine P A Z →
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 2

/-- Literal support factors; the maps below use their canonical inclusions. -/
structure SupportFactors (ρ : Representation (ZMod 2) G V) (P : Subgroup G)
    (s : ℕ) where
  factor : Fin s → Subgroup P
  card_factor : ∀ i, Nat.card (factor i) = 3
  multiply_bijective : Function.Bijective
    (fun x : (i : Fin s) → factor i => (List.ofFn fun i => (x i : P)).prod)
  support_dim : ∀ i, Module.finrank (ZMod 2)
    (subspaceCommutator ρ ⊤ ((factor i).map P.subtype)) = 2
  add_bijective : Function.Bijective
    (fun v : (i : Fin s) → subspaceCommutator ρ ⊤ ((factor i).map P.subtype) =>
      ∑ i, (v i : V))

namespace SupportFactors
variable {ρ : Representation (ZMod 2) G V} {P A : Subgroup G} {s : ℕ}

/-- The original ambient subgroup, as opposed to its coordinates in the core. -/
def ambient (d : SupportFactors ρ P s) (i : Fin s) : Subgroup G :=
  (d.factor i).map P.subtype

/-- The inclusion of a marked factor in the original group. -/
def inclusion (d : SupportFactors ρ P s) (i : Fin s) : d.factor i →* G :=
  P.subtype.comp (d.factor i).subtype

/-- Both coordinate images have order three, and neither projection kills a
nonidentity element of a marked factor. -/
def IsDiagonal (d : SupportFactors ρ P s)
    (e : G ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) : Prop :=
  ∀ i, let f := e.toMonoidHom.comp (d.inclusion i)
    Function.Injective ((MonoidHom.fst _ _).comp f) ∧
    Function.Injective ((MonoidHom.snd _ _).comp f) ∧
    Nat.card ((MonoidHom.fst _ _).comp f).range = 3 ∧
    Nat.card ((MonoidHom.snd _ _).comp f).range = 3

/-- Transitivity uses conjugation by elements of the original actor. -/
def IsTransitive (d : SupportFactors ρ P s) (A : Subgroup G) : Prop :=
  ∀ i j, ∃ a : A,
    (d.ambient i).map (MulAut.conj (a : G)).toMonoidHom = d.ambient j

/-- The two source alternatives, including their marked action clauses. -/
def Alternatives (d : SupportFactors ρ P s) (A : Subgroup G) : Prop :=
  (s = 2 ∧ ∃ e : G ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)),
    d.IsDiagonal e ∧ d.IsTransitive A) ∨
  (s = 3 ∧ ∀ i, A ≤ Subgroup.normalizer (d.ambient i : Set G) ∧
    Module.finrank (ZMod 2)
      (subspaceCommutator ρ (subspaceCommutator ρ ⊤ (d.ambient i)) A) = 1)

end SupportFactors
end CFSG.Quasithin.ChapterD.FittingConfigurations
