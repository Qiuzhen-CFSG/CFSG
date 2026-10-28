module

public import Theory.Representation.BinaryHyperplane
public import Theory.Representation.SimpleCopies
public import Theory.Representation.BinaryOffender.Homogeneous.Existence
public import CFSG.Quasithin.ChapterA.Section01.Representations.Centralizer
public import CFSG.Quasithin.ChapterA.Section01.Representations.Dihedral
public import Mathlib.GroupTheory.Sylow

/-!
# Binary representations in §A.1

Definition A.1.40 uses invariant subspaces, the literal quotient I/C_I(X),
and the full homogeneous component in the image of the orbit span in
V/C_V(X). The source works with a finite group and X = O²(X); the definitions
make sense without these additional restrictions.

A.1.41 embeds the linear centralizer into the unit group of the actual
finite endomorphism field. A.1.42 selects an inertia-fixed simple copy in the
literal central quotient, lifts it by commutators inside the original orbit
span, and proves the inertia criterion and independent nonisomorphic orbit
decomposition. A.1.43 is the binary hyperplane argument; A.1.44 gives the
fixed and moved direct sums for the actual dihedral generators.

The source wrappers retain the residual, Sylow, action-image two-core and
faithfulness hypotheses. The reusable proofs sometimes need fewer assumptions.
Containment J ≤ I_T presents a submodule of I_T as a subspace of V; all
central images and orbit spans are formed using the original quotient map.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, printed pp.31–32 (PDF pp.42–43).
-/

@[expose] public section

open Representation Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterA
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A.1.40: the irreducible X-submodules of V. -/
def Irr (X : Subgroup G) : Set (Submodule (ZMod 2) V) :=
  {I | ∃ hI : X ≤ subspaceStabilizer ρ I,
    IsIrreducible (invariantSubspace ρ X I hI).toRepresentation}

/-- A.1.40: I = [I,X] and the actual quotient I/C_I(X) is irreducible. -/
def IrrPlus (X : Subgroup G) : Set (Submodule (ZMod 2) V) :=
  {I | IsIrrPlus ρ X I}

/-- A.1.40: the central image is its full X-homogeneous component in the
image of the Y-orbit span, with Y ≤ N_G(X). -/
def IrrPlusWith (X Y : Subgroup G) : Set (Submodule (ZMod 2) V) :=
  {I | Homogeneous.IsIrrPlusWith ρ X Y I}

/-- A.1.42, all three clauses: the type-inertia criterion on the original I,
a homogeneous Irr⁺ member inside I_T, and the direct-sum decomposition into
pairwise nonisomorphic distinct right-conjugate central images. The last
clause is stated for every homogeneous member of I_T. -/
theorem lemma_A_1_42 [Finite G] [FiniteDimensional (ZMod 2) V]
    (X : Subgroup G) (_hX : pResidual 2 X = ⊤)
    (T : Sylow 2 (Subgroup.normalizer (X : Set G)))
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ X I) :
    let P : Subgroup G := T.toSubgroup.map (Subgroup.normalizer (X : Set G)).subtype
    let hP : P ≤ Subgroup.normalizer (X : Set G) := by
      dsimp only [P]
      exact Subgroup.map_subtype_le T.toSubgroup
    let S := quotientImage ρ X I hI.choose
    ((∀ t ∈ centralInertia ρ X P hP S, (t : G) ∈ subspaceStabilizer ρ I) ↔
      I ∈ IrrPlusWith ρ X P) ∧
    (∃ J : Submodule (ZMod 2) V, J ≤ orbitSpan ρ P I ∧ J ∈ IrrPlusWith ρ X P) ∧
    (∀ (J : Submodule (ZMod 2) V), J ≤ orbitSpan ρ P I →
      ∀ hJ : Homogeneous.IsIrrPlusWith ρ X P J,
        let Ω := centralOrbit ρ X P hP (quotientImage ρ X J hJ.invariant)
        iSupIndep (fun A : Ω => A.val.toSubmodule) ∧
        (⨆ A : Ω, A.val.toSubmodule) = (orbitSpan ρ P J).map (fixedSpace ρ X).mkQ ∧
        ∀ A B : Ω, A ≠ B → ¬ SameModule A.val B.val) := by
  dsimp only
  refine ⟨inertia_stabilizes_iff_isIrrPlusWith ρ (Subgroup.map_subtype_le T.toSubgroup) hI,
    exists_isIrrPlusWith_le_orbitSpan ρ (Subgroup.map_subtype_le T.toSubgroup)
      (T.isPGroup'.map (Subgroup.normalizer (X : Set G)).subtype) hI, ?_⟩
  intro J _ hJ
  exact hJ.orbit_decomposition ρ

/-- A.1.43: any hyperplane meets an invariant set with more than one point
in an irreducible binary module. -/
theorem lemma_A_1_43 [Finite G] [FiniteDimensional (ZMod 2) V] [IsIrreducible ρ]
    (S : Set V) (hS : ∀ g : G, ∀ s ∈ S, ρ g s ∈ S) (hcard : 1 < Nat.card S)
    (W : Submodule (ZMod 2) V) (hW : Module.finrank (ZMod 2) (V ⧸ W) = 1) :
    ∃ s ∈ S, s ∈ W :=
  BinaryHyperplane.invariant_set_meets_hyperplane ρ S hS hcard W hW

end CFSG.Quasithin.ChapterA
