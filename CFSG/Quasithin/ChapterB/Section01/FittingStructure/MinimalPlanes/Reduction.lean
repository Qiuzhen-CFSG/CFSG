module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.Basic
public import CFSG.Quasithin.ChapterB.Section01.Restriction

/-!
# The actual fixed-space reduction for a minimal Fitting offender

For A in P*(G,V), put F_A=[F(G),A], H=F_A A, B=C_A(F_A), and
W=[C_V(B),F_A]. The definitions below retain these literal subgroups and
subspaces. `SourceReduction` is the intermediate contract for the coprime
and Thompson A × B argument. It does not assert that the contract holds.
In particular its kernel equality is inside H, and its two-core is that of
the faithful action image on W, rather than the core of the ambient G.

The separate assembly uses genuine restriction of minimal offenders to
eliminate B. Solvable FF structure then identifies a single natural plane.
Construction of `SourceReduction` from the original hypotheses remains an
upstream obligation; none of the plane cardinalities or dimensions are fields.

Source: Aschbacher–Smith, B.1.9 proof, first paragraph,
printed p.71 (PDF p.82), combined 1 March 2004 manuscript.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterB.FittingStructure.MinimalPlanes
open Subgroup Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The odd Fitting commutator in the original group. -/
def oddPart (A : Subgroup G) : Subgroup G := ⁅fittingSubgroup G, A⁆

/-- The original local overgroup F_A A. -/
def localGroup (A : Subgroup G) : Subgroup G := oddPart A ⊔ A

/-- The centralizer is relative to A. -/
def kernelActor (A : Subgroup G) : Subgroup G :=
  A ⊓ centralizer (oddPart A : Set G)

/-- The actor inside the local overgroup. -/
def localActor (A : Subgroup G) : Subgroup (localGroup A) :=
  A.subgroupOf (localGroup A)

/-- Restriction of the original action to the local group. -/
def localRepresentation (ρ : Representation (ZMod 2) G V) (A : Subgroup G) :
    Representation (ZMod 2) (localGroup A) V := ρ.comp (localGroup A).subtype

/-- The source test space, before proving that B is trivial. -/
noncomputable def testSpace (ρ : Representation (ZMod 2) G V) (A : Subgroup G) :
    Submodule (ZMod 2) V :=
  subspaceCommutator ρ (fixedSpace ρ (kernelActor A)) (oddPart A)

/-- The faithful image is formed from the local action, not from all of G. -/
noncomputable abbrev testImage (ρ : Representation (ZMod 2) G V) (A : Subgroup G) :=
  subspaceActionImage (localRepresentation ρ A) (testSpace ρ A)

/-- The elementary source reduction needed before applying B.1.8. Each field
must be established from the original Fitting and faithful-action hypotheses. -/
structure SourceReduction (ρ : Representation (ZMod 2) G V) (A : Subgroup G) : Prop where
  stable : (⊤ : Subgroup (localGroup A)) ≤
    subspaceStabilizer (localRepresentation ρ A) (testSpace ρ A)
  moving : subspaceCommutator (localRepresentation ρ A) (testSpace ρ A)
    (localActor A) ≠ ⊥
  fixed : testSpace ρ A ≤ fixedSpace ρ (kernelActor A)
  self_moved : subspaceCommutator ρ (testSpace ρ A) (oddPart A) = testSpace ρ A
  image_solvable : Group.IsSolvable (testImage ρ A)
  image_core : pCore 2 (testImage ρ A) = ⊥
  image_generated : normalClosure
    (restrictedSubgroup (localRepresentation ρ A) (testSpace ρ A) (localActor A) :
      Set (testImage ρ A)) = ⊤
  kernel : subspaceKernel (localRepresentation ρ A) (testSpace ρ A) ⊤ =
    (kernelActor A).subgroupOf (localGroup A)
  odd : Odd (Nat.card (oddPart A))

end CFSG.Quasithin.ChapterB.FittingStructure.MinimalPlanes
