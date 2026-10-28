module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.Transport
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.Coordinates
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.MiddleC2.Descent
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.MiddleC2.Numbering

/-!
# The middle C₂ marked-action transport interface

The middle adjacent pair in the F₄ numbering is `(1, 2)`.  Its first node is
the singleton E₆ node `2`, while its second node is the orbit consisting of
E₆ nodes `1` and `4`; the existing `pairNode` and `f4Simple` definitions carry
this orientation and the original signed parameter.

Once a faithful concrete model of the literal F₄ cover and its complementary
linear action is supplied, the generic transport construction specializes to
this pair.  The model and its two marked matrix comparisons are intentionally
explicit inputs: no F₄--folded-E₆ identification is asserted here.

Alternatively, the checked sparse lattice embedding in `MiddleC2.FiniteLattice`
descends the complementary action directly. `middleC2PairActionOfComparisons`
uses the two precise coordinate comparisons with the actual representations.
Those comparisons remain explicit; the unconditional middle action is still
the assembly obligation.

Sources: GLS3 §§2.2--2.6 (`refs/KGroup/GLS3/chapter2.tex`) and
Aschbacher--Smith A.2.17, printed p.39 (`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation

open WordDescent

variable (F : Type*) [Field F]

/-- Direct descent through the checked integral embedding. The remaining inputs
identify both finite tables with their literal root-indexed representations. -/
def middleC2PairActionOfComparisons
    (S : MiddleC2.SourceComparison F) (C : MiddleC2.ComplementComparison F)
    (htwo : (2 : F) ≠ 0) : PairAction F 1 2 :=
  MiddleC2.actionOfComparisons F S C htwo

@[simp] theorem middleC2PairActionOfComparisons_map_generator
    (S : MiddleC2.SourceComparison F) (C : MiddleC2.ComplementComparison F)
    (htwo : (2 : F) ≠ 0) (s k : Bool) (t : F) :
    (middleC2PairActionOfComparisons F S C htwo).hom (pairGenerator F 1 2 s k t) =
      eigenspaceAction F (-1) (f4Simple F s (pairNode 1 2 k) t) :=
  MiddleC2.actionOfComparisons_map_generator F S C htwo s k t

/- The direct faithful-model specialization keeps the exact local subgroup,
   both signs, both Boolean node choices, and the original parameter. -/
def middleC2PairActionOfFaithfulModel
    {G : Type*} [Group G]
    (ι : G →* Cover F) (hι : Function.Injective ι)
    (x : Bool → Bool → F → G)
    (hx : ∀ s k t, ι (x s k t) = coverSimple F s (pairNode 1 2 k) t)
    (σ : G →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hσ : ∀ s k t,
      σ (x s k t) =
        eigenspaceAction F (-1) (f4Simple F s (pairNode 1 2 k) t)) :
    PairAction F 1 2 :=
  pairActionOfFaithfulModel F 1 2 ι hι x hx σ hσ

@[simp] theorem middleC2PairActionOfFaithfulModel_map_generator
    {G : Type*} [Group G]
    (ι : G →* Cover F) (hι : Function.Injective ι)
    (x : Bool → Bool → F → G)
    (hx : ∀ s k t, ι (x s k t) = coverSimple F s (pairNode 1 2 k) t)
    (σ : G →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hσ : ∀ s k t,
      σ (x s k t) =
        eigenspaceAction F (-1) (f4Simple F s (pairNode 1 2 k) t))
    (s k : Bool) (t : F) :
    (middleC2PairActionOfFaithfulModel F ι hι x hx σ hσ).hom
        (pairGenerator F 1 2 s k t) =
      eigenspaceAction F (-1) (f4Simple F s (pairNode 1 2 k) t) :=
  (middleC2PairActionOfFaithfulModel F ι hι x hx σ hσ).map_generator s k t

/- The column criterion is the characteristic-three-safe form of the same
   specialization.  `linearEquiv_eq_eigenspaceAction` supplies the marked
   equality without an irreducibility assumption. -/
def middleC2PairActionOfFaithfulModelOnColumns
    {G : Type*} [Group G]
    (ι : G →* Cover F) (hι : Function.Injective ι)
    (x : Bool → Bool → F → G)
    (hx : ∀ s k t, ι (x s k t) = coverSimple F s (pairNode 1 2 k) t)
    (htwo : (2 : F) ≠ 0)
    (σ : G →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hσ : ∀ (s k : Bool) (t : F) (c r : Index),
      (σ (x s k t) (antiVector F c) : Space F) r =
        foldedMatrix F (f4Simple F s (pairNode 1 2 k) t) r c -
          foldedMatrix F (f4Simple F s (pairNode 1 2 k) t) r
            (Theory.AlgebraicGroup.StandardRootSystem.typeE6PinnedIndexEquiv c)) :
    PairAction F 1 2 :=
  pairActionOfFaithfulModelOnColumns F 1 2 ι hι x hx htwo σ hσ

@[simp] theorem middleC2PairActionOfFaithfulModelOnColumns_map_generator
    {G : Type*} [Group G]
    (ι : G →* Cover F) (hι : Function.Injective ι)
    (x : Bool → Bool → F → G)
    (hx : ∀ s k t, ι (x s k t) = coverSimple F s (pairNode 1 2 k) t)
    (htwo : (2 : F) ≠ 0)
    (σ : G →* (complementSpace F ≃ₗ[F] complementSpace F))
    (hσ : ∀ (s k : Bool) (t : F) (c r : Index),
      (σ (x s k t) (antiVector F c) : Space F) r =
        foldedMatrix F (f4Simple F s (pairNode 1 2 k) t) r c -
          foldedMatrix F (f4Simple F s (pairNode 1 2 k) t) r
            (Theory.AlgebraicGroup.StandardRootSystem.typeE6PinnedIndexEquiv c))
    (s k : Bool) (t : F) :
    (middleC2PairActionOfFaithfulModelOnColumns F ι hι x hx htwo σ hσ).hom
        (pairGenerator F 1 2 s k t) =
      eigenspaceAction F (-1) (f4Simple F s (pairNode 1 2 k) t) :=
  (middleC2PairActionOfFaithfulModelOnColumns F ι hι x hx htwo σ hσ).map_generator s k t

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
