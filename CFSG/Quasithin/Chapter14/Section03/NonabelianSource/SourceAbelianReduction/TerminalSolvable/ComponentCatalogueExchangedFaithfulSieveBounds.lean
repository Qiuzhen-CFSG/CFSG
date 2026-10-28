module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulAction
public import Theory.GroupTheory.PrimeRankCentralCover

/-!
# The sharp exchanged degree bound on the same H

The literal stabilizer is elementary, acts faithfully, and has rank dim(I)−2.
Its conjugation action on the irreducibly acting normal H image is faithful,
so the degree is at most the automorphism two-rank of H plus two. Transport
along the actual orbit-image equivalence gives the identical bound before
quotienting. No movement of the originally selected component is required.

These are the numerical inputs to the Mathieu and binary-linear row exclusions
in the exchanged-image sieve. Source: Aschbacher--Smith G.11.6, printed p.366.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace ExchangedFaithfulSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedFaithfulSource T M Mc F g B v L I)

include s

/-- The original degree bounds the automorphism rank of the literal H image. -/
theorem image_degree_le_automorphism_rank_add_two :
    finrank (ZMod 2) I ≤ primeRank 2 (MulAut (s.image (componentOrbit L ⊤))) + 2 := by
  let : IsIrreducible (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype) :=
    s.image_irreducible
  have hr := s.image_setup.rank_le_automorphisms (L := s.image (componentOrbit L ⊤)) (by
    rw [normalizer_eq_top_iff.mpr s.image_normal]
    exact le_top)
  have hd := s.dimension_gt_two
  omega

/-- The faithful action quotient preserves the bound on the original orbit. -/
theorem orbit_degree_le_automorphism_rank_add_two :
    finrank (ZMod 2) I ≤ primeRank 2 (MulAut (componentOrbit L ⊤)) + 2 := by
  rw [primeRank_equiv 2 (MulAut.congr s.orbitEquiv)]
  exact s.image_degree_le_automorphism_rank_add_two

/-- Perfectness makes automorphism descent through the whole center faithful.
Thus the same sharp bound also applies to an actual central-quotient model. -/
theorem orbit_degree_le_central_quotient_automorphism_rank_add_two :
    finrank (ZMod 2) I ≤
      primeRank 2 (MulAut ((componentOrbit L ⊤) ⧸ center (componentOrbit L ⊤))) + 2 := by
  let : Group.IsPerfect (componentOrbit L ⊤) := s.component.orbit_isPerfect ⊤
  exact s.orbit_degree_le_automorphism_rank_add_two.trans
    (Nat.add_le_add_right (automorphism_primeRank_le_quotient_center 2) 2)

end ExchangedFaithfulSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
