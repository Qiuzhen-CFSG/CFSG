module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.TernaryRankTwo
public import Theory.Representation.BinaryOffender.TwoPerfectPlane

/-!
# Fitting centralization from the original binary seed

A minimal offender in a normalized two-group would, if noncentral on the
Fitting subgroup, be an order-two Sylow subgroup of an actual B.1.9 factor.
Three-rank at most two makes that factor invariant under the two-perfect
seed actor. Their intersection normalizes the offender, contradicting its
nonzero displacement in the nontrivial invariant binary seed plane.

This is the representation argument of Aschbacher–Smith13.7.14, p.943.
The Chapter13 consumer supplies the literal quotient and seed geometry.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

theorem minimal_offender_centralizes_fitting_of_seed_plane
    (hρ : Function.Injective ρ) (hcore : pCore 2 G = ⊥) (hrank : primeRank 3 G ≤ 2)
    {K B R : Subgroup G} (hK : IsPPerfect 2 K)
    (hR : IsPGroup 2 R) (hKR : K ≤ normalizer (R : Set G))
    (P : Submodule (ZMod 2) V) (hP : K ≤ subspaceStabilizer ρ P)
    (hd : Module.finrank (ZMod 2) P = 2) (hn : ¬ P ≤ fixedSpace ρ K)
    (hB : IsMinimalBestOffender ρ B) (hBR : B ≤ R)
    (hmove : subspaceCommutator ρ ⊤ B ≤ P) :
    B ≤ centralizer (fittingSubgroup G : Set G) := by
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  by_contra hnot
  have hlocal := localPlaneLaw ρ hρ hcore
  obtain ⟨d⟩ := hlocal B hB hnot
  exact not_normalized_order_two_offender_in_plane ρ hρ hK P hP hd hn
    (hB.1.isOffender ρ) d.actor_card hmove
    (twoPerfect_normalizes_minimal_offender ρ hρ hlocal hrank hK hB hnot hR hBR hKR)

end CFSG.Quasithin.ChapterB.FittingStructure
