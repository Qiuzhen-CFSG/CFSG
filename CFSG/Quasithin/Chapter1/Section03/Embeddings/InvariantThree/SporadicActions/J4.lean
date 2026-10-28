module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Covers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Contracts
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Reduction

/-!
# Conditional assembly of the J₄ Sylow-pair exclusion

Place each source pair in a local overgroup isomorphic to the specified
max4 subgroup, and lift the acting automorphisms to that overgroup. A proved
identification of its two-core quotient with S₅ × SL₃(2) then allows the
projection-kernel argument of `J4.Reduction`. A separate sufficient route
uses a common conjugate of max4 preserved by all extending automorphisms.

The quotient and invariant placement remain explicit prerequisites.
Consequently the unconditional `j4_carrierPairExclusion` is still open;
the theorem below is only the complete deduction from those inputs.
It uses neither an assumed J₄ order nor a conditional outer-group theorem.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
open J4Reduction

/-- The source action exclusion follows once both actual local inputs are proved. -/
theorem j4_carrierPairExclusion_of_maximalFour
    (hquot : MaximalFourQuotient) (hplace : MaximalFourPairPlacement) :
    CarrierPairExclusion ClassificationModels.SporadicName.j4.Carrier := by
  change CarrierPairExclusion Janko4.Model
  intro _ _ _ S R h
  obtain ⟨g, _, hR, hstable⟩ := hplace S R h
  obtain ⟨e⟩ := hquot
  apply pairReducible_of_map (MulAut.conj g)
  exact pairReducible_of_localQuotient
    (h.oddComplement.of_mulEquiv ((MulAut.conj g).subgroupMap R)) hR e hstable

private theorem invariant_of_equiv
    {G N : Type*} [Group G] [Finite G] [Group N] {R M : Subgroup G}
    (D : Subgroup (MulAut R)) (hR : XiOddQuotient 3 R) (hRM : R ≤ M)
    (f : M ≃* N)
    (e : (N ⧸ pCore 2 N) ≃* Janko4.LocalStructure.SymmetricLinear.QuotientModel)
    (ha : ∀ a ∈ D, ∃ c : MulAut M,
      ∀ r : R, inclusion hRM (a r) = c (inclusion hRM r)) :
    ∃ A : Subgroup (R ⧸ frattini R), A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ a ∈ D, ∀ x ∈ A, quotientAut (frattini R) a x ∈ A := by
  let eM := (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e
  exact invariantFrattiniSubgroup_of_localQuotient D hR hRM eM ha

/-- It suffices to place and lift each acting two-group separately. The
two-core quotient is transported along the actual local-group equivalence. -/
theorem j4_carrierPairExclusion_of_maximalFourActions
    (hquot : MaximalFourQuotient) (hactions : MaximalFourPairActions) :
    CarrierPairExclusion ClassificationModels.SporadicName.j4.Carrier := by
  change CarrierPairExclusion Janko4.Model
  intro _ _ _ S R h D hD htwo
  obtain ⟨M, hRM, _, ⟨f⟩, ha⟩ := hactions S R h D hD htwo
  obtain ⟨e⟩ := hquot
  exact invariant_of_equiv (N := Janko4.LocalStructure.SymmetricLinear.max4Subgroup)
    D h.oddComplement hRM f e ha

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
