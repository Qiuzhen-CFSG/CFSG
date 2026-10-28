module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.ExceptionalActions.Carriers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.ExceptionalActions.G2
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.ExceptionalActions.G2Placement
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.ExceptionalActions.Triality
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage

/-!
# Exceptional characteristic-two three-complement actions

For G₂(2^f), f ≥ 2, and genuine ³D₄(2^f), f ≥ 1, the Sylow pair supplies
proper-parabolic placement and then common Sylow/Borel/Cartan coordinates.
At triality field order two the actual full parabolics have three-rank at
most one, contradicting the complement's rank two. Above this endpoint,
inner–field (respectively inner–coefficient) coverage and the Borel kernel
give a uniform power of two on R and its literal Frattini quotient.
Every two-subgroup of the full pair automizer is therefore reducible.

Only the universal earlier multiplier implications `G2TwoCenter` and
`TrialityTwoCenter` remain named inputs, as authorized for this source step.
They concern all finite quasisimple covers and are independent of the pair
and its action. The pair's trivial two-core kills the resulting center.
All placement, automorphism coverage, inner-kernel and action premises are
discharged. No p > 3 classification conclusion is used at p = 3.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528),
with the earlier covering-group input of I.1.3, printed p.407.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.ExceptionalActions
universe u

/-- The universal earlier multiplier consequence for the even G₂ covers.
It has no Sylow pair or action hypothesis. -/
def G2TwoCenter : Prop :=
  ∀ (K : Type u) [Group K] [Finite K], IsQuasisimple K →
    ∀ f : ℕ, 2 ≤ f → ClassificationModels.IsG2At (K ⧸ center K) (2 ^ f) →
      IsPGroup 2 (center K)

/-- The universal earlier multiplier consequence for genuine even triality
covers, including the binary endpoint, independent of any Sylow pair. -/
def TrialityTwoCenter : Prop :=
  ∀ (K : Type u) [Group K] [Finite K], IsQuasisimple K →
    ∀ f : ℕ, 1 ≤ f → Triality.Standard.IsTrialityGroupAt (2 ^ f) (K ⧸ center K) →
      IsPGroup 2 (center K)

variable {Q : Type u} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}

/-- The G₂ source branch: every extending pair automorphism is one field
power on the actual complement. Placement and coverage are proved inputs. -/
theorem g2_pair_power (hcover : G2TwoCenter.{u}) (h : PairInput S R)
    {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassificationModels.IsG2At (Q ⧸ center Q) (2 ^ f)) :
    ∀ b ∈ pairAutomizer (S : Subgroup Q) R,
      ∃ k : ℕ, ∀ r : R, b r = r ^ (2 ^ k) := by
  have hZ := hcover Q h.quasisimple f hf hm
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := g2_model_of_two_center h hZ hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hq : 2 < Nat.card F := by
    rw [hcard]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) hf)
  obtain ⟨e', hS, hR⟩ := g2_placement h e hq
  exact g2_pair_power_of_equiv (S : Subgroup Q) R e' hS hR
    (Atlas.G2.LieAutomorphismExtensions.semilinearAction_surjective hq)

/-- The genuine binary triality branch is impossible by proper-parabolic
placement and the full parabolics' three-rank-at-most-one obstruction. -/
theorem triality_binary_impossible (hcover : TrialityTwoCenter.{u}) (h : PairInput S R)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (Q ⧸ center Q)) : False := by
  have hZ := hcover Q h.quasisimple 1 (by decide) (by simpa only [pow_one] using hm)
  obtain ⟨P, hq, ⟨e⟩⟩ := triality_model_of_two_center h hZ hm
  exact TrialityPlacement.not_pair_of_q_eq_two h P hq e

/-- The triality source branch: the full cubic coefficient action yields
one power of two on the actual complement. Simplicity and perfectness for
automorphism coverage are inherited from the original quasisimple cover. -/
theorem triality_pair_power (hcover : TrialityTwoCenter.{u}) (h : PairInput S R)
    {f : ℕ} (hf : 1 ≤ f)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ f) (Q ⧸ center Q)) :
    ∀ b ∈ pairAutomizer (S : Subgroup Q) R,
      ∃ k : ℕ, ∀ r : R, b r = r ^ (2 ^ k) := by
  by_cases hf1 : f = 1
  · exact (triality_binary_impossible hcover h
      (by simpa only [hf1, pow_one] using hm)).elim
  have hZ := hcover Q h.quasisimple f hf hm
  let : IsQuasisimple Q := h.quasisimple
  let : IsSimpleGroup (Q ⧸ center Q) := h.quasisimple.simple
  let : IsSimpleGroup Q := (equivCenterQuotient h hZ).isSimpleGroup
  obtain ⟨P, hq, ⟨e⟩⟩ := triality_model_of_two_center h hZ hm
  obtain ⟨e', hS, hR⟩ := TrialityPlacement.torus_coordinates h P f hf hq e
  exact triality_pair_power_of_equiv (S : Subgroup Q) R P f hf hq e' hS hR

omit [Finite Q] in
private theorem frattini_power_of_power (b : MulAut R) (k : ℕ)
    (hb : ∀ r : R, b r = r ^ (2 ^ k)) (v : R ⧸ frattini R) :
    quotientAut (frattini R) b v = v ^ (2 ^ k) := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (frattini R) v
  rw [quotientAut_apply_mk, hb, map_pow]

/-- The G₂ field-power identity on R/Φ(R), for the entire pair automizer. -/
theorem g2_frattini_power (hcover : G2TwoCenter.{u}) (h : PairInput S R)
    {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassificationModels.IsG2At (Q ⧸ center Q) (2 ^ f)) :
    ∀ b ∈ pairAutomizer (S : Subgroup Q) R, ∃ k : ℕ,
      ∀ v : R ⧸ frattini R, quotientAut (frattini R) b v = v ^ (2 ^ k) := by
  intro b hb
  obtain ⟨k, hk⟩ := g2_pair_power hcover h hf hm b hb
  exact ⟨k, frattini_power_of_power b k hk⟩

/-- The genuine triality coefficient-power identity on R/Φ(R), including
the inner kernel and every extending pair automorphism. -/
theorem triality_frattini_power (hcover : TrialityTwoCenter.{u}) (h : PairInput S R)
    {f : ℕ} (hf : 1 ≤ f)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ f) (Q ⧸ center Q)) :
    ∀ b ∈ pairAutomizer (S : Subgroup Q) R, ∃ k : ℕ,
      ∀ v : R ⧸ frattini R, quotientAut (frattini R) b v = v ^ (2 ^ k) := by
  intro b hb
  obtain ⟨k, hk⟩ := triality_pair_power hcover h hf hm b hb
  exact ⟨k, frattini_power_of_power b k hk⟩

/-- Exclude G₂(2^f), f ≥ 2, for every two-subgroup of the pair automizer.
The only earlier input is the universal multiplier consequence. -/
theorem g2_pairReducible (hcover : G2TwoCenter.{u}) (h : PairInput S R)
    {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassificationModels.IsG2At (Q ⧸ center Q) (2 ^ f)) :
    PairReducible (S : Subgroup Q) R := by
  apply pairReducible_of_quotient_powers _ _ h.oddComplement.not_isCyclic
  intro b hb v
  obtain ⟨k, hk⟩ := g2_frattini_power hcover h hf hm b hb
  rw [hk]
  exact pow_mem (mem_zpowers v) _

/-- Exclude genuine ³D₄(2^f), f ≥ 1, for every two-subgroup of the pair
automizer, with only the universal earlier multiplier consequence explicit. -/
theorem triality_pairReducible (hcover : TrialityTwoCenter.{u}) (h : PairInput S R)
    {f : ℕ} (hf : 1 ≤ f)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ f) (Q ⧸ center Q)) :
    PairReducible (S : Subgroup Q) R := by
  apply pairReducible_of_quotient_powers _ _ h.oddComplement.not_isCyclic
  intro b hb v
  obtain ⟨k, hk⟩ := triality_frattini_power hcover h hf hm b hb
  rw [hk]
  exact pow_mem (mem_zpowers v) _

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.ExceptionalActions
