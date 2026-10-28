module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.Setup
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.FourObstruction
public import Theory.SpecificGroups.PSL2.CentralizerNonsquare

/-!
# The independent nonsquareness branch of the exceptional linear case

For `L = residualGenerated M z t ≃ PSL₂(8)` and `J = C_G(L)` of order two,
Proposition 13.1 identifies the distinguished centralizer closure of every
involution in the two-point stabilizer with `L`. Since `J ≤ D`, this applies
to the nonidentity element `u ∈ J`. Conjugation invariance of `Z` then gives
`C_G(u) ≤ N_G(L)`, and the actual matrix automorphism calculation excludes
all square roots of `u`.

The Proposition 13.1 conclusion remains an explicit premise below. This
module proves its application to the literal `L`, `D`, and `J` of the setup;
it does not yet discharge that earlier local analysis from the original
minimal-counterexample hypotheses. Neither an exceptional quotient nor an
equality between the closure of `J` and the two-core is used.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Proposition 13.1, Lemma 15.2(c),
and the final paragraph of Lemma 15.7. The proof uses no assertion about
the two-residual of `C_G(u)`, and does not assume that `u ∈ Z`.
-/

namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1

/-- The distinguished closure inside `C_G(u)` is normalized by `C_G(u)`.
Only conjugation invariance of the distinguished set is used. -/
public theorem centralizer_le_normalizer_centralizerClosure
    {G : Type*} [Group G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (u : G) :
    centralizer ({u} : Set G) ≤ normalizer (centralizerClosure Z u : Set G) := by
  apply le_normalizer_closure_iff.mpr
  intro x hx z hz
  apply Subgroup.subset_closure
  refine ⟨h.invariant x z hz.1, ?_⟩
  exact (centralizer ({u} : Set G)).mul_mem
    ((centralizer ({u} : Set G)).mul_mem hx hz.2)
    ((centralizer ({u} : Set G)).inv_mem hx)

/-- The nonsquareness conclusion of source Lemma 15.7 from the earlier
centralizer-closure conclusion of Proposition 13.1. The latter is kept explicit
until the original local analysis supplies it; no quotient from the equality
case of Lemma 15.7 and no fusion of `u` into `Z` is assumed. -/
public theorem linear_centralizer_nonsquare_of_centralizerClosure
    {G : Type*} [Group G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) {z t : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup 3)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hclosure : ∀ u : G, u ∈ residualPairStabilizer M t → IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t) :
    ∀ u : G, u ∈ centralizer (residualGenerated M z t : Set G) → u ≠ 1 →
      ∀ x : G, x ^ 2 ≠ u := by
  intro u hu hne
  have hu2 : u ^ 2 = 1 := by
    have hh := pow_card_eq_one'
      (x := (⟨u, hu⟩ : centralizer (residualGenerated M z t : Set G)))
    rw [hJ] at hh
    exact congrArg Subtype.val hh
  have heq := hclosure u (centralizer_residualGenerated_le_pair h hz hzM hu) ⟨hne, hu2⟩
  apply Theory.PSL2.nonsquare_of_card_two_centralizer (residualGenerated M z t) e hJ hu hne
  rw [← heq]
  exact centralizer_le_normalizer_centralizerClosure h u

end BenderSuzuki.ZD
