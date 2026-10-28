module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Model
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Centralizers
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Parity.Corollary714

/-!
# Distinguished local recognition for Section 16

Corollary 7.13 is assembled for the actual distinguished local circle.
The solvable branch follows from Lemma 3.12. In the nonsolvable branch,
local induction and strong embedding remove the extra cyclic factor,
while the action theorem makes the odd core central. The recognized
Borel action and Frattini factorization give double transitivity and the
two-point factorization on the full orbit.

Source: GLS, Volume 4, Chapter 2, Corollaries 7.13–7.14. The full orbit is
intended in 7.13(b), as its proof shows; the punctured-orbit wording of the
printed statement cannot be used. The Frattini factor is `F ∩ M`.

Corollary 7.14 is re-exported from `Parity.Corollary714`. The distinguished
centralizer traces have size one in the solvable case and `2^n - 1`, with
`n ≥ 2`, in the nonsolvable case. Fusion and simplicity make their sizes
congruent modulo four, excluding mixed solvability. Both corollaries use
only the supplied minimal-counterexample, simple-reduction and residual-action
hypotheses; no model, counting or permutation-sign premise remains.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Corollary 7.13 for distinguished local circles, with the actual model,
Borel subgroup, perfect cover, and the full-orbit action conclusions. -/
public theorem localCircle_corollary713
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (F : Subgroup G) (hF : F ≠ ⊤) (hFM : ¬ F ≤ M)
    (hne : ∃ z ∈ Z, z ∈ F ∧ z ∈ M) :
    let C := localCircle Z F
    let A := localCircleIn Z F
    ¬ A ≤ M ∧
      ((Group.IsSolvable C ∧ ∃ z ∈ Z, IsInvolution z ∧ z ∈ F ∧ z ∈ M ∧
        (∀ w ∈ Z, w ∈ F → w ∈ M → w = z) ∧
        F ⊓ M = F ⊓ Subgroup.centralizer ({z} : Set G)) ∨
      (pPrimeCore 2 C = Subgroup.center C ∧ commutator C = ⊤ ∧
        IsSimpleBenderGroup (C ⧸ Subgroup.center C) ∧
        IsBorelSubgroup ((M.comap (localCircleHom Z F)).map
          (QuotientGroup.mk' (Subgroup.center C))) ∧
        IsTwoTransitiveOn A {beta : G ⧸ M | InOrbit F (QuotientGroup.mk 1) beta} ∧
        ∀ beta : G ⧸ M, InOrbit F (QuotientGroup.mk 1) beta →
          beta ≠ QuotientGroup.mk 1 →
          (F : Set G) = (A : Set G) * (F ⊓ M ⊓ MulAction.stabilizer G beta : Subgroup G))) := by
  classical
  refine ⟨localCircleIn_not_le h.disconnected F hFM hne, ?_⟩
  by_cases hsol : Group.IsSolvable (localCircle Z F)
  · left
    obtain ⟨z, hz, hzF, hzM, hu, hc⟩ :=
      localCircle_solvable_alternative h.disconnected r ha F hF hFM hne hsol
    exact ⟨hsol, z, hz, h.disconnected.involutions z hz, hzF, hzM, hu, hc⟩
  · right
    obtain ⟨hc, hp, hm, hb⟩ := localCircle_nonsolvable_structure h r ha F hF hFM hne hsol
    exact ⟨hc, hp, hm, hb, localCircle_twoTransitiveOn h r F hF hFM hne hsol,
      fun _ hbeta hnebase => localCircle_twoPoint_factorization h r F hF hFM hne hsol hbeta hnebase⟩

end BenderSuzuki.ZD
