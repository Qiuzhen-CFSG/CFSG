module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Parity
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Counts

/-!
# Simultaneous solvability of distinguished centralizer circles

For a centralizer escaping `M`, the solvable circle has distinguished trace
of size one, while the nonsolvable circle has trace of size `2^n - 1` for
some `n ≥ 2`. The conjugation parity theorem rules out these two alternatives
occurring together. This gives the simultaneous-solvability clause, and the
existing centralizer noncontainment theorem supplies the other source clause.

The standing minimal-counterexample, simple-reduction and residual-action
hypotheses are exactly those used by the existing local-recognition results.
In particular the earlier action theorem, supplied by
`residualAction_of_minimalCounterexample`, remains the assembly owner's
source input; no sign or trace-count hypothesis is assumed here.

Source: GLS, Volume 4, Chapter 2, Corollary 7.14.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem centralizerCircle_solvable_of_solvable
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {v₁ v₂ : G}
    (hv₁ : IsInvolution v₁) (hv₁M : v₁ ∈ M)
    (hC₁ : ¬ Subgroup.centralizer ({v₁} : Set G) ≤ M)
    (hv₂ : IsInvolution v₂) (hv₂M : v₂ ∈ M)
    (hC₂ : ¬ Subgroup.centralizer ({v₂} : Set G) ≤ M)
    (hsol : Group.IsSolvable (localCircle Z (Subgroup.centralizer ({v₁} : Set G)))) :
    Group.IsSolvable (localCircle Z (Subgroup.centralizer ({v₂} : Set G))) := by
  by_contra hns
  have hc₁ := residualCentralizerTrace_ncard_eq_one_of_solvable
    h.disconnected r ha hv₁ hv₁M hC₁ hsol
  obtain ⟨n, hn, hc₂⟩ := residualCentralizerTrace_ncard_eq_two_pow_sub_one_of_nonsolvable
    h r ha hv₂ hv₂M hC₂ hns
  have hp := residualCentralizerTrace_ncard_modEq_four h.disconnected r hv₁ hv₁M hv₂ hv₂M
  rw [hc₁, hc₂] at hp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hk : 0 < 2 ^ k := pow_pos (by decide) _
  simp only [Nat.ModEq, pow_add] at hp
  norm_num only [pow_two, Nat.reduceMul, Nat.reduceMod] at hp
  omega

/-- Involution centralizers escaping `M` have simultaneously solvable
or nonsolvable distinguished circles, by the literal trace counts. -/
public theorem centralizerCircle_solvable_iff
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {v₁ v₂ : G}
    (hv₁ : IsInvolution v₁) (hv₁M : v₁ ∈ M)
    (hC₁ : ¬ Subgroup.centralizer ({v₁} : Set G) ≤ M)
    (hv₂ : IsInvolution v₂) (hv₂M : v₂ ∈ M)
    (hC₂ : ¬ Subgroup.centralizer ({v₂} : Set G) ≤ M) :
    Group.IsSolvable (localCircle Z (Subgroup.centralizer ({v₁} : Set G))) ↔
      Group.IsSolvable (localCircle Z (Subgroup.centralizer ({v₂} : Set G))) :=
  ⟨centralizerCircle_solvable_of_solvable h r ha hv₁ hv₁M hC₁ hv₂ hv₂M hC₂,
    centralizerCircle_solvable_of_solvable h r ha hv₂ hv₂M hC₂ hv₁ hv₁M hC₁⟩

/-- Both clauses of GLS4 Corollary 7.14 under the standing distinguished
local-recognition hypotheses, with the ambient circles for noncontainment
and their internal realizations for solvability. -/
public theorem localCircle_corollary714
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {v₁ v₂ : G}
    (hv₁ : IsInvolution v₁) (hv₁M : v₁ ∈ M)
    (hC₁ : ¬ Subgroup.centralizer ({v₁} : Set G) ≤ M)
    (hv₂ : IsInvolution v₂) (hv₂M : v₂ ∈ M)
    (hC₂ : ¬ Subgroup.centralizer ({v₂} : Set G) ≤ M) :
    ¬ centralizerClosure Z v₁ ≤ M ∧ ¬ centralizerClosure Z v₂ ≤ M ∧
      (Group.IsSolvable (localCircle Z (Subgroup.centralizer ({v₁} : Set G))) ↔
        Group.IsSolvable (localCircle Z (Subgroup.centralizer ({v₂} : Set G)))) :=
  ⟨centralizerClosure_not_le h.disconnected r hv₁ hv₁M hC₁,
    centralizerClosure_not_le h.disconnected r hv₂ hv₂M hC₂,
    centralizerCircle_solvable_iff h r ha hv₁ hv₁M hC₁ hv₂ hv₂M hC₂⟩

end BenderSuzuki.ZD
