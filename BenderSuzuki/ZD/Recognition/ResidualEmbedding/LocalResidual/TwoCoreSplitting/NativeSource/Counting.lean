module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.NativeSource.Models
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.LinearCount

/-!
# Section 17 counting from the preceding source inputs

The local nonsolvability and distinguished-trace count determine the actual
covering models. Strong embedding supplies a Sylow subgroup inside M; Sylow
conjugacy transports the Section 16 divisibility statement to that subgroup.
The proved incidence counts and model elimination then construct the original
counting witness. No model alternative or Sylow placement is a hypothesis.

Source: GLS IV, Chapter 2, Lemmas 16.3, 16.4(c), Corollary 16.6, and
Lemmas 17.1–17.5. The geometric clauses of 17.2(e,f) remain explicit here.
-/

noncomputable section
namespace BenderSuzuki.ZD.Section17
open Subgroup PFAppendixIII Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The counting witness on the original t and u, constructed without a
model or placed-Sylow premise. The parameter comes from the literal trace,
and the input Sylow subgroup is arbitrary. -/
public theorem twoCoreCountingData_of_nonsolvable_trace
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hnM : ¬ IsStronglyEmbedded M)
    (hg : ResidualGeneration Z M) (d : TwoCoreLocalData Z M)
    (hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (hns : ¬ Group.IsSolvable
      (localCircle Z (centralizer ({((d.u : M) : G)} : Set G))))
    {n : ℕ} (htrace : (residualCentralizerTrace Z M ((d.u : M) : G)).ncard = 2 ^ n - 1)
    (P : Sylow 2 (centralizerClosure Z ((d.u : M) : G)))
    (hdiv : 2 ^ n * Nat.card P ∣ Nat.card (G ⧸ M) - 1)
    (hfusion : IsConj ((d.u : M) : G) (d.t * ((d.u : M) : G)))
    (hfix : ∀ gamma : G ⧸ M,
      residualPairStabilizer M d.t ⊓
          centralizerClosure Z (d.t * ((d.u : M) : G)) ≤
        MulAction.stabilizer G gamma ↔
      gamma = QuotientGroup.mk 1 ∨ gamma = d.t • (QuotientGroup.mk 1 : G ⧸ M))
    (hN : let L := centralizerClosure Z (d.t * ((d.u : M) : G))
      let H := (residualPairStabilizer M d.t ⊓ L).subgroupOf L
      let t : L := ⟨d.t, t_mem_twisted_circle d⟩
      normalizer (H : Set L) ≤ H ⊔ zpowers t) :
    Nonempty (TwoCoreCountingData Z M) := by
  have hv : PFAppendixIII.IsInvolution ((d.u : M) : G) := by
    have ho : orderOf ((d.u : M) : G) = 2 := by simpa using d.u_order
    obtain ⟨hs, hn⟩ := orderOf_eq_prime_iff.mp ho
    exact ⟨hn, hs⟩
  have hC : ¬ centralizer ({((d.u : M) : G)} : Set G) ≤ M := fun hle =>
    d.t_not_mem (hle (mem_centralizer_singleton_iff.mpr d.commutes_t.symm.eq))
  have hn := (centralizerCircle_model_at_trace h r ha hv
    (d.u : M).property hC hns htrace).1
  obtain ⟨Q, hQM⟩ := exists_sylow_in_centralizerClosure_le h.disconnected r hv
    (d.u : M).property hC
  have hdivQ : 2 ^ n * Nat.card Q ∣ Nat.card (G ⧸ M) - 1 := by
    rw [Nat.card_congr (Q.equiv P).toEquiv]
    exact hdiv
  exact twoCoreCountingData_of_source_inputs h r ha hnM hg d hlocal n hn Q hQM hdivQ
    hfusion hfix hN (centralizerClosure_models_at_trace h r ha hv
      (d.u : M).property hC hns htrace)

end BenderSuzuki.ZD.Section17
