module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.Exceptional.MarkedQuotient.TwoCover
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.Exceptional.MarkedQuotient.LocalData
public import Theory.GroupAction.SemilinearPointStabilizerExceptional
public import Theory.GroupTheory.PCoreSurjective

/-!
# Conditional assembly of the marked exceptional quotient

The homocyclic local structure and the faithful field action together give
the exact witnesses used in the last paragraph of GLS 4, Chapter 2,
Lemma 15.7. Factoring out the two-core gives trivial two-core, so the proved
semilinear-stabilizer classification identifies `M/V` with `PSL₃(2)` and
forces `n = 3`. The double-cover comparison then identifies the literal
`M/R₀` with `SL₂(7)`, marking the centralizer element by `-I`.

The two structures are explicit intermediate inputs. Their construction
from the original minimal-counterexample and residual-action hypotheses
remains necessary; this module does not yet assert the unconditional source
conclusion. Final source assembly belongs here once both producers are proved.
All normality and both quotients are relative to `M`.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemma 15.7, lines 2738–2754.
-/

namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1

/-- Apply the action classification to the actual two-core quotient.
The trivial-two-core premise is proved from the quotient definition. -/
public theorem ExceptionalFieldAction.exceptional
    {G : Type*} [Group G] [Finite G] {M : Subgroup G} {n : ℕ}
    (a : ExceptionalFieldAction M n) (hn : 2 ≤ n) :
    n = 3 ∧ Nonempty
      (M ⧸ pCore 2 M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let := a.action
  let : FaithfulSMul (M ⧸ pCore 2 M) (GaloisField 2 n) := a.faithful
  have hcore : pCore 2 (M ⧸ pCore 2 M) = ⊥ := by
    let q := QuotientGroup.mk' (pCore 2 M)
    have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
    have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    have hc := congrArg (map q) (q.comap_pCore_of_ker_isPGroup hq hk)
    rw [map_comap_eq_self_of_surjective hq] at hc
    exact hc.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))
  exact a.coordinates.exceptional a.two_transitive hn (GaloisField.card 2 n (by omega)) hcore

/-- Assemble the marked quotient and its complete fiber fusion from the
local subgroup and action constructions. These two premises still require
source proofs; the result supplies the exact square-lifting interface. -/
public theorem linear_marked_quotient_of_local_structure_and_action
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} {n : ℕ} (hn : 2 ≤ n)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hRV : linearCentralizerClosure M z t = pCore 2 M)
    (d : ExceptionalLocalStructure Z M z t n) (a : ExceptionalFieldAction M n) :
    n = 3 ∧ ∃ (u : M) (R₀ : Subgroup M) (hR₀ : R₀.Normal),
      letI := hR₀
      (u : G) ∈ centralizer (residualGenerated M z t : Set G) ∧ (u : G) ≠ 1 ∧
        ∃ eQ : M ⧸ R₀ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 7),
          eQ (QuotientGroup.mk' R₀ u) = -1 ∧
          ∀ v : M, QuotientGroup.mk' R₀ v = QuotientGroup.mk' R₀ u →
            IsConj (v : G) (u : G) := by
  obtain ⟨hnthree, ⟨eB⟩⟩ := a.exceptional hn
  obtain ⟨eQ, hu⟩ := linear_marked_sl2Seven_of_two_cover h r d.kernel
    (d.kernel_le_closure.trans hRV.le) (d.core_image_card_two hR hRV)
    eB d.u (hRV ▸ d.u_mem_closure) d.u_not_mem
  exact ⟨hnthree, d.u, d.kernel, d.kernel_normal, d.u_mem, d.u_ne_one,
    eQ, hu, d.marked_coset_fusion⟩

end BenderSuzuki.ZD
