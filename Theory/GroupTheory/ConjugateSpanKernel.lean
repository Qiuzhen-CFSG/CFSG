module

public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.PGroupCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Kernels on conjugate spans

For W = ⟨Z^(KH)⟩ and U = [W,K] normalized by H, the generation identity
W = ⟨Z^H⟩ ⊔ U lets an H-invariant subgroup fixing Z and U fix all of W.
We also prove the finite-group input used to place such a kernel in a
Sylow subgroup: a proper normal subgroup of a p-perfect group whose
p-core quotient has prime order lies in the p-core.

These elementary generation and kernel arguments supply the local action
comparison in Aschbacher–Smith, combined manuscript of 1 March 2004,
§13.6, printed pp.928–931, using the cubic residual from p.926.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

/-- Every proper normal subgroup lies in the p-core when the group is
p-perfect and its p-core quotient has prime order. -/
theorem normal_le_pCore_of_pPerfect_prime_quotient [Finite G]
    {p : ℕ} (hG : IsPPerfect p G)
    (hprime : (Nat.card (G ⧸ pCore p G)).Prime)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊤) : N ≤ pCore p G := by
  let f := QuotientGroup.mk' (pCore p G)
  let : Fact (Nat.card (G ⧸ pCore p G)).Prime := ⟨hprime⟩
  rcases (N.map f).eq_bot_or_eq_top_of_prime_card with h | h
  · simpa only [f, QuotientGroup.ker_mk'] using (map_eq_bot_iff N).mp h
  · have hs : N ⊔ pCore p G = ⊤ := by
      have hh := congrArg (fun A : Subgroup (G ⧸ pCore p G) => A.comap f) h
      simpa only [comap_map_eq, f, QuotientGroup.ker_mk', comap_top] using hh
    exact (hN (hG N inferInstance
      (isPGroup_quotient_of_sup_eq_top N (pCore p G) pCore_isPGroup hs))).elim

/-- A proper restriction kernel in a p-perfect group with prime core
quotient is a p-group. -/
theorem isPGroup_inf_centralizer_of_prime_core_quotient [Finite G]
    {p : ℕ} (D U : Subgroup G) (hp : IsPPerfect p D)
    (hprime : (Nat.card (D ⧸ pCore p D)).Prime)
    (hn : D ≤ normalizer (U : Set G)) (hmove : ¬ D ≤ centralizer (U : Set G)) :
    IsPGroup p (D ⊓ centralizer (U : Set G) : Subgroup G) := by
  let C := D ⊓ centralizer (U : Set G)
  have hDC : D ≤ normalizer (C : Set G) :=
    (le_inf D.le_normalizer (hn.trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  let : (C.subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer (show C ≤ D from inf_le_left)).mpr hDC
  have hproper : C.subgroupOf D ≠ ⊤ := by
    intro he
    apply hmove
    intro x hx
    have hc : (⟨x, hx⟩ : D) ∈ C.subgroupOf D := he ▸ mem_top _
    exact hc.2
  have hcore := normal_le_pCore_of_pPerfect_prime_quotient hp hprime
    (C.subgroupOf D) hproper
  exact (pCore_isPGroup.to_le hcore).of_equiv
    (subgroupOfEquivOfLe (show C ≤ D from inf_le_left))

/-- Splitting off the displacements of one set of conjugators. -/
theorem conjugateSpanBy_sup_eq_span_sup_commutator (Z K H : Subgroup G)
    (hU : H ≤ normalizer
      (⁅conjugateSpanBy Z (K ⊔ H), K⁆ : Subgroup G)) :
    conjugateSpanBy Z (K ⊔ H) =
      conjugateSpanBy Z H ⊔ ⁅conjugateSpanBy Z (K ⊔ H), K⁆ := by
  let W := conjugateSpanBy Z (K ⊔ H)
  let U := ⁅W, K⁆
  let V := conjugateSpanBy Z H
  have hV : V ≤ W := conjugateSpanBy_mono le_rfl le_sup_right
  have hU' : U ≤ W := le_normalizer_iff_commutator_le_left.mp
    (le_sup_left.trans (le_normalizer_conjugateSpanBy Z (K ⊔ H)))
  have hVW : V ⊔ U ≤ W := sup_le hV hU'
  apply le_antisymm ?_ hVW
  apply conjugateSpanBy_le ((le_conjugateSpanBy Z H).trans le_sup_left)
  apply sup_le
  · apply le_normalizer_iff.mpr
    intro k hk x hx
    have hc : ⁅k, x⁆ ∈ U := by
      change ⁅k, x⁆ ∈ ⁅W, K⁆
      rw [commutator_comm]
      exact commutator_mem_commutator hk (hVW hx)
    have hm := (V ⊔ U).mul_mem (mem_sup_right hc) hx
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hm
  · exact (le_inf (le_normalizer_conjugateSpanBy Z H) hU).trans
      (normalizer_inf_normalizer_le_normalizer_sup V U)

/-- An invariant kernel fixing both the seed and one displacement subgroup
fixes the whole span. -/
theorem le_centralizer_span_sup_of_kernel (Z K H Q : Subgroup G)
    (hU : H ≤ normalizer
      (⁅conjugateSpanBy Z (K ⊔ H), K⁆ : Subgroup G))
    (hQ : H ≤ normalizer (Q : Set G))
    (hz : Q ≤ centralizer (Z : Set G))
    (hu : Q ≤ centralizer (⁅conjugateSpanBy Z (K ⊔ H), K⁆ : Subgroup G)) :
    Q ≤ centralizer (conjugateSpanBy Z (K ⊔ H) : Set G) := by
  rw [conjugateSpanBy_sup_eq_span_sup_commutator Z K H hU]
  exact le_centralizer_iff.mpr (sup_le
    (le_centralizer_iff.mp (le_centralizer_conjugateSpanBy_of_normalizes Q Z H hQ hz))
    (le_centralizer_iff.mp hu))
end Subgroup

end
