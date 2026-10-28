module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition
public import CFSG.Quasithin.ChapterG.Section09.Basic
public import Theory.Representation.Quotient

/-!
# The original-actor parameters for binary rank-one recognition

A genuine isomorphism from the component to SL₂ transports its faithful
irreducible action to the reusable classifier. Normalization and binary
irreducibility embed the elementary abelian actor in the component's
automorphism group. The proved sharp two-rank bound then gives `m ≤ n`.
Together with the source degree bound this yields `m ≥ n-1` for the
natural and Hermitian cases, and `m = 3` for the exceptional triple tensor.

The intertwining equivalences retain the actual component isomorphism.
The Hermitian case includes a field identification with GF(2^(2s)) and
its fixed half-field action, also for `s = 1`. The literal minus Omega
comparison is a separate group-and-module comparison, not inferred from
these dimensions.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3(6),
(7), (16), printed pp.354,356--357.
-/

public section

open scoped MatrixGroups
open Representation.SL2

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {C : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}
  {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- The original elementary abelian actor has rank at most `n` when its
irreducible component is genuinely isomorphic to SL₂(2ⁿ). The sharp model
bound is proved, rather than retained as an extra premise. -/
theorem rank_one_actor_rank_le
    (h : ComponentHypothesis C ρ A L L m)
    (e : L ≃* SL(2,K)) {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card K = 2 ^ n) : m ≤ n := by
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hr : primeRank 2 (MulAut L) ≤ n := by
    rw [Theory.GroupTheory.primeRank_equiv 2 (MulAut.congr e)]
    exact Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn hcard
  apply (h.toSetup.rank_le_automorphisms ?_).trans hr
  rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_H]
  exact le_top

/-- The SL₂ branches (6), (7), (16) of G.9.3 with their original actor and
actual intertwiners. Case (7) uses the concrete Hermitian action; identifying
that action with literal minus Omega is the separate model comparison.
No automorphism-rank or module-classification premise remains. -/
theorem rank_one_module_alternatives
    (h : ComponentHypothesis C ρ A L L m)
    (e : L ≃* SL(2,K)) (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card K = 2 ^ n) :
    let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
    m ≤ n ∧
    ((Module.finrank (ZMod 2) V = 2 * n ∧ n - 1 ≤ m ∧ BinarySmall.IsNatural σ) ∨
    (∃ s : ℕ, ∃ hs : 0 < s, n = 2 * s ∧ Module.finrank (ZMod 2) V = 2 * n ∧
      n - 1 ≤ m ∧ letI : NeZero s := ⟨hs.ne'⟩; BinarySmall.IsHermitian σ s) ∨
    (n = 3 ∧ Module.finrank (ZMod 2) V = 8 ∧ m = 3 ∧ BinarySmall.IsTriple σ ∧
      Nonempty (K ≃+* GaloisField 2 3) ∧
      ∀ τ : K ≃+* K, ∃ j : ℕ, j < 3 ∧ (iterateFrobeniusEquiv K 2 1) ^ j = τ)) := by
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  have hf : Function.Injective σ := h.faithful.comp (L.subtype_injective.comp e.symm.injective)
  have hm := rank_one_actor_rank_le h e hn hcard
  have hd := h.degree_le
  have hsmall : Module.finrank (ZMod 2) V ≤ 2 * (n + 1) := by omega
  refine ⟨hm, ?_⟩
  rcases binary_small_faithful_classification σ hf n hn hcard hsmall with hnat | hherm | htriple
  · exact .inl ⟨hnat.2.1, by omega, hnat.2.2⟩
  · obtain ⟨hs, hv, hpos, hh⟩ := hherm
    exact .inr (.inl ⟨_, hpos, hs.symm, hv, by omega, hh⟩)
  · obtain ⟨_, hn3, hv, ht, hfield, hfrob⟩ := htriple
    exact .inr (.inr ⟨hn3, hv, by omega, ht, hfield, hfrob⟩)
end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic
