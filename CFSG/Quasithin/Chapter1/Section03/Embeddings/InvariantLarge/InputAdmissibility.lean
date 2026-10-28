module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction

/-!
# The scope of the intrinsic Ξ input

An odd Ξ-complement normalized irreducibly by a two-group satisfies every
`LocalInput` clause with `X = P` if the overgroup has trivial two-core.
The two-residual identities then follow from coprimeness, and the
Frattini-commutator identity follows from irreducibility and noncyclicity.

This calculation records an input-boundary issue for Proposition 1.3.4:
`LocalInput` does not include the original `XT ∈ H` condition, characteristic
two, or a Sylow condition in the overgroup. In particular these must not be
silently inferred when applying source A.3.15, whose hypotheses include a
Sylow two-subgroup of the almost-simple group. This theorem is a construction
of local inputs, not a counterexample to the full embedding statement.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Definition 1.3.1 and Lemma 1.3.2, pp. 508–509;
Lemma A.3.15, pp. 50–51.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
variable {G : Type*} [Group G]

/-- The record admits X = P and a trivial two-core in the overgroup. -/
theorem localInput_of_normalized_complement [Finite G] {p : ℕ} [Fact p.Prime]
    {T P H : Subgroup G} (ho : Odd p) (hP : XiOddQuotient p P)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer P) (hH : P ⊔ T ≤ H)
    (hcoreH : pCore 2 H = ⊥)
    (hirr : ∀ A : Subgroup (P ⧸ frattini P),
      (∀ s : (T ⊓ normalizer P : Subgroup G), ∀ a ∈ A,
        frattiniConjugationAction (T ⊓ normalizer P) P inf_le_right s a ∈ A) →
      A = ⊥ ∨ A = ⊤) : LocalInput p T P P H := by
  have hp := hP.isPGroup
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr ho
  have hcore : pCore 2 P = ⊥ := by
    have hd := (pCore_isPGroup (p := 2) (G := P)).disjoint_of_coprime
      (hp.to_subgroup ⊤) hcop
    simpa only [inf_top_eq] using hd.eq_bot
  have hcoreIn : P.pCoreIn 2 = ⊥ := by
    change (pCore 2 P).map P.subtype = ⊥
    rw [hcore, Subgroup.map_bot]
  have hperf : IsPPerfect 2 P := by
    intro N hN htwo
    let _ := hN
    have hpq := hp.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    have hd := (htwo.to_subgroup ⊤).disjoint_of_coprime (hpq.to_subgroup ⊤) hcop
    have htop : (⊤ : Subgroup (P ⧸ N)) = ⊥ := by
      simpa only [inf_idem] using hd.eq_bot
    apply top_unique
    intro x _
    apply (QuotientGroup.eq_one_iff x).mp
    exact Subgroup.mem_bot.mp (htop ▸ mem_top (QuotientGroup.mk' N x))
  have hq : XiOddQuotient p (XiQuotient P) :=
    hP.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hcore).trans
      QuotientGroup.quotientBot).symm
  refine ⟨Fact.out, ho, hH, hT, hn, hperf, hq, ?_, ?_, ?_, ?_, ?_, ?_, hirr, ?_, ?_⟩
  · exact isSylowIn_iff.mpr ⟨hp, le_rfl, fun U _ hPU hUP => le_antisymm hUP hPU⟩
  · rw [hcoreIn, bot_sup_eq]
  · rw [hcoreIn]
    exact disjoint_bot_left
  · rw [hcoreIn]
    apply le_antisymm
    · apply (Subgroup.closure_le (K := P)).mpr
      rintro x ⟨n, hn, a, ha, rfl⟩
      have hn1 : n = 1 := hn
      change n * a * n⁻¹ ∈ P
      simpa only [hn1, one_mul, inv_one, mul_one] using ha
    · intro x hx
      exact subset_closure ⟨1, mem_bot.mpr rfl, x, hx, by simp⟩
  · rw [hcoreIn, commutator_bot_left]
  · rw [hcoreIn, bot_sup_eq, inf_eq_left.mpr hn]
  · exact XiAction.eq_commutator_frattini_of_irreducible P _ inf_le_right
      (hT.to_le inf_le_left) hp hP.not_isCyclic hirr
  · have hh : H.pCoreIn 2 = ⊥ := by
      change (pCore 2 H).map H.subtype = ⊥
      rw [hcoreH, Subgroup.map_bot]
    rw [hh, bot_sup_eq, (pResidual_eq_top_iff 2 P).mpr hperf,
      ← MonoidHom.range_eq_map, range_subtype]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
