module

public import CFSG.Quasithin.Chapter1.Defs

/-!
# The collection `He`: elementary local setup

The final lemma of Aschbacher–Smith §1.1 (Lemma 1.1.6, p. 503 in the
combined 1 March 2004 manuscript) supplies the inputs of Lemma 1.1.5.
A normal two-subgroup `B` lies in the cores of `K` and `K ∩ M`.
Centralizing the latter core therefore forces membership in `C_G(B) ≤ K`.
The identity `T ∩ K = S` places the central involution in `S`.

The even-characteristic input is stated explicitly for the chosen Sylow
subgroup. No quasithin or known-simple-group assumption is needed for this
local setup. The component classification in Lemma 1.1.5 requires those
additional assumptions and is a separate part of the section.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1

open Subgroup

variable {G : Type*} [Group G]

/-- A two-local subgroup has nontrivial two-core. -/
theorem mem_H_of_isTwoLocal {K : Subgroup G} (hK : IsTwoLocal K) : K ∈ H G := by
  obtain ⟨B, hne, hp, rfl⟩ := hK
  intro he
  apply hne
  apply le_antisymm _ bot_le
  have hb := le_pCoreIn_of_normalizes hp B.le_normalizer le_rfl
  exact he ▸ hb

/-- The ambient definition of `He` is exactly the intrinsic centralizer
condition `C_K(O₂(K)) ≤ O₂(K)` from Definition 1.1.1. -/
theorem mem_He_iff {K : Subgroup G} : K ∈ He G ↔
    centralizer (pCore 2 K : Set K) ≤ pCore 2 K := by
  constructor
  · intro h x hx
    have hc : (x : G) ∈ centralizer (K.pCoreIn 2 : Set G) := by
      apply mem_centralizer_iff.mpr
      intro y hy
      obtain ⟨a, ha, rfl⟩ :=
        (mem_map (f := K.subtype) (K := pCore 2 K)).mp hy
      exact congrArg Subtype.val (mem_centralizer_iff.mp hx a ha)
    obtain ⟨y, hy, he⟩ := mem_map.mp (h ⟨x.property, hc⟩)
    exact (Subtype.ext he : y = x) ▸ hy
  · intro h x hx
    have hc : (⟨x, hx.1⟩ : K) ∈ centralizer (pCore 2 K : Set K) := by
      intro y hy
      apply Subtype.ext
      exact mem_centralizer_iff.mp hx.2 y (mem_map.mpr ⟨y, hy, rfl⟩)
    exact mem_map.mpr ⟨⟨x, hx.1⟩, h hc, rfl⟩

/-- Aschbacher–Smith 1.1.6: a sufficiently large subgroup of a two-local
subgroup satisfies all the hypotheses of 1.1.5. The explicit hypothesis
`hEven` is condition (E) for maximal two-locals containing the chosen `T`. -/
theorem lemma_1_1_6 [Finite G]
    {B K M : Subgroup G} (hBne : B ≠ ⊥) (hB : IsPGroup 2 B)
    (hBK : B ≤ K) (hCK : centralizer (B : Set G) ≤ K)
    (hKN : K ≤ normalizer (B : Set G))
    (S : Sylow 2 K) (T : Sylow 2 G)
    (hST : (S : Subgroup K).map K.subtype ≤ (T : Subgroup G))
    {z : G} (hz : orderOf z = 2) (hzT : z ∈ (T : Subgroup G))
    (hzcentral : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hM : IsMaximalTwoLocal M) (hCM : centralizer ({z} : Set G) ≤ M)
    (hEven : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      (T : Subgroup G) ≤ N → N ∈ He G) :
    Lemma115Hypotheses K S M z := by
  have hTM : (T : Subgroup G) ≤ M := by
    intro t ht
    apply hCM
    exact mem_centralizer_singleton_iff.mpr (hzcentral t ht)
  have hcore : B ≤ K.pCoreIn 2 := le_pCoreIn_of_normalizes hB hBK hKN
  have hBS : B ≤ (S : Subgroup K).map K.subtype :=
    hcore.trans (pCoreIn_le_sylow K S)
  have hzC : z ∈ centralizer (B : Set G) := by
    intro b hb
    exact hzcentral b (hST (hBS hb))
  have hzK : z ∈ K := hCK hzC
  have hinf := inf_eq_sylow_map S T.isPGroup' hST
  refine ⟨?_, ?_, ?_, hz, ?_, ?_, hCM⟩
  · intro he
    exact hBne (le_antisymm (he ▸ hcore) bot_le)
  · exact ⟨hEven M hM hTM, mem_H_of_isTwoLocal hM.1, hST.trans hTM⟩
  · exact centralizer_pCoreIn_inf_le hB hBK (hBS.trans (hST.trans hTM)) hKN hCK
  · rw [← hinf]
    exact ⟨hzT, hzK⟩
  · intro s hs
    exact hzcentral s (hST hs)

end CFSG.Quasithin.Chapter1
