module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.LocalGeometry.UnitaryDegree

/-!
# Local fixed-coset geometry in Lemma 12.8

The literal odd-core quotient supplies the fixed subgroup order q = 2^k and
the Borel degree q^i+1. If the actor centralizes L, Lemma 12.3 gives either
collapse or an actual unitary enlargement. Computing that same Borel index
in the supplied model forces the same exponent i; the distinguished subgroup
order forces the same k. Thus the model and count are coupled without any
centralization, collapse, or ambient degree premise.

Source: GLS4, Chapter 2, Lemmas 12.3–12.4 and the fixed-orbit calculation of
Lemma 12.8, `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII LocalGeometry
open _root_.BenderSuzuki.MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem degree_exponent_injective {k i j : ℕ} (hk : 2 ≤ k)
    (he : (2 ^ k) ^ i + 1 = (2 ^ k) ^ j + 1) : i = j := by
  apply Nat.pow_right_injective (show 2 ≤ 2 ^ k from
    one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (by omega))
  exact Nat.add_right_cancel he

/-- The complete pointwise local geometry, conditional only on the authorized
Lemma 12.3–12.4 local data. The integer parameters agree in every model clause. -/
public theorem proper_residualGenerated_point_geometry_of_local
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t) :
    ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      ∃ k i : ℕ, ResidualCentralizerPointGeometry Z M z t v k i := by
  intro v hvD hv
  obtain ⟨k, i, hk, hi, ho, hcard, hfixed⟩ :=
    fixed_cosets_geometry_parameters h.disconnected r htM hlocal hvD hv
  refine ⟨k, i, hk, hi, ho, hcard, hfixed, ?_⟩
  intro hvL
  obtain ⟨n, hn, hmodels, hAL, _, _, _, _, _, hAcard, _⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  have hAC : closure (Z ∩ (M : Set G)) ≤ centralizer ({v} : Set G) := by
    intro a haA
    apply mem_centralizer_singleton_iff.mpr
    exact mem_centralizer_iff.mp hvL a (hAL haA)
  have hAk : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ k := by
    simpa only [inf_eq_left.mpr hAC] using hcard
  have hnk : n = k := Nat.pow_right_injective (by decide : 2 ≤ 2)
    (hAcard.symm.trans hAk)
  subst n
  have hindex := fixed_cosets_card_eq_local_index r hlocal hvD hv
  rcases hlocal.centralizing_extension v hvL hv.ne_one with he | he
  · rw [he] at hindex
    have hs := stronglyEmbedded_in_proper_residualGenerated
      h.disconnected r hz hzM ht htM hL
    rcases hmodels with hpsl | ⟨m, hm, hkm, hsuz⟩
    · obtain ⟨e⟩ := hpsl
      have hb := borel_of_stronglyEmbedded_simple hs
        ((IsSimpleBenderGroupAtExponent.isPSL2 ⟨e⟩).isSimple hk)
      have hdegree : (M.comap (residualGenerated M z t).subtype).index = 2 ^ k + 1 := by
        exact ((M.comap (residualGenerated M z t).subtype).index_map_equiv e).symm.trans
          (psl2_borel_index hk (hb.map_mulEquiv e))
      have hii : i = 1 := degree_exponent_injective hk (by
        simpa only [pow_one] using hfixed.symm.trans (hindex.trans hdegree))
      exact Or.inl ⟨hii, he, ⟨e⟩⟩
    · obtain ⟨e⟩ := hsuz
      have hb := borel_of_stronglyEmbedded_simple hs
        ((IsSimpleBenderGroupAtExponent.isSuzuki ⟨m, hkm, ⟨e⟩⟩).isSimple hk)
      have hdegree : (M.comap (residualGenerated M z t).subtype).index = (2 ^ k) ^ 2 + 1 := by
        rw [hkm]
        exact ((M.comap (residualGenerated M z t).subtype).index_map_equiv e).symm.trans
          (suzuki_borel_index hm (hb.map_mulEquiv e))
      have hii := degree_exponent_injective hk (hfixed.symm.trans (hindex.trans hdegree))
      exact Or.inr (Or.inl ⟨hii, he, m, hm, hkm, ⟨e⟩⟩)
  · obtain ⟨j, hj, hAj, hpsl, hlt, hcover⟩ := he
    have hjk : j = k := Nat.pow_right_injective (by decide : 2 ≤ 2) (hAj.symm.trans hAk)
    subst j
    have hs := (pair_involution_centralizerClosure_local
      h.disconnected r htM hvD hv).2.2
    have hdegree := unitary_cover_index hk hcover hs
    have hii := degree_exponent_injective hk (hfixed.symm.trans (hindex.trans hdegree))
    exact Or.inr (Or.inr ⟨hii, hlt, hcover, hpsl⟩)

end BenderSuzuki.ZD
