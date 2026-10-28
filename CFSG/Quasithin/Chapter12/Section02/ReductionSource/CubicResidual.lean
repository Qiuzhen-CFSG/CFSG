module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceCubicResidual

/-!
# The original Chapter 12 nonnormal branch has its cubic residual

The Hypothesis 12.2.1 input constructs the same Fundamental Setup used by
Chapter 10. Its nonnormal branch now supplies O^{3′}(M)=⟨Lᵀ⟩ and the
normalizer order consequence of 10.2.1 without a residual-identification
premise. In the alternating-five case the quotient marking discharges the
cubic divisibility condition as well.

These are source inputs for the remaining 10.0.1 normalization argument;
they do not assert the seven-case module classification of 12.2.2.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
10.1.3–10.2.1, printed pp.742–743, and Theorem 12.2.2, printed p.795.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal earlier-source input supplies the nonnormal cubic residual
and its normalizer consequence on one and the same Fundamental Setup. -/
theorem Hypothesis1221.exists_original_cubic_residual_setup
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      (primeToResidual 3 D.maximalLocal).map D.maximalLocal.subtype = localOrbit T L ∧
      ∀ S : Subgroup G,
        Nat.Coprime 3 (Nat.card (localOrbit T L ⊓ normalizer (S : Set G) : Subgroup G)) →
        Nat.Coprime 3 (Nat.card (D.maximalLocal ⊓ normalizer (S : Set G) : Subgroup G)) := by
  obtain ⟨D⟩ := h.exists_original_fundamentalSetup
  exact ⟨D, Chapter10.source_nonnormal_cubic_residual D hn hd,
    Chapter10.source_nonnormal_normalizer_three_free D hn hd⟩

/-- The A₅ branch of original 10.2.1 needs no separate quotient order or
cubic residual assumption. The later normalizer intersection bound remains
with the original marked-module calculation. -/
theorem Hypothesis1221.exists_original_alternating_five_residual_setup
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      (primeToResidual 3 D.maximalLocal).map D.maximalLocal.subtype = localOrbit T L ∧
      ∀ S : Subgroup G,
        Nat.Coprime 3 (Nat.card (localOrbit T L ⊓ normalizer (S : Set G) : Subgroup G)) →
        Nat.Coprime 3 (Nat.card (D.maximalLocal ⊓ normalizer (S : Set G) : Subgroup G)) := by
  apply h.exists_original_cubic_residual_setup hn
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

end CFSG.Quasithin.Chapter12.Section02
