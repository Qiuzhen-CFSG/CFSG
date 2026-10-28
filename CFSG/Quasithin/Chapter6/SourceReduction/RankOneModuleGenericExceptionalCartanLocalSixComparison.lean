module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.SixCubic

/-!
# Comparison of the two original Thompson actions in the six-space case

The right six-space makes the escaping cubic fail to normalize J(T).
The left natural row makes the whole Borel normalize J(T), so that row
is impossible. The genuine symmetric-five row therefore remains, with
n=2, the literal left A₅ quotient and equality of the original Cartan
with its escaping cubic. In particular degree greater than two selects
the right four-space without assuming cubic omega-centralization.

The completed FF reduction supplies these comparisons on the universal
source Input. The symmetric-five omega argument, blocks, and subsequent
sieve remain with the local Cartan classification owner.

Source: Aschbacher–Smith 5.1.13, printed p.637.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The six-space forces the genuine left symmetric-five alternative,
including the original degree and quotient; it is not itself an exclusion. -/
theorem LocalA7Configuration.six_left_symmetric_five
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (hc : Nat.card (localOmegaModule T K) = 64) :
    n = 2 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) ∧
      A = D ∧ ¬ D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  have hn := a.six_cubic_not_normalizes_thompson h hH hgen c d hc
  rcases a.left_thompson_cubic_dichotomy h c d with hnat | hfive
  · exact (hn (((d.cubic_le.trans inf_le_left).trans c.left_le).trans
      (le_sup_left.trans hnat.2))).elim
  · exact hfive

/-- Higher left degree selects the right four-space and its natural-left
Thompson containment using both original Hall conditions. -/
theorem LocalA7Configuration.four_of_degree_gt_two
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) (hn : 2 < n) :
    Nat.card (localOmegaModule T K) = 16 ∧
      B ⊔ D ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      localBorel T L ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  have hc : Nat.card (localOmegaModule T K) = 16 := by
    rcases a.card with hc | hc
    · exact hc
    · have hh := (a.six_left_symmetric_five h hH hgen c d hc).1
      omega
  exact ⟨hc,a.four_cubic_normalizes_thompson h hH hgen c d hc,
    a.four_left_thompson_natural h hH hgen c d hc⟩

/-- The actual source inputs have a four-space or a degree-two six-space.
The FF reduction is proved and the latter alternative retains its full data. -/
theorem localCartan_noncentral_thompson_comparison
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K : Subgroup G, LocalA7Configuration T L H X K ∧
      ((Nat.card (localOmegaModule T K) = 16 ∧
        B ⊔ D ⊔ (T : Subgroup G) ≤
          normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
        elementaryAbelianMaxJ (T : Subgroup G) ≤
          ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
        localBorel T L ⊔ (T : Subgroup G) ≤
          normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ∨
      (Nat.card (localOmegaModule T K) = 64 ∧ n = 2 ∧
        Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) ∧ A = D ∧
        ¬ D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))) := by
  obtain ⟨K,a⟩ := localCartan_ffReduction T L W n h H hH hgen A B c Y hY X D d hXC
  refine ⟨K,a,?_⟩
  rcases a.card with hc | hc
  · exact Or.inl ⟨hc,a.four_cubic_normalizes_thompson h hH hgen c d hc,
      a.four_left_thompson_natural h hH hgen c d hc⟩
  · exact Or.inr ⟨hc,a.six_left_symmetric_five h hH hgen c d hc⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
