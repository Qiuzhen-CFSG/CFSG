module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FourCubic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRightThompson

/-!
# The original local Cartan cubic comparison

In the four-dimensional right action, the original right Hall subgroup
and the escaping cubic normalize J(T). This contradicts the genuine
symmetric-five left row, so the natural-row Thompson containment and
whole-Borel normalization hold, including at degree two.

The completed FF reduction applies this result on the original source
inputs. If the cubic centralizes omega, the checked six-space obstruction
selects the four-space and removes the remaining dimension premise.
The block exclusions, degree restriction and sieve remain obligations
of the local Cartan classification owner.

Source: Aschbacher–Smith 5.1.13, printed p.637.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The original noncentral, centralizing-cubic branch has both Thompson
normalizations, with the actual Borel and the actual two-core containment. -/
theorem localCartan_noncentral_cubic_thompson_comparison
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T)
    (hd : D ≤ omegaCentralizer T) :
    ∃ K : Subgroup G, LocalA7Configuration T L H X K ∧
      Nat.card (localOmegaModule T K) = 16 ∧
      B ⊔ D ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      localBorel T L ⊔ (T : Subgroup G) ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  obtain ⟨K,a⟩ := localCartan_ffReduction T L W n h H hH hgen A B c Y hY X D d hXC
  have hc := (a.four_of_cubic_centralizes h hH hgen d hd).1
  exact ⟨K,a,hc,a.four_cubic_normalizes_thompson h hH hgen c d hc,
    a.four_left_thompson_natural h hH hgen c d hc⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
