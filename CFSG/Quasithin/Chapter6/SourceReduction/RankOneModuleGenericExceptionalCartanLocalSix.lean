module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.SixGeometry

/-!
# The centralizing-cubic branch of the original Cartan comparison

In the deleted A₇ six-space, omega-centralization forces normalization of
the actual A₅ residual section. The escaping cubic therefore rules out that
space whenever it centralizes omega. Applying the completed FF reduction
leaves the four-space, with its residual fixed-space vanishing, literal
A₇ two-core quotient and omega intersection of order two.

The full local Cartan classification owner retains the left-module
comparison, both block cases and torus argument. Cubic centralization here
is the explicit intermediate premise used in the A₅-module branch on p.637.

Source: Aschbacher–Smith 5.1.13, printed pp.637–638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- Centralization by the actual escaping cubic rules out the six-space
alternative. All four-space geometry remains on the original subgroups. -/
theorem LocalA7Configuration.four_of_cubic_centralizes
    {T : Sylow 2 G} {L W H A Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (d : LocalCartanWitness T H A Y X D) (hd : D ≤ omegaCentralizer T) :
    Nat.card (localOmegaModule T K) = 16 ∧
      localOmegaModule T K ⊓ centralizer (residual H : Set G) = ⊥ ∧
      Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* alternatingGroup (Fin 7)) ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (residual H : Set G) =
        omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G) ⊓ localOmegaModule T K : Subgroup G) = 2 := by
  have hc : Nat.card (localOmegaModule T K) = 16 := by
    rcases a.card with hc | hc
    · exact hc
    · exact False.elim (a.six_cubic_not_centralizes h hH hgen d hc hd)
  obtain ⟨hf,hq⟩ := a.four_geometry h d hc
  exact ⟨hc,hf,hq,a.four_omega_fixed_eq h d hc,a.four_omega_intersection_card_two h d hc⟩

/-- The completed FF reduction on the original universal Input leaves a
four-space whenever the witnessed cubic centralizes the original omega-center.
The local Cartan A₇-exclusion owner retains discharge of that source premise. -/
theorem localCartan_noncentral_four_of_cubic_centralizes
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T)
    (hd : D ≤ omegaCentralizer T) :
    ∃ K : Subgroup G, LocalA7Configuration T L H X K ∧
      Nat.card (localOmegaModule T K) = 16 ∧
      localOmegaModule T K ⊓ centralizer (residual H : Set G) = ⊥ ∧
      Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* alternatingGroup (Fin 7)) ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (residual H : Set G) =
        omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G) ⊓ localOmegaModule T K : Subgroup G) = 2 := by
  obtain ⟨K,a⟩ := localCartan_ffReduction T L W n h H hH hgen A B c Y hY X D d hXC
  exact ⟨K,a,a.four_of_cubic_centralizes h hH hgen d hd⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
