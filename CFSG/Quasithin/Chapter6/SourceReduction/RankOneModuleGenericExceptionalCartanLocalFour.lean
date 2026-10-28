module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FourGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.CharacteristicControl
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.Complete

/-!
# Four-space geometry in the original local Cartan contradiction

The completed FF reduction gives the original A₇ configuration. In its
four-dimensional alternative the residual has no fixed vectors, its fixed
subgroup on omega equals that of the overcomponent, and the whole Sylow
join has A₇ two-core quotient. The actual omega intersection is the fixed
line of order two. Uniqueness also rules out the common
characteristic-subgroup alternative for the original two components.
The six-dimensional comparison, both block cases and torus inversion
remain with the universal local Cartan owner.

Source: Aschbacher–Smith 5.1.13, printed pp.637–638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The original FF witness, with its four-space branch identified on the
literal residual action and the whole local two-core quotient. -/
theorem localCartan_noncentral_four_or_six
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K : Subgroup G, LocalA7Configuration T L H X K ∧
      ((Nat.card (localOmegaModule T K) = 16 ∧
        localOmegaModule T K ⊓ centralizer (residual H : Set G) = ⊥ ∧
        Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
          pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* alternatingGroup (Fin 7)) ∧
        omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (residual H : Set G) =
          omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G) ∧
        Nat.card (omegaOneCenterAmbient (T : Subgroup G) ⊓ localOmegaModule T K : Subgroup G) = 2) ∨
      Nat.card (localOmegaModule T K) = 64) := by
  obtain ⟨K,a⟩ := localCartan_ffReduction T L W n h H hH hgen A B c Y hY X D d hXC
  refine ⟨K,a,?_⟩
  rcases a.card with hc | hc
  · have hc' : Nat.card (localOmegaModule T K) = 16 := hc
    obtain ⟨hf,hq⟩ := a.four_geometry h d hc'
    exact Or.inl ⟨hc',hf,hq,a.four_omega_fixed_eq h d hc',
      a.four_omega_intersection_card_two h d hc'⟩
  · exact Or.inr hc

/-- Even before identifying the left module, the fixed subgroups of L
and the A₇ overcomponent have trivial intersection in the omega-center. -/
theorem LocalA7Configuration.omega_common_fixed_eq_bot
    {T : Sylow 2 G} {L W H X K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A Y D : Subgroup G} (d : LocalCartanWitness T H A Y X D) :
    (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓
      centralizer (K : Set G) = ⊥ := by
  apply bot_unique
  exact (inf_le_inf_left _ (centralizer_le (d.residual_le.trans a.contains))).trans_eq
    (h.omega_common_fixed_eq_bot hH)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
