module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNaturalFixed
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalFourReduction
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.CharacteristicControl

/-!
# The original omega-center inside the Cartan four-space

Reselect the actual left omega-span and apply the natural cubic fixed-space
identity. Every omega-vector fixed by the right component is then fixed by
L and by the original residual, so local uniqueness kills this fixed
supplement. The source omega-span splitting puts omega in the four-space.
The previously proved Sylow fixed-line calculation gives its order two;
the original residual has no fixed point there.

This supplies the fixed-space premise for the subsequent block comparison.
The block exclusions and torus contradiction remain necessary.
Source: Aschbacher–Smith 5.1.13, printed pp.637–638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The original cubic and L have the same fixed subgroup on omega.
Reselecting the omega-span handles an arbitrary original W. -/
theorem LocalA7Configuration.omega_cubic_fixed_eq_left
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (D : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) := by
  have hDL := ((d.cubic_le.trans inf_le_left).trans c.left_le).trans inf_le_left
  apply le_antisymm ?_ (inf_le_inf_left _ (centralizer_le hDL))
  by_cases hLC : L ≤ omegaCentralizer T
  · exact le_inf inf_le_left (inf_le_left.trans (le_centralizer_iff.mp hLC))
  have hs := h.omega_span_input hLC
  have hn : D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
    (le_sup_right.trans le_sup_left).trans
      (a.four_cubic_normalizes_thompson h hH hgen c d (a.four h hH hgen c d))
  have he := hs.cubic_fixed_eq_of_normalizes_thompson (a.left_thompson_moves hs) hDL d.cubic_card hn
  intro z hz
  exact ⟨hz.1,(he.le ⟨le_conjugateSpanBy _ _ hz.1,hz.2⟩).2⟩

/-- Local uniqueness kills the component-fixed supplement of omega. -/
theorem LocalA7Configuration.omega_component_fixed_eq_bot
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G) = ⊥ := by
  have hDK := (d.cubic_le.trans inf_le_right).trans a.contains
  have he := a.omega_cubic_fixed_eq_left h hH hgen c d
  apply bot_unique
  intro z hz
  apply (h.omega_common_fixed_eq_bot hH).le
  exact ⟨he.le ⟨hz.1,centralizer_le hDK hz.2⟩,centralizer_le (d.residual_le.trans a.contains) hz.2⟩

/-- The original omega-center lies in the four-space; its order is two,
and the original residual has no fixed point on it. -/
theorem LocalA7Configuration.omega_four_geometry
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    omegaOneCenterAmbient (T : Subgroup G) ≤ localOmegaModule T K ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2 ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (residual H : Set G) = ⊥ := by
  have hc := a.four h hH hgen c d
  have hzero := a.omega_component_fixed_eq_bot h hH hgen c d
  have hZ : omegaOneCenterAmbient (T : Subgroup G) ≤ localOmegaModule T K := by
    have he := a.span_eq
    rw [hzero,sup_bot_eq] at he
    exact (le_conjugateSpanBy _ _).trans_eq he
  refine ⟨hZ,?_,?_⟩
  · have hh := a.four_omega_intersection_card_two h d hc
    rwa [inf_eq_left.mpr hZ] at hh
  · rw [a.four_omega_fixed_eq h d hc,hzero]

/-- The original noncentral source inputs supply the four-space and the
literal residual-fixed-point vanishing, with no extra module premise. -/
theorem localCartan_noncentral_omega_four
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K : Subgroup G, LocalA7Configuration T L H X K ∧
      Nat.card (localOmegaModule T K) = 16 ∧
      omegaOneCenterAmbient (T : Subgroup G) ≤ localOmegaModule T K ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2 ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (residual H : Set G) = ⊥ := by
  obtain ⟨K,a⟩ := localCartan_ffReduction T L W n h H hH hgen A B c Y hY X D d hXC
  exact ⟨K,a,a.four h hH hgen c d,a.omega_four_geometry h hH hgen c d⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
