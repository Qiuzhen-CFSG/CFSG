module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.Projection
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.Consequences

/-!
# Connecting the projection to the standard configuration

Tight embedding and the relative normalizer equality of 16.4.2(1) give
`C_TC(r)=C_TC(R)` for every nonidentity `r∈R`. The chosen Δ₀ omega
containment makes `R₀ = R ∩ KL` nontrivial. These deductions construct the
projection configuration once the actual inner-factor and central-cover
containments have been supplied. They are preparatory results, not the
Sylow upgrade 16.4.10.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemmas 16.4.2 and 16.4.10, printed pp.1183 and 1192–1193.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections
open Subgroup
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- The inner-automorphism part `R₀` in 16.4.10. -/
def innerPart (L R : Subgroup G) : Subgroup G :=
  R ⊓ (centralizer (L : Set G) ⊔ L)

/-- Tight embedding makes every nonidentity element of `R` have the same
centralizer in `T_C`, once the relative normalizer identity 16.4.2(1) is supplied. -/
theorem IntersectionSetup.uniform_centralizers
    (h : IntersectionSetup T z L g R)
    (hn : commutingSylow T L ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) =
      commutingSylow T L ⊓ centralizer (R : Set G))
    {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    commutingSylow T L ⊓ centralizer ({r} : Set G) =
      commutingSylow T L ⊓ centralizer (R : Set G) := by
  apply le_antisymm
  · intro c hc
    rw [← hn]
    refine ⟨hc.1, h.normalizer_le (zpowers_ne_bot.mpr hr1) (zpowers_le.mpr hr) ?_⟩
    apply centralizer_le_normalizer
    apply mem_centralizer_iff.mpr
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    have hrc : Commute r c := mem_centralizer_iff.mp hc.2 r (by simp)
    exact (hrc.zpow_left n).eq
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hr))

/-- The inner part is nontrivial because it contains all involutions of `R`. -/
theorem IntersectionSetup.innerPart_ne_bot
    (h : IntersectionSetup T z L g R)
    (hOmega : omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L) :
    innerPart L R ≠ ⊥ := by
  have hn := h.sylow.ne_bot_of_even h.mem_delta.2.2
  have hd : 2 ∣ Nat.card R := by
    rcases h.sylow.isPGroup.card_eq_or_dvd with hc | hc
    · exact (hn (R.eq_bot_iff_card.mpr hc)).elim
    · exact hc
  have hOm := omega₁_map_subtype_ne_bot R 2 hd
  have hle : omegaOneAmbient R ≤ innerPart L R := le_inf (omegaOneAmbient_le R) hOmega
  intro he
  apply hOm
  exact eq_bot_iff.mpr (he ▸ hle)

/-- Connect the projection construction to the genuine intersection setup.
The center containment is the earlier two-cover input. The factor containment
must be supplied for the actual inner part, not for an unrelated tagged group. -/
theorem IntersectionSetup.projection_configuration
    (h : IntersectionSetup T z L g R)
    (hn : commutingSylow T L ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) =
      commutingSylow T L ⊓ centralizer (R : Set G))
    (hproper : commutingSylow T L ⊓ centralizer (R : Set G) < commutingSylow T L)
    (hOmega : omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L)
    (hfactors : innerPart L R ≤ commutingSylow T L ⊔ L)
    (hcenter : L ⊓ centralizer (L : Set G) ≤ commutingSylow T L) :
    SylowSymmetry.ProjectionConfiguration (commutingSylow T L) L (innerPart L R)
      (commutingSylow T L ⊓ centralizer (R : Set G)) where
  centralizes := inf_le_right
  factors := hfactors
  nontrivial := h.innerPart_ne_bot hOmega
  proper := hproper
  centralizers := fun _ ha ha1 => h.uniform_centralizers hn ha.1 ha1
  center_le := hcenter

end CFSG.Quasithin.Chapter16.Intersections
