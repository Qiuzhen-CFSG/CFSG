module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.SmallModelExclusion.Local
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage
public import Theory.SpecificGroups.Tits.ReeLocalBlockOrders
public import Theory.SpecificGroups.Tits.RelativeSecondBlockLayers.SecondOrder
public import Theory.SpecificGroups.Tits.RelativeSylowMarking

/-!
# Excluding the Tits model from the selection

The checked Parrott--Atlas equivalence transports the component to the
concrete Atlas carrier. Sylow conjugacy preserves the specified local
intersection, so the exhaustive Sylow double-coset coverage puts that proper
subgroup in one of the two marked parabolics. Their proved orders, 10240 and
6144, are not divisible by nine; the full source shadow gives the contradiction.

Source: Aschbacher--Smith, initial parabolic selection, printed p.1139;
Parrott (1972), §5, p.683, for the concrete local presentation and geometry.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
open SmallModelExclusion
variable {G : Type*} [Group G] [Finite G]
variable {L MI Y S : Subgroup G} [L.Normal]
private instance component_normal : (centralizerQuotientComponent L).Normal :=
  (inferInstance : L.Normal).map (centralizerQuotientMap L) (QuotientGroup.mk'_surjective _)

/-- The actual Parrott Tits carrier is excluded by its checked Sylow-local geometry. -/
theorem Setup.not_tits (d : Setup L MI Y S) (hp : QuotientParabolic L MI S)
    (hm : Nonempty (centralizerQuotientComponent L ≃* Tits.ParrottGroup)) : False := by
  obtain ⟨e⟩ := hm
  let H := (MI.map (centralizerQuotientMap L)).subgroupOf (centralizerQuotientComponent L)
  obtain ⟨Q, hQ⟩ := local_sylow d.quotient_local
  obtain ⟨f, hf⟩ := Tits.RelativeSylowMarking.exists_sylow_marking
    (e.trans Tits.parrottFiniteImageEquiv) Q
  have hproper : H.map f.toMonoidHom ≠ ⊤ := by
    intro he
    apply local_proper d hp
    apply top_unique
    intro x _
    obtain ⟨y, hy, hxy⟩ := (show f x ∈ H.map f.toMonoidHom by rw [he]; trivial)
    exact f.injective hxy ▸ hy
  have hS : Tits.atlas1600SylowTwoSubgroup ≤ H.map f.toMonoidHom :=
    hf ▸ map_mono hQ
  have h9 : 9 ∣ Nat.card (H.map f.toMonoidHom) := by
    rw [card_map_of_injective f.injective]
    exact local_nine d.quotient_local (quotient_two d)
  rcases Tits.ConverseLocalCoverage.le_first_or_second _ hproper hS with h | h
  · have hd := h9.trans (card_dvd_of_le h)
    rw [Tits.ReeLocalBlockOrders.first_card] at hd
    norm_num at hd
  · have hd := h9.trans (card_dvd_of_le h)
    rw [Tits.RelativeSecondBlockLayers.second_card] at hd
    norm_num at hd


end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
