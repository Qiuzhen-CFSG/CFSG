module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSylowFrattini
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.PairedCentralizerSource
public import Theory.SpecificGroups.AlternatingSix.CommutingLocalRank
/-!
# The original component Sylow fixer kills a two-group Frattini subgroup

The small-model source constructs the actual component Sylow. Pointwise
fixers are inner by that Sylow except for A₆; a commuting conjugate excludes
A₆ by the proved quasithin local-rank obstruction. The literal normalizer
action therefore kills the actor's Frattini subgroup. The nonnormal source
wrapper supplies its commuting companion internally.

Source: Aschbacher--Smith 2.5.20, the third Sylow-conjugate argument, p.564.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
  {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
/-- Pointwise fixation of the original component Sylow kills the Frattini action. -/
theorem MathieuSourceSetup.commuting_sylow_fixer_frattini
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = L ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel L)
    (u : G) (hLu : L ≤ centralizer (L.conjBy u : Set G))
    (A : Subgroup G) (hpA : IsPGroup 2 A)
    (hAN : A ≤ normalizer (L : Set G))
    (hAP : A ≤ centralizer (((S : Subgroup H).map H.subtype ⊓ L : Subgroup G) : Set G)) :
    (frattini A).map A.subtype ≤ centralizer (L : Set G) := by
  have hm := MathieuSourceSetup.small_remaining_component c hG hempty hgen hb
  obtain ⟨P, hP⟩ := MathieuSourceSetup.exists_relative_component_sylow c
  let α : A →* MulAut L := L.normalizerMonoidHom.comp (inclusion hAN)
  have hfix : ∀ a x, x ∈ P → α a x = x := by
    intro a x hx
    apply Subtype.ext
    change (a : G) * (x : G) * (a : G)⁻¹ = x
    have hxY : (x : G) ∈ (S : Subgroup H).map H.subtype := by
      have hh : x ∈ ((S : Subgroup H).map H.subtype).subgroupOf L := hP ▸ hx
      exact hh
    rw [← hAP a.property x ⟨hxY, x.property⟩, mul_inv_cancel_right]
  rcases hm.alternatingSix_or_frattini_le_fixer_kernel hpA P α hfix with hA6 | hker
  · obtain ⟨e⟩ := hA6
    exact (alternatingGroup.not_commuting_a6_of_quasithin hG.quasithin L (L.conjBy u)
      e (((MulAut.conj u).subgroupMap L).symm.trans e) hLu).elim
  · rintro x ⟨a, ha, rfl⟩ k hk
    have hh := congrArg (fun b : MulAut L => (b ⟨k, hk⟩ : G)) (hker ha)
    change (a : G) * k * (a : G)⁻¹ = k at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
/-- A genuine nonnormal source component supplies the commuting companion. -/
theorem MathieuSourceSetup.nonnormal_sylow_fixer_frattini
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = L ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel L)
    (hn : ¬ (L.subgroupOf H).Normal)
    (A : Subgroup G) (hpA : IsPGroup 2 A)
    (hAN : A ≤ normalizer (L : Set G))
    (hAP : A ≤ centralizer (((S : Subgroup H).map H.subtype ⊓ L : Subgroup G) : Set G)) :
    (frattini A).map A.subtype ≤ centralizer (L : Set G) := by
  have hi := (source_component_normal_or_index_two hG.quasithin c.gamma
    ⟨c.component_le, c.component⟩).resolve_left hn
  obtain ⟨u, _, hc, _⟩ := TwoComponentCenter.exists_two_component_orbit
    H L c.component_le c.component S hi
  exact MathieuSourceSetup.commuting_sylow_fixer_frattini c hG hempty hgen hb u hc A hpA hAN hAP
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
