module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Selection
public import CFSG.Quasithin.ChapterC.Section01.BlockDefs

/-!
# The common source configuration for the remaining 4.3.2 branches

This interface records the simultaneous choices in the opening of 4.3.2 and
4.3.3–5: the maximal intermediate I, the same outside H and its full Sylow
intersection, the escaping C-component containing L, and the crossing element.
The full module is always [Ω₁Z(O₂(LT)),L], not the chosen Chapter 12 module.
All normality and quotient statements refer to these actual subgroups.

Construction of this configuration from failure of uniqueness still requires
the rank-one instance of 4.2.12 and the simultaneous maximal choices. Excluding
its ordinary component is 4.3.6, its block component is 4.3.7, and its
remaining constrained component is 4.3.8–16 and the final contradiction.
The conditional assembly below records these four independent obligations
and does not assert 4.3.2.

Source: Aschbacher–Smith, printed pp.613–618.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]

/-- Exact shared subgroups at the start of the ordinary/constrained split.
No classification conclusion, module model or uniqueness over L is a field. -/
structure SourceConfiguration (T : Sylow 2 G) (L : Subgroup G) where
  I : Subgroup G
  H : Subgroup G
  K : Subgroup H
  t : G
  le_I : L ≤ I
  I_le : I ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2
  I_maximal : ∀ J : Subgroup G, I < J →
    J ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
    UniqueMaximalOvergroup J (normalizer (L : Set G))
  I_eq : I = L ⊔ I.pCoreIn 2
  core_intersection : I.pCoreIn 2 = I ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2
  maximal : IsMaximalTwoLocal H
  I_le_H : I ≤ H
  outside : ¬ H ≤ normalizer (L : Set G)
  c28 : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
    (H ⊓ normalizer (L : Set G)) L (I.pCoreIn 2)
    (Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2))
  component : K.IsCComponent
  quotient : IsQuasisimple (K ⧸ pCore 2 K)
  le_component : L ≤ K.map H.subtype
  component_outside : ¬ K.map H.subtype ≤ normalizer (L : Set G)
  component_normal : K.Normal
  component_cases : IsComponent H K ∨ generalizedFitting K = pCore 2 K
  normalizer_component : H = normalizer (K.map H.subtype : Set G)
  sylow_strict : (T : Subgroup G) ⊓ H < (T : Subgroup G)
  sylow : ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = (T : Subgroup G) ⊓ H
  normalizer_sylow : normalizer ((T : Subgroup G) ⊓ H : Set G) ≤ normalizer (L : Set G)
  strict_unique : ∀ X : Subgroup G, (T : Subgroup G) ⊓ H < X → X ≤ (T : Subgroup G) →
    UniqueMaximalOvergroup (L ⊔ X) (normalizer (L : Set G))
  core_sylow : I.pCoreIn 2 = ((T : Subgroup G) ⊓ H) ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2
  core_join : I.pCoreIn 2 = (I ⊔ ((T : Subgroup G) ⊓ H)).pCoreIn 2
  crossing_mem : t ∈ (T : Subgroup G)
  crossing_outside : t ∉ (T : Subgroup G) ⊓ H
  crossing_normalizes : t ∈ normalizer ((T : Subgroup G) ⊓ H : Set G)
  crossing_square : t ^ 2 ∈ (T : Subgroup G) ⊓ H
  crossing_core : I.pCoreIn 2 < (L ⊔ (T : Subgroup G)).pCoreIn 2 →
    t ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧ t ^ 2 ∈ I.pCoreIn 2

/-- The shared source choices imply the normalizer control used in both
component branches of 4.3.5. -/
theorem SourceConfiguration.crossing_normalizer_control {T : Sylow 2 G} {L : Subgroup G}
    (c : SourceConfiguration T L) {W : Subgroup G} (hW : IsPGroup 2 W) (hne : W ≠ ⊥)
    (hn : L ⊔ ((T : Subgroup G) ⊓ c.H ⊔ zpowers c.t) ≤ normalizer (W : Set G)) :
    normalizer (W : Set G) ≤ normalizer (L : Set G) := by
  have hs : (T : Subgroup G) ⊓ c.H < (T : Subgroup G) ⊓ c.H ⊔ zpowers c.t := by
    apply lt_of_le_of_ne le_sup_left
    intro he
    have ht : c.t ∈ (T : Subgroup G) ⊓ c.H ⊔ zpowers c.t :=
      (le_sup_right : zpowers c.t ≤ (T : Subgroup G) ⊓ c.H ⊔ zpowers c.t) (mem_zpowers c.t)
    exact c.crossing_outside (he.ge ht)
  have hu := c.strict_unique _ hs (sup_le inf_le_left (zpowers_le.mpr c.crossing_mem))
  exact normalizer_le_of_unique_maximalTwoLocal hu.2.2 hW hne hn

omit [Finite G] in
/-- Conditional assembly only: construction and all three source exclusions must
be proved before this yields original 4.3.2. -/
theorem uniqueness_of_source_exclusions {T : Sylow 2 G} {L : Subgroup G}
    (hselect : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G)) →
      Nonempty (SourceConfiguration T L))
    (hordinary : ∀ c : SourceConfiguration T L, IsComponent c.H c.K → False)
    (hblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ChapterC.IsBlock c.K → False)
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False) :
    ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G) := by
  have hu : UniqueMaximalOvergroup L (normalizer (L : Set G)) := by
    by_contra hn
    obtain ⟨c⟩ := hselect hn
    rcases c.component_cases with ho | hc
    · exact hordinary c ho
    · by_cases hb : ChapterC.IsBlock c.K
      · exact hblock c hc hb
      · exact hnonblock c hc hb
  exact hu.2.2

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
