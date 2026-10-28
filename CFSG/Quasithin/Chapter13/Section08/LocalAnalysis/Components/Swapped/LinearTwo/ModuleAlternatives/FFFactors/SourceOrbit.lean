module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.OrbitActor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.SourceSections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.ProductCoordinates
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The original component orbit in the maximal FF quotient

The source product equivalence and the actual PSL₂ identification make K₀*
centerless. The literal quotient H/O₂(H) has trivial two-core, and is generated
by K₀* and the image of the two-group T. Thus its component-orbit centralizer
is trivial. The maximal quotient remains nontrivial on that orbit, so its
action is faithful, and its offender actor contains the entire original K₀*.

These are actor comparisons preceding B.5.6; no classification branch or
natural/orthogonal module identification is assumed or concluded here.
The group-only orbit facts reused from F918Sections are independent of its
conditional representation dichotomy.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.16(1), printed p.952 (PDF p.969), and Hypothesis B.5.3, p.104.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
open ComponentSieve.AlternatingAndLinear.FourStructure

theorem center_eq_bot_of_square {A B : Type*} [Group A] [Group B]
    (e : A × A ≃* B) (hZ : center A = ⊥) : center B = ⊥ := by
  apply le_bot_iff.mp
  intro b hb
  have hx := ((Subgroup.centerCongr e).symm ⟨b, hb⟩).property
  have hz : center (A × A) = ⊥ := by simp [Subgroup.center_prod, hZ]
  change e.symm b ∈ center (A × A) at hx
  rw [hz, mem_bot] at hx
  exact e.symm.injective (hx.trans (map_one e.symm).symm)

variable {G : Type*} [Group G] [Finite G]

theorem source_orbit_centralizer (H K L₁ T : Subgroup G)
    (hH : H = conjugateSpanBy K T ⊔ (L₁ ⊔ T)) (hL : L₁ ≤ conjugateSpanBy K T)
    (hT : IsPGroup 2 T) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    (e : Source.starImage H K × Source.starImage H K ≃*
      Source.starImage H (conjugateSpanBy K T)) :
    centralizer (Source.starImage H (conjugateSpanBy K T) : Set (Source.Hstar H)) = ⊥ := by
  have hKH : K ≤ H := (le_conjugateSpanBy K T).trans (by rw [hH]; exact le_sup_left)
  have hTH : T ≤ H := by rw [hH]; exact le_sup_right.trans le_sup_right
  have he := F918Sections.star_conjugateSpan H K T hKH hTH
  have hgen := F918Sections.star_actor_generated H K L₁ T hH hL
  have ht : IsPGroup 2 (Source.starImage H T) :=
    (hT.of_equiv (subgroupOfEquivOfLe hTH).symm).map (QuotientGroup.mk' (pCore 2 H))
  have hz := center_eq_bot_of_square e (center_eq_bot_of_psl2 hmodel)
  rw [he] at hgen hz ⊢
  exact centralizer_orbit_eq_bot _ _ hgen ht hz (pCore_quotient_pCore_eq_bot 2)

section Section
variable (H V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (ChiefFactors.SourceSpace H V₃ V₁))
    (hρ : ChiefFactors.IsSourceAction H V₃ V₁ ρ)

include hρ

theorem source_section_actor_comparison
    (K L₁ T : Subgroup G)
    (hH : H = conjugateSpanBy K T ⊔ (L₁ ⊔ T)) (hL : L₁ ≤ conjugateSpanBy K T)
    (hK : (K.subgroupOf H).IsCComponent)
    (hq : IsQuasisimple (Source.starImage H K)) (hT : IsPGroup 2 T)
    {n : ℕ} (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    (e : Source.starImage H K × Source.starImage H K ≃*
      Source.starImage H (conjugateSpanBy K T))
    (hLN : L₁ ≤ normalizer (V₃ : Set G)) (hline : V₁ ≤ V₃)
    (hseed : V₃ ≤ ⁅L₁, V₃⁆ ⊔ V₁)
    (W : Subrepresentation ρ)
    (hW : ¬ subspaceCommutator ρ ⊤ (Source.starImage H (conjugateSpanBy K T)) ≤ W.toSubmodule)
    (hmax : ∀ Y : Subrepresentation ρ, W ≤ Y →
      ¬ subspaceCommutator ρ ⊤ (Source.starImage H (conjugateSpanBy K T)) ≤ Y.toSubmodule → Y = W)
    (hff : IsFFModule (imageRepresentation W.quotientRepresentation)) :
    Function.Injective W.quotientRepresentation ∧
      actionSubgroup W.quotientRepresentation (Source.starImage H (conjugateSpanBy K T)) ≤
        offenderActor (imageRepresentation W.quotientRepresentation) := by
  have hfull := source_moved_eq_top H V₃ V₁ ρ hρ K L₁ T hH hL hLN hline hseed
  let : W.quotientRepresentation.IsIrreducible :=
    maximal_component_section_irreducible ρ W _ hfull hW hmax
  let : Module.Finite (ZMod 2) (ChiefFactors.SourceSpace H V₃ V₁) := Module.Finite.of_finite
  have hc := source_orbit_centralizer H K L₁ T hH hL hT hmodel e
  have hKH : K ≤ H := (le_conjugateSpanBy K T).trans (by rw [hH]; exact le_sup_left)
  have hTH : T ≤ H := by rw [hH]; exact le_sup_right.trans le_sup_right
  have he := F918Sections.star_conjugateSpan H K T hKH hTH
  have hcomp := F918Sections.star_isComponent H K hK hq
  have hqfull := quotient_full_commutator ρ W _ hfull
  rw [he] at hc hqfull ⊢
  have hn : ¬ ∀ l ∈ conjugateSpanBy (Source.starImage H K) (Source.starImage H T),
      ∀ v, W.quotientRepresentation l v = v := by
    intro hall
    have hz : subspaceCommutator W.quotientRepresentation ⊤
        (conjugateSpanBy (Source.starImage H K) (Source.starImage H T)) = ⊥ := by
      apply (subspaceCommutator_eq_bot_iff _ _ _).mpr
      intro v _ l
      exact hall l l.property v
    exact top_ne_bot (α := Subrepresentation W.quotientRepresentation)
      (Subrepresentation.toSubmodule_injective (hqfull.symm.trans hz))
  exact ⟨orbit_action_faithful _ _ _ hcomp hc hn,
    orbit_image_le_offender _ _ _ hcomp hc hff⟩

end Section
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
