module

public import CFSG.Quasithin.ChapterJ.Section05.SourceGeometry.Source
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Maximal

/-!
# The original second point stabilizer and its derived intersection

Orbit--stabilizer gives the actual second F-stabilizer order15600 from the
unchanged Rudvalis action. The marking into the full binary Ree group then
transports native maximality and the exact normalizer of its intersection
with F′. The latter subgroup has order7800. These are the primitive-second-
suborbit and socle-normalizer inputs used in source J.5.6 and J.5.5(5).

Source: Aschbacher--Smith J.5.4--6, printed pp.446--447. No maximality or
normalizer conclusion is assumed on the original source stabilizer.
-/

public section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
variable {G:Type*} [Group G] {F:Subgroup G} {δ γ:Cosets F}
  (h:RudvalisAction F δ γ)
include h

private theorem second_card : Nat.card (stabilizer F γ)=15600 := by
  have hc:=Nat.card_congr (orbitProdStabilizerEquivGroup F γ)
  rw [Nat.card_prod,h.second_length] at hc
  have hf : Nat.card F=35942400 :=
    (Nat.card_congr h.marking.toEquiv).trans Tits.ExceptionalParabolics.FullRee.group_card
  rw [hf] at hc
  omega

private theorem second_map_card :
    Nat.card ((stabilizer F γ).map h.marking.toMonoidHom)=15600 := by
  rw [card_map_of_injective h.marking.injective,h.second_card]

/-- The unchanged second source stabilizer is maximal in the unchanged F. -/
theorem second_stabilizer_isCoatom : IsCoatom (stabilizer F γ) := by
  have hm := Tits.ExceptionalParabolics.FullRee.FiveOvergroups.isCoatom_of_card
    ((stabilizer F γ).map h.marking.toMonoidHom) h.second_map_card
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨?_,fun K hK hle=>?_⟩
  · intro he
    apply hm.1
    rw [he,map_top_of_surjective _ h.marking.surjective]
  · have hmap : K.map h.marking.toMonoidHom≠⊤ := by
      intro he
      apply hK
      apply map_injective (f:=h.marking.toMonoidHom) h.marking.injective
      rw [he,map_top_of_surjective _ h.marking.surjective]
    have hh := (isCoatom_iff_ge_of_le.mp hm).2 _ hmap (map_mono hle)
    intro k hk
    obtain ⟨x,hx,he⟩ := hh (mem_map_of_mem h.marking.toMonoidHom hk)
    exact h.marking.injective he ▸ hx

private theorem intersection_map :
    (stabilizer F γ⊓commutator F).map h.marking.toMonoidHom =
      (stabilizer F γ).map h.marking.toMonoidHom⊓commutator (ReeF4.Model 0) := by
  rw [map_inf _ _ _ h.marking.injective,map_commutator_eq,
    MonoidHom.range_eq_top.mpr h.marking.surjective,← _root_.commutator_def]

/-- The literal intersection with F′ has the native socle order. -/
theorem second_intersection_card : Nat.card (stabilizer F γ⊓commutator F : Subgroup F)=7800 := by
  rw [←card_map_of_injective (f:=h.marking.toMonoidHom) h.marking.injective,h.intersection_map]
  exact Tits.ExceptionalParabolics.FullRee.FiveOvergroups.intersection_card_of_card _ h.second_map_card

/-- The full F-normalizer of the actual second-stabilizer intersection with F′. -/
theorem second_intersection_normalizer :
    normalizer ((stabilizer F γ⊓commutator F : Subgroup F):Set F)=stabilizer F γ := by
  apply map_injective (f:=h.marking.toMonoidHom) h.marking.injective
  rw [map_normalizer_eq_of_bijective _ h.marking.bijective,h.intersection_map]
  exact Tits.ExceptionalParabolics.FullRee.FiveOvergroups.normalizer_intersection_of_card _ h.second_map_card
end CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
