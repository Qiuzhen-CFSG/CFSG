module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Inputs
public import Theory.SpecificGroups.Alternating.SixSubgroupObstructions

/-!
# Transport for the exceptional fixed-component inspection

The model equivalence transports the automorphism and the embedded component
together. For a simple fixed model, subnormality forces a component to be the
whole group, so its order excludes A₆. These are the two component-calculus
steps used with the exceptional rows of Aschbacher–Smith 16.1.4, printed
p.1171, in the inspection in E.6.23, printed p.254 of `refs/quasithin.pdf`.
Neither lemma supplies an involution table or a smaller-field identification.
-/

public section
open Subgroup Theory.GroupTheory
open alternatingGroup.SixSubgroupObstructions
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo

/-- Transport the actor and its literal fixed component by the same equivalence. -/
theorem ExcludesFixedSix.of_equiv {D E : Type*} [Group D] [Group E]
    (e : D ≃* E) (hE : ExcludesFixedSix E) : ExcludesFixedSix D := by
  intro a ha S hS hs
  have hfixed : a.fixedSubgroup.map e.toMonoidHom =
      (MulAut.congr e a).fixedSubgroup := by
    ext x
    rw [mem_map_equiv, MulAut.mem_fixedSubgroup, MulAut.mem_fixedSubgroup]
    change a (e.symm x) = e.symm x ↔ e (a (e.symm x)) = x
    rw [← e.injective.eq_iff, e.apply_symm_apply]
  exact hE (MulAut.congr e a) (((MulAut.congr e).orderOf_eq a).trans ha)
    (S.map e.toMonoidHom) (hfixed ▸ hS.map e)
    (hs.map (fun f => (e.subgroupMap S).symm.trans f))

/-- In a simple group a component is the whole group; its order then excludes A₆. -/
theorem not_six_component_of_simple {D : Type*} [Group D] [IsSimpleGroup D]
    (hc : Nat.card D ≠ 360) (S : Subgroup D) (hS : IsComponent D S) :
    ¬ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  have he : Nat.card S = 360 := (Nat.card_congr e.toEquiv).trans card_six
  rcases hS.1.eq_bot_or_top_of_isSimpleGroup inferInstance with hb | ht
  · norm_num [hb, card_bot] at he
  · exact hc (by simpa only [ht, card_top] using he)

/-- Use an actual fixed-group isomorphism, retaining relative component membership. -/
theorem not_six_of_simple_fixed_model {D E : Type*} [Group D] [Group E]
    [IsSimpleGroup E] (hc : Nat.card E ≠ 360)
    (a : MulAut D) (e : a.fixedSubgroup ≃* E)
    (S : Subgroup D) (hS : IsComponentIn S a.fixedSubgroup) :
    ¬ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨f⟩
  exact not_six_component_of_simple hc _ (hS.2.map_equiv e)
    ⟨(e.subgroupMap (S.subgroupOf a.fixedSubgroup)).symm.trans
      ((subgroupOfEquivOfLe hS.1).trans f)⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo
