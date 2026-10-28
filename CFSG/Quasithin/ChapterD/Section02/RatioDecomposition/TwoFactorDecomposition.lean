module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.TransitivePair
/-!
# Literal decomposition with two factors

When the finite ratio decomposition has two indices and spans the full module,
its original embedded actors form an internal direct product and their original
supports are complementary. No reindexing or change of the action is needed.

Source: Aschbacher--Smith 15.1.2(3), printed p.1086.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)
namespace FactorData

theorem two_factor_literal_decomposition (hU : U = ⊤) (hc : Nat.card d.Index = 2) :
    ∃ i j : d.Index, i ≠ j ∧ (∀ k, k = i ∨ k = j) ∧
      (c.ambientFactor d i).actor ⊔ (c.ambientFactor d j).actor = K ∧
      Disjoint (c.ambientFactor d i).actor (c.ambientFactor d j).actor ∧
      (∀ x ∈ (c.ambientFactor d i).actor, ∀ y ∈ (c.ambientFactor d j).actor, Commute x y) ∧
      IsCompl (c.ambientFactor d i).space (c.ambientFactor d j).space := by
  obtain ⟨i,j,hij,hall⟩ := Nat.card_eq_two_iff.mp hc
  have hk (k : d.Index) : k = i ∨ k = j := by
    have hh : k ∈ ({i,j} : Set d.Index) := hall.symm ▸ Set.mem_univ k
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hh
  have hsup : (⨆ k, (c.ambientFactor d k).actor) = K := by
    simp only [ambientFactor,Factor.map_actor,embedding,←Subgroup.map_iSup,
      d.group_generation,←MonoidHom.range_eq_map,Subgroup.range_subtype]
  have hact : (c.ambientFactor d i).actor ⊔ (c.ambientFactor d j).actor = K := by
    apply Eq.trans _ hsup
    apply le_antisymm
    · exact sup_le (le_iSup (fun k => (c.ambientFactor d k).actor) i)
        (le_iSup (fun k => (c.ambientFactor d k).actor) j)
    · exact iSup_le fun k => by rcases hk k with rfl | rfl; exact le_sup_left; exact le_sup_right
  have hspace : (c.ambientFactor d i).space ⊔ (c.ambientFactor d j).space = ⊤ := by
    apply Eq.trans _ ((c.ambient_spaces_generate d).trans hU)
    apply le_antisymm
    · exact sup_le (le_iSup (fun k => (c.ambientFactor d k).space) i)
        (le_iSup (fun k => (c.ambientFactor d k).space) j)
    · exact iSup_le fun k => by rcases hk k with rfl | rfl; exact le_sup_left; exact le_sup_right
  refine ⟨i,j,hij,hk,hact,?_,?_,?_⟩
  · simpa only [ambientFactor,Factor.map_actor,embedding] using
      Subgroup.disjoint_map K.subtype_injective (d.actors_independent.pairwiseDisjoint hij)
  · intro x hx y hy
    simp only [ambientFactor,Factor.map_actor,embedding] at hx hy
    obtain ⟨x,hx,rfl⟩ := hx
    obtain ⟨y,hy,rfl⟩ := hy
    exact congrArg K.subtype (d.actors_commute c.faithful hij hx hy).eq
  · exact ⟨(c.ambient_spaces_independent d).pairwiseDisjoint hij,codisjoint_iff.mpr hspace⟩
end FactorData
end CFSG.Quasithin.ChapterD.RatioDecomposition
