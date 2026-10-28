module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalDefs
public import CFSG.Quasithin.Chapter6.Section01.SourceBasic
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import Theory.GroupTheory.PGroup.OmegaCentralizerDetection
public import Theory.GroupTheory.TwoLocalCharacteristicControl

/-!
# Local placement and fixed spaces for the escaping Cartan component

The witness is a component relative to its local overgroup. Restricting
that component to its Sylow join and comparing two-cores puts it in the
actual local family. It therefore has a maximal local overcomponent.

The original rank-one component already satisfies source 1.2.7. If the
outside subgroup H centralizes the Sylow omega-center, this uniqueness
excludes every L-fixed central involution. The p-group center argument
then eliminates the fixed subgroup of the entire selected reduced module,
and hence of its literal commutator layer. No module marking is assumed.

Source: Aschbacher--Smith, 5.1.13, printed pp.637--638, using 1.2.7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

namespace LocalCartanWitness
variable {T : Sylow 2 G} {H A Y X D : Subgroup G}
  (d : LocalCartanWitness T H A Y X D)
include d

omit [Finite G] in
theorem sylow_normalizes (hTH : (T : Subgroup G) ≤ H)
    (hHY : H ≤ Y) : (T : Subgroup G) ≤ normalizer (X : Set G) :=
  (hTH.trans hHY).trans
    ((normal_subgroupOf_iff_le_normalizer d.component_le).mp d.component_normal)

omit [Finite G] in
theorem mem_localFamily (hTH : (T : Subgroup G) ≤ H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G)) :
    X ∈ Chapter1.L G (T : Subgroup G) := by
  have hJY : X ⊔ (T : Subgroup G) ≤ Y :=
    sup_le d.component_le (hTH.trans hY.2)
  refine ⟨d.component.subgroupOf_of_le le_sup_left hJY,
    ⟨T.subtype le_sup_right, ?_⟩, ?_⟩
  · simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]
  · intro hzero
    exact hY.1 (bot_unique
      ((pCoreIn_le_pCoreIn_of_sylow T le_sup_right hJY).trans_eq hzero))

theorem exists_maximal_local (hTH : (T : Subgroup G) ≤ H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G)) :
    ∃ K ∈ Chapter1.LStar G (T : Subgroup G), X ≤ K :=
  Chapter1.exists_mem_LStar_ge (d.mem_localFamily hTH hY)

theorem component_escape {M : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hTM : (T : Subgroup G) ≤ M)
    (hH : ¬ H ≤ M) : ¬ X ≤ M :=
  fun hX => residual_not_le T H M hTH hTM hH (d.residual_le.trans hX)

end LocalCartanWitness

namespace Input
variable {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}
  (h : Input KnownSimple.IsKnownSimple T L W n)
include h

theorem unique_local_join :
    ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (L : Set G) := by
  have hstar : L ∈ Chapter1.LStar G (T : Subgroup G) := by
    refine ⟨h.local_mem.1.prop, ?_⟩
    intro K hK hLK
    exact le_antisymm (h.local_mem.1.2 hK hLK) hLK
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hstar
  have he : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      h.sylow_normalizes) (le_componentOrbit L T)
  simpa only [he] using hu.normalizer_unique

theorem centralOmega_disjoint_of_outside_centralizes
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ omegaCentralizer T) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  apply eq_bot_iff.mpr
  intro z hz
  by_contra hzone
  have hz1 : z ≠ 1 := fun heq => hzone (mem_bot.mpr heq)
  have hzT := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz.1
  have hCC : omegaCentralizer T ≤ centralizer ({z} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr hz.1)
  obtain ⟨N, hCN, hN⟩ := Finite.exists_le_maximal
    (isTwoLocal_involution_centralizer (orderOf_eq_prime hzT.2.1 hz1))
  have hLC : L ≤ centralizer ({z} : Set G) := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hz.2 l hl)
  have hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hzT.2.2 t ht)
  have hNM := h.unique_local_join N hN ((sup_le hLC hTC).trans hCN)
  exact hH.1.2 (hNM ▸ hHC.trans (hCC.trans hCN))

theorem reduced_le_sylow : W ≤ (T : Subgroup G) := by
  obtain ⟨S, hS⟩ := h.local_mem.1.prop.2.1
  exact (reduced_le_core h.reduced).trans ((pCoreIn_le_sylow _ S).trans_eq hS)

theorem reduced_fixed_eq_bot_of_outside_centralizes
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ omegaCentralizer T) : W ⊓ centralizer (L : Set G) = ⊥ := by
  exact Subgroup.inf_centralizer_eq_bot_of_omega_disjoint T L W h.reduced.2.1
    h.reduced_le_sylow (le_sup_right.trans (reduced_normalizes h.reduced))
    h.sylow_normalizes (h.centralOmega_disjoint_of_outside_centralizes hH hHC)

theorem layer_fixed_eq_bot_of_outside_centralizes
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ omegaCentralizer T) :
    layer L W ⊓ centralizer (L : Set G) = ⊥ := by
  apply le_bot_iff.mp
  apply (inf_le_inf_right _ ?_).trans_eq
    (h.reduced_fixed_eq_bot_of_outside_centralizes hH hHC)
  exact le_normalizer_iff_commutator_le_left.mp
    (le_sup_left.trans (reduced_normalizes h.reduced))

end Input
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
