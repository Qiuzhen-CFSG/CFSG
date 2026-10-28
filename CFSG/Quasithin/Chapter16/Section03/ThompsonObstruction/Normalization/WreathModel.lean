module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Normalization.Normality
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Normalization.WreathModel.Splitting
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Normalization.WreathModel.WreathFactor
public import Theory.GroupTheory.MarkedInternalProduct
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The marked local wreath model

The local Sylow splits as P = ⟨t⟩ × Q, where Q = (P ∩ K)⟨z⟩ is an actual
Sylow two-subgroup in the marked S₈ extension. The splitting is proved from
the conjugation action on K ≃ A₈ and its given centralizer, while Q is
identified with the binary-tree Sylow and hence with D₈ wreath C₂.
The resulting isomorphism preserves both specified subgroup factors exactly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, completion of
the proof of Theorem 16.3.7, printed p.1182 / PDF p.1199.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The chosen local Sylow has the actual wreath model, with both marked factors. -/
theorem Selected.exists_marked_model (s : Selected T z t L) :
    ∃ e : localSylow s.P ≃* LocalSylowModel,
      ((zpowers t).subgroupOf (localSylow s.P)).map e.toMonoidHom =
        (⊤ : Subgroup (Multiplicative (ZMod 2))).prod ⊥ ∧
      (((localSylow s.P ⊓ enlargement t L) ⊔ zpowers z).subgroupOf
        (localSylow s.P)).map e.toMonoidHom =
        (⊥ : Subgroup (Multiplicative (ZMod 2))).prod ⊤ := by
  obtain ⟨e, hA, hB⟩ := exists_marked_internalProductEquiv
    (localSylow s.P) (zpowers t) ((localSylow s.P ⊓ enlargement t L) ⊔ zpowers z)
    s.centralFactor_sup_wreathFactor s.centralFactor_disjoint_wreathFactor
    s.centralFactor_centralizes_wreathFactor
  let eA : zpowers t ≃* Multiplicative (ZMod 2) := mulEquivOfCyclicCardEq (by
    rw [Nat.card_zpowers, s.counterexample.involution]
    norm_num [Nat.card_eq_fintype_card])
  let eB := s.wreathFactorEquiv
  refine ⟨e.trans (eA.prodCongr eB), ?_, ?_⟩
  · change ((zpowers t).subgroupOf (localSylow s.P)).map
      ((eA.prodCongr eB).toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map, hA, map_equiv_eq_comap_symm']
    ext x
    simp only [mem_comap, mem_prod, mem_top, mem_bot, true_and]
    change eB.symm x.2 = 1 ↔ x.2 = 1
    exact eB.symm.map_eq_one_iff
  · change (((localSylow s.P ⊓ enlargement t L) ⊔ zpowers z).subgroupOf
      (localSylow s.P)).map ((eA.prodCongr eB).toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map, hB, map_equiv_eq_comap_symm']
    ext x
    simp only [mem_comap, mem_prod, mem_top, mem_bot, and_true]
    change eA.symm x.1 = 1 ↔ x.1 = 1
    exact eA.symm.map_eq_one_iff

end CFSG.Quasithin.Chapter16.ThompsonObstruction
