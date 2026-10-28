module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.Basic
public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.HigherLinear
public import Theory.SpecificGroups.SymmetricEight.ComponentMarking
public import Theory.SpecificGroups.SymmetricEight.EvenPairCentralizer

/-!
# The PSL₄(2)–A₆ pair fixer

The concrete PSL₄(2) ≃ A₈ comparison and the component-centralizing
involution identify the actual embedded A₆ with the even permutations on
six points. Its full permutation centralizer has order at most two.
The proved S₈ ≃ Aut(A₈) action transfers this bound to Aut(I).
Thus the result controls all automorphisms fixing the embedded component,
without assuming a conjugacy class of A₆ embeddings or a graph label.

Source: Aschbacher–Smith, 16.1.7(3e) and the sieve in 16.3.5, combined
manuscript of 1 March 2004, printed pp.1172 and 1178–1179.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] {E L I : Subgroup G} {t i : G}

/-- The full fixer of the actual A₆ component in a PSL₄(2) enlargement. -/
theorem pairFixer_card_le_two_psl4 (h : PairContext E L I t i)
    (hlarge : ClassicalGroup.IsPSL I 4 2)
    (hsmall : Nonempty (L ≃* alternatingGroup (Fin 6))) :
    Nat.card (pairFixer L I) ≤ 2 := by
  obtain ⟨es⟩ := hsmall
  have hcard : Nat.card L = 360 := by
    rw [Nat.card_congr es.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  obtain ⟨f, _, hI, hL⟩ :=
    Theory.SpecificGroups.SymmetricEight.ComponentMarking.exists_marked_equiv
      (LiePreliminaries.higherLinearFourAlternatingEquiv hlarge)
      (h.normalizes h.t_mem) h.setup.involution_t h.proper h.component_in_centralizer hcard
  let e : I ≃* alternatingGroup (Fin 8) :=
    ((subgroupOfEquivOfLe (le_sup_left : I ≤ I ⊔ zpowers t)).symm.trans
      (f.subgroupMap (I.subgroupOf (I ⊔ zpowers t)))).trans (MulEquiv.subgroupCongr hI)
  have hmap : (L.subgroupOf I).map
      ((alternatingGroup (Fin 8)).subtype.comp e.toMonoidHom) =
      Theory.SpecificGroups.SymmetricEight.EvenPairCentralizer.evenPair := by
    change _ = alternatingGroup (Fin 8) ⊓ _
    rw [← hL]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, mem_sup_left x.property⟩, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, h.proper.le hx⟩, hx, rfl⟩
  exact Theory.SpecificGroups.SymmetricEight.EvenPairCentralizer.automorphismFixer_card_le_two
    e (L.subgroupOf I) hmap

/-- The PSL₄(2) branch of the strict bound required by `LieBounds.graph_binary`. -/
theorem pairFixer_card_lt_four_psl4 (h : PairContext E L I t i)
    (hlarge : ClassicalGroup.IsPSL I 4 2)
    (hsmall : Nonempty (L ≃* alternatingGroup (Fin 6))) :
    Nat.card (pairFixer L I) < 4 :=
  (pairFixer_card_le_two_psl4 h hlarge hsmall).trans_lt (by decide)

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
