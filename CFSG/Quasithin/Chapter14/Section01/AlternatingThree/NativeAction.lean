module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.CubicPairMarking
public import Theory.SpecificGroups.Alternating.FourPairInnerAction
public import Theory.SpecificGroups.Alternating.FourPairThompson.Core
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The original block and Thompson subgroup in native wreath coordinates

The faithful conjugation action is marked using the two actual Sylow
conjugate blocks. Its image contains the alternating base and contains a
factor-swapping actor. The native elementary sixteen-group pulls back to
a normal two-subgroup, hence lies in the original two-core and then in R.
Injectivity preserves the original Thompson subgroup and movement identity.

This supplies the literal finite-model input of Aschbacher--Smith 14.1.10,
printed p.978. No automorphism-surjectivity or Thompson containment is
assumed in this transport.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.AlternatingThree
open AlternatingFourPair
variable {G : Type*} [Group G] [Finite G]

/-- Every native hypothesis is produced from the same original block, core, Sylow and action. -/
theorem faithful_pair_native_action
    (hf : generalizedFitting G = pCore 2 G) (hr : primeRank 3 G ≤ 2)
    (S : Sylow 2 G) (X R : Subgroup G) (hb : ChapterC.IsBlock X)
    (ha : ChapterC.IsAlternatingBlock X 3) (hQR : pCore 2 G ≤ R)
    (hm : X = ⁅X,elementaryAbelianMaxJ R⁆)
    (hn : (conjugateSpanBy X (S : Subgroup G)).Normal)
    (hcard : Nat.card (conjugateSpanBy X (S : Subgroup G)) = 144)
    (hc : centralizer (conjugateSpanBy X (S : Subgroup G) : Set G) = ⊥) :
    ∃ f : G →* W, Function.Injective f ∧
      Thompson.alternatingBase ≤ f.range ∧ ¬ f.range ≤ Thompson.base ∧
      Thompson.kleinBase ≤ R.map f ∧ Nat.card (X.map f) = 12 ∧
      X.map f = ⁅X.map f,elementaryAbelianMaxJ (R.map f)⁆ := by
  let N := conjugateSpanBy X (S : Subgroup G)
  let : N.Normal := hn
  obtain ⟨t,_,e,hX,hY⟩ := ChapterC.RankOne.ChiProduct.cubic_pair_marking hf hr S X hb ha hcard
  let f := normalPairAction N e
  have hi : Function.Injective f := normalPairAction_injective N e hc
  have hAlt : Thompson.alternatingBase ≤ f.range := by
    rw [←map_inner_eq_alternatingBase,←normalPairAction_map_self N e]
    exact map_le_range f N
  have htrans : ¬ f.range ≤ Thompson.base := by
    intro hle
    have hw : f (t : G) ∈ Thompson.base := hle ⟨t,rfl⟩
    have hh := normalPairAction_map_conjugate N X (le_conjugateSpanBy X _) e (t : G)
    rw [hX,hY] at hh
    exact axis0_ne_axis1 ((map_axis0_of_mem_base _ hw).symm.trans hh)
  have hKR : Thompson.kleinBase ≤ R.map f := by
    have hp : IsPGroup 2 (Thompson.kleinBase.comap f) :=
      (IsElementaryAbelian.isPGroup 2 Thompson.kleinBase).comap_of_injective f hi
    have hKQ : Thompson.kleinBase.comap f ≤ pCore 2 G := le_sSup ⟨inferInstance,hp⟩
    have hh : (Thompson.kleinBase.comap f).map f = Thompson.kleinBase :=
      map_comap_eq_self (Thompson.kleinBase_le_alternatingBase.trans hAlt)
    exact hh ▸ map_mono (f := f) (hKQ.trans hQR)
  refine ⟨f,hi,hAlt,htrans,hKR,?_,?_⟩
  · obtain ⟨eX⟩ := ha.equiv_alternatingFour
    rw [card_map_of_injective hi,Nat.card_congr eX.toEquiv]
    exact alternatingGroup.card_of_card_eq_four (by norm_num)
  · have hh := congrArg (map f) hm
    rwa [map_commutator,←elementaryAbelianMaxJ_map_injective f hi] at hh

end CFSG.Quasithin.Chapter14.AlternatingThree
