module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.TorusSplitting
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four

/-!
# The original chosen-module U₄ Sylow splitting and remaining obstruction

The whole reduced module supplies every original prepared input. The torus
and Hall argument constructs a cyclic complement to T∩L, so a proper inner
Sylow supplies an actual outer involution even when the unitary exponent is
even. If T is inner the order comparison on the same marked extension gives
GlobalExit. Otherwise the same ambient normalizer-growth configuration remains.
Its nontrivial invariant long-root intersection is still to be proved.

Source: Aschbacher–Smith F.4.29(2),37–38, 5.3.3 and the Chapter12 application,
printed pp.289,293–294,659,795 of `refs/quasithin.pdf`. Both orientations,
ordinary and degree-two comparisons, q=4 and the full catalogue are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}
variable (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
include D h hmany hn hpsl hH d hp hm hc

/-- The literal original Sylow has a cyclic complement to its inner intersection. -/
theorem rankOne_unitaryFour_sylow_complement :
    ∃ B : Subgroup G, B ≤ (T : Subgroup G) ∧ Disjoint ((T : Subgroup G) ⊓ L) B ∧
      (T : Set G) = (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) * (B : Set G) ∧
      IsCyclic B ∧ Nat.card B = L.relIndex (T : Subgroup G) :=
  d.unitaryFour_sylow_complement
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc

/-- This supplies the outer involution needed by ambient normalizer growth. -/
theorem rankOne_unitaryFour_exists_outer_involution
    (hST : (T : Subgroup G) ⊓ L < (T : Subgroup G)) :
    ∃ t : T, orderOf t=2 ∧ t.val ∉ L :=
  d.unitaryFour_exists_outer_involution
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc hST

/-- Innerness of T discharges the order input on the same constructed extension. -/
theorem rankOne_unitaryFour_order_of_inner_sylow
    (hs : (T : Subgroup G) ⊓ L = (T : Subgroup G)) :
    Nat.card G = Nat.card
      (D.rankOne_unitaryFourNormalizerMarking h hmany hn hpsl hH d hp m hm hc).extension.carrier :=
  d.unitaryFour_order_of_inner_sylow
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc hs _

/-- The prepared chosen-module row has GlobalExit or the precise remaining
ambient fixed-root obstruction, with no outer-existence premise. -/
theorem rankOne_unitaryFour_globalExit_or_long_root_obstruction :
    1 < m ∧ n = 2*m ∧
    (RankOneModule.GlobalExit G ∨
    ∃ f : T, orderOf f=2 ∧ f.val ∉ L ∧ f.val ∉ residual H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      ∃ V : Subgroup G, IsPGroup 2 V ∧
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) < V ∧
        V ≤ centralizer ({f.val} : Set G) ∧
        V ≤ normalizer (((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ∧
        (∀ i : Fin 2, ¬ V ≤ normalizer (![L,residual H] i : Set G)) ∧
        (∀ B : Subgroup G, B ≤ (center (residual H)).map (residual H).subtype →
          V ≤ normalizer (B : Set G) → B=⊥) ∧
        let P := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
        let Z := (center P ⊓ _root_.commutator P).map P.subtype
        let B := Z ⊓ (center (residual H)).map (residual H).subtype
        Z ≤ ((T : Subgroup G) ⊓ L) ⊓ centralizer ({f.val} : Set G) ∧
          V ≤ normalizer (Z : Set G) ∧
          (V ≤ normalizer (B : Set G) → B=⊥)) := by
  obtain ⟨hm',hn',hcases⟩ := d.unitaryFour_recognition_or_long_root_obstruction
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc
  refine ⟨hm',hn',hcases.imp ?_ id⟩
  intro hh
  exact D.rankOne_globalExit_of_unitaryFour_constructed h hmany hn hpsl hH d hp m hm hc hh.1.le

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
