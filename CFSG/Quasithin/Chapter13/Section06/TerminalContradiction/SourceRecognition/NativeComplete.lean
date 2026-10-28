module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.F916Complete
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.SourceStrictBound

/-!
# The marked A₅ terminal contradiction from proved source module bounds

The original A₅ context supplies the abelian closure, 13.5.7 family and
third-space normalizer. The proved F.9 construction gives a quadratic actor
of ratio at most two on U_H/V₁. Native source recognition for PSL₃(4), M₂₃
and J₂ gives the strict opposite inequality on that same quotient action.
No F.9 or B.4 classification callback remains.

The original compatible coordinates, fusion, nonsingular centralizer bound,
component conclusion, and genuine earlier A.3.12 input are retained. This
is the terminal source argument and does not assert all earlier parts of 13.6.1.
Source: Aschbacher–Smith 13.5.7, 13.6.2 and terminal 13.6, pp.917,926,935.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Ratio Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original marked A₅ terminal argument with closure and F.9 setup supplied. -/
theorem terminal_contradiction_of_marked_A5_native
    (d : Context T L V V₁ V₂ V₃)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
    (coordinates : FiveCoordinates V) (v z : V)
    (hv : BinaryPermutation.FiveGeometry.form (coordinates.equiv v).toAdd ≠ 0)
    (hz : z ≠ 1) (hzline : zpowers z.val = V₁)
    (hqz : BinaryPermutation.FiveGeometry.form (coordinates.equiv z).toAdd = 0)
    (hAlt : alternatingGroup (Fin 5) ≤ coordinates.actor.range)
    (hfusion : ∀ x : V, x ≠ 1 → ∀ a : G, MulAut.conj a x.val ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n x.val = MulAut.conj a x.val)
    (hCv : centralizer ({v.val} : Set G) ≤ normalizer (V : Set G))
    (hmark : ∀ x : V, x.val ∈ V₃ ↔ (coordinates.equiv x).toAdd.val 4 = 0)
    (houtside : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hcounter : CentralizerReduction.IsA5Counterexample G)
    (hcomponents : Components.Conclusion
      ((T : Subgroup G).subgroupOf (centralizer ({z.val} : Set G)))) : False := by
  have hc : centralizer (V₁ : Set G) = centralizer ({z.val} : Set G) := by
    rw [←hzline, zpowers_eq_closure, centralizer_closure]
  let := SourceAbelian.source_closure_abelian d hA312 z.val hzline houtside hcounter
  have hT : (T : Subgroup G) ≤ centralizer ({z.val} : Set G) := by
    rw [←hc]
    exact d.flag.one_invariant.trans
      (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
  have hcontains : residualCentralizer L (zpowers z.val) ⊔ (T : Subgroup G) ≤
      centralizer ({z.val} : Set G) := by
    rw [hzline, ←hc]
    exact sup_le (map_subtype_le _ |>.trans inf_le_right) (hc ▸ hT)
  have h1357 : Earlier1357 T L V V₃ (zpowers z.val)
      (centralizer ({z.val} : Set G)) (normalizer (L : Set G)) := by
    rw [hzline, ←hc]
    exact earlier1357 d hA312
  have hz2 : orderOf z.val = 2 := by
    rw [←Nat.card_zpowers, hzline]
    exact d.flag.one_card
  obtain ⟨hU, hn, hk, _, hq⟩ := exists_bounded_faithful_source_action
    coordinates v z hv hz hz2 hqz hAlt hfusion hCv hmark (d.seed_normalizer hA312)
    hcontains houtside h1357 (earlierF923_of_source T L V V₃ (zpowers z.val))
    (earlierF9163_of_five coordinates v z hv hz hqz hAlt hfusion hCv hmark
      (d.seed_normalizer hA312))
  let := hU
  exact (not_lt_of_ge hq) (SourceStrictBound.quadraticRatio_gt_two_of_source
    (centralizer ({z.val} : Set G)) V₃ (zpowers z.val) hn hk
    ((T : Subgroup G).subgroupOf (centralizer ({z.val} : Set G))) hcomponents
    (source_star_sqtk d.hypothesis.qtke z.val hz2))

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
