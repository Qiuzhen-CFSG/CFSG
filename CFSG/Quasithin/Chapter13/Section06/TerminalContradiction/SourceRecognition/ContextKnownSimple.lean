module
public import CFSG.Quasithin.Chapter13.Section06.SourceAbelian.KnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ContextComplete

/-!
# Original A₅ terminal action over the known-simple catalogue

The original context now supplies abelian closure and the earlier F.9 setup
without A.3.12. The actual marked quotient action violates the two independent
quadratic-ratio bounds, so the original exceptional component conclusion
implies the terminal contradiction. Component construction remains separate.

Source: Aschbacher–Smith 13.6.2 and terminal 13.6, printed pp.926,935.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Ratio Section05.A5Source CentralizerReduction CentralizerReduction.A5Module
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original marked A₅ terminal argument with closure and F.9 setup supplied. -/
theorem terminal_contradiction_of_marked_A5_knownSimple
    (d : Context T L V V₁ V₂ V₃)
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
  let := SourceAbelian.source_closure_abelian_knownSimple d z.val hzline houtside hcounter
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
    exact earlier1357_knownSimple d
  have hz2 : orderOf z.val = 2 := by
    rw [←Nat.card_zpowers, hzline]
    exact d.flag.one_card
  obtain ⟨hU, hn, hk, _, hq⟩ := exists_bounded_faithful_source_action
    coordinates v z hv hz hz2 hqz hAlt hfusion hCv hmark (d.seed_normalizer_knownSimple)
    hcontains houtside h1357 (earlierF923_of_source T L V V₃ (zpowers z.val))
    (earlierF9163_of_five coordinates v z hv hz hqz hAlt hfusion hCv hmark
      (d.seed_normalizer_knownSimple))
  let := hU
  exact (not_lt_of_ge hq) (SourceStrictBound.quadraticRatio_gt_two_of_source
    (centralizer ({z.val} : Set G)) V₃ (zpowers z.val) hn hk
    ((T : Subgroup G).subgroupOf (centralizer ({z.val} : Set G))) hcomponents
    (source_star_sqtk d.hypothesis.qtke z.val hz2))


omit [IsElementaryAbelian 2 V] in
/-- Apply the terminal contradiction at the original source flag and its literal line centralizer. -/
theorem terminal_contradiction_of_A5_context_knownSimple
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    (hcomponents : Components.Conclusion
      ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G)))) : False := by
  let := d.elementary
  obtain ⟨c, hv, _⟩ := source_coordinates d
  have hC : centralizer (V₁ : Set G) = centralizer ({c.singular.val} : Set G) := by
    calc
      _ = centralizer (zpowers c.singular.val : Set G) :=
        congrArg (fun W : Subgroup G => centralizer (W : Set G)) c.line_eq.symm
      _ = _ := by rw [zpowers_eq_closure, centralizer_closure]
  exact terminal_contradiction_of_marked_A5_knownSimple d c.coordinates
    c.nonsingular c.singular c.form_nonsingular c.singular_ne_one c.line_eq
    c.form_singular c.alternating_le
    (d.flag.normalizer_controls_fusion_of_nonsingular_centralizer hCv)
    (by simpa only [hv] using hCv) c.third_mark
    (hC ▸ houtside) hcounter (hC ▸ hcomponents)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
