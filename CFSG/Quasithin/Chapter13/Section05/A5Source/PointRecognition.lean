module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.RecognitionKnownSimple

/-!
# A₅ recognition at the original point normalizer

A nonabelian seed closure forces the full point centralizer outside N_G(L).
Otherwise the trivial-intersection property of the original chosen module
makes this centralizer normalize V, and the seed closure is contained in V.
The order-two invariant line then places that same centralizer in H_z.

Apply the completed normal and nonnormal recognition to this actual member.
Since the source line has order two, its normalizer is its centralizer. Thus
the conclusion uses the original G₁ = N_G(V₁), with no escaping-subgroup choice,
F.9, component catalogue, or A.3.12 input beyond the original A₅ Context.

Source: Aschbacher–Smith, Theorem 13.5.12 and the choice of H immediately
following it, printed p.918; nonnormal component argument 13.5.19–25,
printed pp.922–925.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- Nonabelianness supplies the actual escaping member used in 13.5.19–25. -/
theorem point_centralizer_mem_family_of_nonabelian
    (hU : ¬ IsMulCommutative (conjugateSpanBy V₃ (centralizer (V₁ : Set G)))) :
    centralizer (V₁ : Set G) ∈ Section08.Source.Hz (residualCentralizer L V₁)
      (T : Subgroup G) (centralizer (V₁ : Set G)) (normalizer (L : Set G)) := by
  have hline : V₁ ≤ V := d.flag.one_le_two.trans d.flag.two_le_V
  have hne : V₁ ≠ ⊥ := by
    intro he
    have hc := d.flag.one_card
    rw [he, card_bot] at hc
    contradiction
  have hTZ : (T : Subgroup G) ≤ centralizer (V₁ : Set G) :=
    d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
  have hcore : V₁ ≤ (centralizer (V₁ : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le (hline.trans d.chosen.le_sylow))
      ((hline.trans d.chosen.le_sylow).trans hTZ) (Subgroup.centralizer_le_normalizer _)
  refine ⟨⟨?_, sup_le ((map_subtype_le _).trans inf_le_right) hTZ⟩, le_rfl, ?_⟩
  · intro he
    exact hne (bot_unique (hcore.trans_eq he))
  · intro hlocal
    have hnorm : centralizer (V₁ : Set G) ≤ normalizer (V : Set G) :=
      (le_inf hlocal le_rfl).trans
        (inf_centralizer_le_normalizer_of_trivial_intersections d.trivial_intersections hne hline)
    have hspan : conjugateSpanBy V₃ (centralizer (V₁ : Set G)) ≤ V :=
      conjugateSpanBy_le d.third_le hnorm
    let : IsElementaryAbelian 2 V := d.elementary
    exact hU (le_centralizer_iff_isMulCommutative.mp
      (hspan.trans ((le_centralizer V).trans (centralizer_le hspan))))

/-- The A₅ conclusion of 13.5.12 on the unchanged source point normalizer. -/
theorem source_point_modelConclusion_knownSimple
    (hU : ¬ IsMulCommutative (conjugateSpanBy V₃ (normalizer (V₁ : Set G)))) :
    ModelConclusion G 5 := by
  have he : normalizer (V₁ : Set G) = centralizer (V₁ : Set G) :=
    le_antisymm (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
      (Subgroup.centralizer_le_normalizer _)
  rw [he] at hU
  let : IsElementaryAbelian 2 V := d.elementary
  exact source_modelConclusion_knownSimple d
    (point_centralizer_mem_family_of_nonabelian d hU) hU

end CFSG.Quasithin.Chapter13.Section05.A5Source
