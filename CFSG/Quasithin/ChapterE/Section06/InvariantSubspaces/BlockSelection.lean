module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Counting

/-!
# Assembly of the single-block configuration

The E.6.7 source input retains all three clauses, including the actual
module and Borel identifications. The number of its factors is forced to
one by the rank obstruction. Once the residual calculation is supplied,
relative normality follows from characteristicity of the residual; the
intrinsic Sylow-overgroup calculation then supplies the last field of
`SingleBlock`.

This is conditional assembly, not a completed proof of block selection:
`FixedNineInput`, `SingleResidualInput`, and `BlockSylowMaximalInput` are
still separate model obligations. In particular neither the residual
identity nor the unique-maximal conclusion is included in `E67Input`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the proof of
E.6.14, printed p.251 (PDF p.262), and E.6.7, printed p.246 (PDF p.257).
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G] [Finite G]

/-- The low-three-rank branch already selects a single actual block from
E.6.7, independently of the automorphism, residual, and maximality work. -/
theorem exists_single_of_rank
    {K : GroupClass} {T : Sylow 2 G} {M V W : Subgroup G}
    (h : HypothesisE61 K T M V) (h67 : E67Input T M V)
    (hW : W ∈ obstructionFamily M V)
    (hc : HasCharacteristicTwo (centralizer (W : Set G)))
    (hrank : primeRank 3 (centralizer (W : Set G)) ≤ 1) :
    ∃ L : Subgroup G, L ≤ centralizer (W : Set G) ∧
      centralizer (W : Set G) = (centralizer (W : Set G) ⊓ M) ⊔ L ∧
      ChapterC.IsChiZeroBlock L ∧
      (L.subgroupOf (centralizer (W : Set G))).IsSubnormal ∧ ¬ L ≤ M := by
  have hQH := (Chapter1.isSylowIn_iff.mp (h.sylow_obstruction hW)).2.1
  obtain ⟨d⟩ := h67 W hW (centralizer (W : Set G)) hQH le_rfl hc
  exact d.toBlockFamily.exists_single
    (d.toBlockFamily.count_eq_one_of_rank hW.2.2.1 hrank) hW.2.2.1

/-- Conditional assembly with all remaining model premises exposed. The
count-one premise of the residual calculation is proved here in both
branches of ThreeCondition. Final source assembly must discharge all
three model inputs; this theorem alone does not establish E.6.14. -/
theorem singleBlockInput_of_model_inputs
    {K : GroupClass} {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 K T M V) (h67 : E67Input T M V)
    (hfixed : FixedNineInput G) (hres : SingleResidualInput T M V)
    (hmax : BlockSylowMaximalInput G) : SingleBlockInput T M V := by
  intro W hW hc hthree
  have hSyl := h.sylow_obstruction hW
  have hQH := (Chapter1.isSylowIn_iff.mp hSyl).2.1
  obtain ⟨d⟩ := h67 W hW (centralizer (W : Set G)) hQH le_rfl hc
  have hcount := d.toBlockFamily.count_eq_one h hW hc hfixed hthree
  let i : Fin d.count := ⟨0, by omega⟩
  have hr := hres W hW hc hthree d hcount i
  have hn : ((d.block i).subgroupOf (centralizer (W : Set G))).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    rw [hr]
    exact (centralizer (W : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (centralizer (W : Set G))
        (primeToResidual 3 (centralizer (W : Set G))))
  exact ⟨d.block i, ⟨d.le i, d.toBlockFamily.generated_of_count_eq_one hcount i,
    d.type i, hr, hmax _ _ _ hc hSyl (d.le i) hn (d.type i)⟩⟩

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
