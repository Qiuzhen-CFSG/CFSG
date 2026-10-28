module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source.RankOne
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source.BorelMarks
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.BorelMarks.Linear
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The complete original rank-one branch of E.6.7

The original Thompson movement restricts to H. C.1.29's full Borel theorem
therefore identifies the actual intersection with M, after transport through
the canonical relative-block equivalence. Applying the rank-one source
calculation discharges every earlier premise, including I.2.3, and retains
the regular action on the same actual displacement subgroup for E.6.11.

Source: Aschbacher–Smith E.6.7(3) and E.6.11, pp.246 and 249.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- The literal rank-one Borel follows from original source control and movement. -/
theorem source_linear_borel {𝒦 : GroupClass} {T : Sylow 2 G}
    {M V W H L : Subgroup G} {n : ℕ}
    (h : HypothesisE61 𝒦 T M V) (hW : W ∈ obstructionFamily M V)
    (hQH : sylowCentralizer (T : Subgroup G) V ≤ H)
    (hHC : H ≤ centralizer (W : Set G))
    (hLH : L ≤ H) (hL : ChapterC.IsBlock (L.subgroupOf H))
    (hout : ¬ L ≤ M)
    (hm : L = ⁅L, elementaryAbelianMaxJ (sylowCentralizer (T : Subgroup G) V)⁆)
    (hType : ChapterC.IsL2EvenBlock L n) : L2BlockBorel L (M.subgroupOf L) n := by
  obtain ⟨S, hS, hcontrol⟩ := source_control_sylow h hW hQH hHC
  let e := subgroupOfEquivOfLe hLH
  have ht := hType.of_mulEquiv e.symm
  have hout' : ¬ L.subgroupOf H ≤ M.subgroupOf H := by
    intro hh
    apply hout
    intro l hl
    exact hh (show (⟨l, hLH hl⟩ : H) ∈ L.subgroupOf H from hl)
  have hm' : L.subgroupOf H = ⁅L.subgroupOf H, elementaryAbelianMaxJ (S : Subgroup H)⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator, ← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      hS, map_subgroupOf_eq_of_le hQH, map_subgroupOf_eq_of_le hLH]
    exact hm
  have hb := linear_block_borel_of_control S _ _ hcontrol hL hout' hm' ht
  have hh := hb.of_mulEquiv e
  rw [map_relative_intersection hLH] at hh
  exact hh

/-- All original rank-one conclusions plus the regular-action consequence
on the same torus, with no Borel or cover theorem left as a premise. -/
theorem source_rankOne {𝒦 : GroupClass} {T : Sylow 2 G}
    {M V W H L : Subgroup G} {n : ℕ}
    (h : HypothesisE61 𝒦 T M V) (hW : W ∈ obstructionFamily M V)
    (hQH : sylowCentralizer (T : Subgroup G) V ≤ H)
    (hHC : H ≤ centralizer (W : Set G)) (hc : HasCharacteristicTwo H)
    (hLH : L ≤ H) (hL : ChapterC.IsBlock (L.subgroupOf H))
    (hout : ¬ L ≤ M)
    (hm : L = ⁅L, elementaryAbelianMaxJ (sylowCentralizer (T : Subgroup G) V)⁆)
    (hType : ChapterC.IsL2EvenBlock L n) :
    V ≤ normalizer (L : Set G) ∧
    ∃ X : Subgroup G, X ≤ L ⊓ M ∧ IsCyclic X ∧ Nat.card X = 2^n-1 ∧
      V = (V ⊓ centralizer (L : Set G)) ⊔ ⁅V,X⁆ ∧
      Disjoint (V ⊓ centralizer (L : Set G)) ⁅V,X⁆ ∧ Nat.card ↥⁅V,X⁆ = 2^n ∧
      (L ⊓ M : Set G) = ((L ⊓ sylowCentralizer (T : Subgroup G) V : Subgroup G) : Set G) *
        (X : Set G) ∧
      L2BlockBorel L (M.subgroupOf L) n ∧ n ≤ subgroupCorank V W ∧
      RegularConjugationOnNonidentity X ⁅V,X⁆ :=
  source_rankOne_of_borel h hW hQH hHC hc hLH hL hout hType
    (source_linear_borel h hW hQH hHC hLH hL hout hm hType)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
