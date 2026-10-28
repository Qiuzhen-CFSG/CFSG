module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelsSourceGeometry
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.Reorientation

/-!
# Centered intervals supplied by the original large source action

The first singular arc chooses an orientation of the original two vertex
orbits. The preferred track in that orientation has a central involution,
and (5.3) excludes every central involution from its fixer. The preceding
interval theorems therefore apply with those source premises discharged:
every central block has two edges and is centered in its fixed interval.
Its radius is one, two, or odd and at least three. The radius-one exclusion,
neighbor product, and cyclic edge center remain the separate (6.8) argument.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(5.3), (6.3)--(6.8), pp.395--400.
-/

@[expose] public section
open Subgroup SimpleGraph Theory.GroupTheory
open Theory.GroupAction.CubicTree Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

/-- The source record is unchanged by exchanging its two original orbits. -/
theorem LargeTreeSource.swap (h : LargeTreeSource F s) :
    LargeTreeSource (RankTwo.swapFamily F) s := by
  refine ⟨h.action.swap, fun i => h.not_cubic (!i), fun i => h.not_alternating (!i),
    h.five_le, h.odd, shortRegular_swap h.regular, ?_⟩
  obtain ⟨v, p, hp, hn⟩ := h.singular
  let e := RankTwo.swapGraphIso F
  refine ⟨e v, p.map e.toHom, ?_, ?_⟩
  · exact (BasedWalk.nonbacktracking_map_iff e.toHom
      (fun v => (e.mapNeighborSet v).injective) p).2 hp
  · exact fun hh => hn ((rightRegular_graphIso_iff e (RankTwo.swapVertex_smul F) p).1 hh)

/-- Select the actual source orientation, rather than assuming a first-class
root for the given singular arc. The ambient group and index are unchanged. -/
theorem LargeTreeSource.exists_first_singular_orientation (h : LargeTreeSource F s) :
    ∃ flip : Bool, let F' := if flip then RankTwo.swapFamily F else F
      LargeTreeSource F' s ∧ ∃ (v : RankTwo.Vertex F') (p : BasedWalk (RankTwo.graph F') s v),
        v.type = false ∧ p.Nonbacktracking ∧ ¬ RightRegular (A := G) p := by
  obtain ⟨v, p, hp, hn⟩ := h.singular
  cases hv : v.type with
  | false => exact ⟨false, h, v, p, hv, hp, hn⟩
  | true => exact ⟨true, h.swap, singular_swap p hv hp hn⟩

/-- Every track through the original base edge contains a central involution
in the large residual case. The common edge group is a nontrivial finite
two-group, so its center supplies the involution. -/
theorem LargeTreeSource.exists_centralInvolution (h : LargeTreeSource F s)
    (t : Track (RankTwo.graph F) G)
    (h0 : t.vertex 0 = RankTwo.base F false) (h1 : t.vertex 1 = RankTwo.base F true) :
    ∃ z : G, t.CentralInvolution z := by
  let B := F false ⊓ F true
  let : Finite (F false) := h.action.finite false
  let : Finite B := Finite.of_injective
    (Subgroup.inclusion (show B ≤ F false from inf_le_left)) (Subgroup.inclusion_injective _)
  have hne : B ≠ ⊥ := by
    intro hb
    apply h.action.overlap_not_normal_of_large_residual h.not_cubic h.not_alternating false
    change (B.subgroupOf (F false)).Normal
    rw [hb, bot_subgroupOf]
    infer_instance
  let : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hne
  let : Nontrivial (Subgroup.center B) := h.action.primitive.sylow.isPGroup.center_nontrivial
  have hP : IsPGroup 2 (Subgroup.center B) := h.action.primitive.sylow.isPGroup.to_subgroup _
  have hdiv : 2 ∣ Nat.card (Subgroup.center B) := by
    rcases hP.card_eq_or_dvd with he | hd
    · have hc : 1 < Nat.card (Subgroup.center B) := Finite.one_lt_card
      omega
    · exact hd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center B) 2 hdiv
  have horder : orderOf (z.val : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz
  have he : t.edgeStabilizer 0 = B := by
    change RankTwo.stabilizer F (t.vertex 0) ⊓
      RankTwo.stabilizer F (t.vertex 1) = B
    rw [h0, h1]
    simp only [RankTwo.stabilizer, RankTwo.base, stabilizer_base]
    rfl
  refine ⟨z.val, horder, 0, ?_, ?_⟩
  · rw [he]
    exact z.val.property
  · intro g hg
    rw [he] at hg
    exact Subtype.ext_iff.mp (mem_center_iff.mp z.property ⟨g, hg⟩) |>.symm

/-- All interval premises come from the original oriented source. This is
the complete centered-interval input to the remaining local (6.8) proof. -/
theorem LargeTreeSource.exists_centered_source_track
    (h : LargeTreeSource F s) {v : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) s v) (hp : p.Nonbacktracking)
    (hn : ¬ RightRegular (A := G) p) (hv : v.type = false) :
    ∃ t : Track (RankTwo.graph F) G,
      t.vertex 0 = RankTwo.base F false ∧ t.vertex 1 = RankTwo.base F true ∧
      (AdjacentInvolutionMovers (RankTwo.graph F) G → t.HasReflections) ∧
      (∃ z : G, t.CentralInvolution z) ∧
      (∀ z : G, t.CentralInvolution z → z ∉ t.fixer) ∧
      ∀ z : G, t.CentralInvolution z → ∃ d : t.CentralInterval z,
        d.centralRight - d.centralLeft = 2 ∧ d.leftMargin = d.rightMargin ∧
        (d.rightMargin = 1 ∨ d.rightMargin = 2 ∨ Odd d.rightMargin ∧ 3 ≤ d.rightMargin) := by
  let ht := h.action.toCubicTreeAction
  obtain ⟨t, h0, h1, href⟩ := ht.exists_preferred_track
  have hf : ∀ z : G, t.CentralInvolution z → z ∉ t.fixer :=
    ht.centralInvolution_not_mem_trackFixer h.not_cubic h.not_alternating t h0 h1
      h.five_le h.odd h.regular p hp hn hv
  refine ⟨t, h0, h1, href, h.exists_centralInvolution t h0 h1, hf, ?_⟩
  intro z hz
  obtain ⟨d⟩ := ht.exists_centralInterval_of_not_mem_fixer t z hz (hf z hz)
  have hw := ht.centralInterval_length_eq_two h.five_le h.regular p hp hn
    h.not_cubic h.not_alternating t hf href hz d
  have he := ht.centralInterval_fixedLength_even h.five_le h.regular p hp hn
    h.not_cubic h.not_alternating t hf href hz d
  have hm := (ht.centralInterval_centered_of_length_two h.five_le h.regular t hz d hw he).1
  refine ⟨d, hw, hm, ?_⟩
  rcases Nat.even_or_odd d.rightMargin with hEven | hOdd
  · exact Or.inr (Or.inl (ht.centered_even_radius_eq_two h.five_le h.regular
      h.not_cubic h.not_alternating t hf hz d hw hm hEven))
  · by_cases hone : d.rightMargin = 1
    · exact Or.inl hone
    · have hpos := (ht.centralInterval_chiefBounds_of_large_residual
        h.not_cubic h.not_alternating t hz d).2.2.1
      exact Or.inr (Or.inr ⟨hOdd, by obtain ⟨k, hk⟩ := hOdd; omega⟩)

/-- The original source itself supplies a centered preferred track in one
of its two orientations. No track, involution, reflection, or finite-fixer
premise remains. -/
theorem LargeTreeSource.exists_oriented_centered_source_track (h : LargeTreeSource F s) :
    ∃ flip : Bool, let F' := if flip then RankTwo.swapFamily F else F
      ∃ t : Track (RankTwo.graph F') G,
        t.vertex 0 = RankTwo.base F' false ∧ t.vertex 1 = RankTwo.base F' true ∧
        (AdjacentInvolutionMovers (RankTwo.graph F') G → t.HasReflections) ∧
        (∃ z : G, t.CentralInvolution z) ∧
        (∀ z : G, t.CentralInvolution z → z ∉ t.fixer) ∧
        ∀ z : G, t.CentralInvolution z → ∃ d : t.CentralInterval z,
          d.centralRight - d.centralLeft = 2 ∧ d.leftMargin = d.rightMargin ∧
          (d.rightMargin = 1 ∨ d.rightMargin = 2 ∨
            Odd d.rightMargin ∧ 3 ≤ d.rightMargin) := by
  obtain ⟨flip, h', v, p, hv, hp, hn⟩ := h.exists_first_singular_orientation
  exact ⟨flip, h'.exists_centered_source_track p hp hn hv⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
