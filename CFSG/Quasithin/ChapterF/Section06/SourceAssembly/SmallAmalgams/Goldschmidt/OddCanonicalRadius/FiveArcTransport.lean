module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.OddCanonicalRadius.NeighborhoodProduct
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.OddCanonicalRadius.FiveTerminal
public import Theory.GroupAction.CubicTree.TrackArcs
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Transporting the radius-five commutator to arbitrary eight-arcs

Short-arc transitivity aligns the middle four edges with the chosen track.
The neighbor-product relation gives four possible labels at each endpoint;
commuting interior factors leave their commutator equal to the midpoint label.
The terminal folded-arc argument then excludes radius five.

Only the single aligned track commutator remains an earlier-source premise.
Source: Goldschmidt (1980), (6.11), printed pp.402–403.
-/

@[expose] public section

open scoped commutatorElement

namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt

variable {G : Type*} [Group G]

private theorem remove_left_endpoint_factor (a : G) {b y : G}
    (hby : Commute b y) : ⁅a * b, y⁆ = ⁅a, y⁆ := by
  simp only [commutatorElement_mul_left_eq_conj_mul, hby.commutator_eq,
    mul_one, mul_inv_cancel, one_mul]

private theorem remove_right_endpoint_factor (b : G) {x c : G}
    (hxc : Commute x c) : ⁅x, b * c⁆ = ⁅x, b⁆ := by
  simp only [commutatorElement_mul_right_eq_mul_conj, hxc.commutator_eq,
    mul_one, mul_inv_cancel_right]

/-- The four allowed endpoint labels have the same midpoint commutator.
Only the seven displayed commuting pairs are needed for this calculation. -/
private theorem fiveEndpoint_commutator {a b c d e x y : G}
    (hac : Commute a c) (had : Commute a d)
    (hbc : Commute b c) (hbd : Commute b d) (hbe : Commute b e)
    (hcd : Commute c d) (hce : Commute c e)
    (hae : ⁅a, e⁆ = c)
    (hx : x = a ∨ x = a * b ∨ x = a * c ∨ x = a * b * c)
    (hy : y = e ∨ y = e * d ∨ y = e * c ∨ y = e * d * c) :
    ⁅x, y⁆ = c := by
  have hxe : ⁅x, e⁆ = c := by
    rcases hx with rfl | rfl | rfl | rfl
    · exact hae
    · exact (remove_left_endpoint_factor a hbe).trans hae
    · exact (remove_left_endpoint_factor a hce).trans hae
    · exact (remove_left_endpoint_factor (a * b) hce).trans
        ((remove_left_endpoint_factor a hbe).trans hae)
  have hxd : Commute x d := by
    rcases hx with rfl | rfl | rfl | rfl
    · exact had
    · exact had.mul_left hbd
    · exact had.mul_left hcd
    · exact (had.mul_left hbd).mul_left hcd
  have hxc : Commute x c := by
    rcases hx with rfl | rfl | rfl | rfl
    · exact hac
    · exact hac.mul_left hbc
    · exact hac.mul_left (Commute.refl c)
    · exact (hac.mul_left hbc).mul_left (Commute.refl c)
  rcases hy with rfl | rfl | rfl | rfl
  · exact hxe
  · exact (remove_right_endpoint_factor e hxd).trans hxe
  · exact (remove_right_endpoint_factor e hxc).trans hxe
  · exact (remove_right_endpoint_factor (e * d) hxc).trans
      ((remove_right_endpoint_factor e hxd).trans hxe)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt


@[expose] public section
open Subgroup SimpleGraph
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry

variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem type_of_two_steps {a b c : RankTwo.Vertex F}
    (hab : (RankTwo.graph F).Adj a b) (hbc : (RankTwo.graph F).Adj b c) : c.type = a.type := by
  have h0 := hab.1
  have h1 := hbc.1
  cases h2 : a.type <;> cases h3 : b.type <;> cases h4 : c.type <;> simp_all

private theorem CanonicalLabelSetup.five_endpoint_alternatives
    (d : CanonicalLabelSetup F s) (h : CubicTreeAction F)
    {a0 a1 a2 a3 : RankTwo.Vertex F}
    (h01 : (RankTwo.graph F).Adj a0 a1)
    (h12 : (RankTwo.graph F).Adj a1 a2)
    (h23 : (RankTwo.graph F).Adj a2 a3)
    (h02 : a0 ≠ a2) (h13 : a1 ≠ a3)
    (ha0 : a0.type = d.side)
    (x C : G) (hx2 : x • a2 = a2) (hx3 : x • a3 = a3)
    (hx1 : x • a1 ≠ a1)
    (hxa0 : d.label (x • a0) = d.label a0 * C)
    (hC : Commute (d.label a2) C)
    (hbranch : ∀ {a b u w : RankTwo.Vertex F}, a.type = d.side →
      (RankTwo.graph F).Adj a b → (RankTwo.graph F).Adj b u →
      (RankTwo.graph F).Adj b w → u ≠ a → w ≠ a →
      d.label w = d.label u ∨ d.label w = d.label u * d.label a) :
    ∀ {u v : RankTwo.Vertex F},
      (RankTwo.graph F).Adj a2 v → v ≠ a3 →
      (RankTwo.graph F).Adj v u → u ≠ a2 →
      d.label u = d.label a0 ∨
        d.label u = d.label a0 * d.label a2 ∨
        d.label u = d.label a0 * C ∨
        d.label u = d.label a0 * d.label a2 * C := by
  have ha2 : a2.type = d.side := by
    exact (type_of_two_steps h01 h12).trans ha0
  have hxa1a3 : x • a1 ≠ a3 := by
    intro he
    exact h13 ((MulAction.toPerm x).injective (he.trans hx3.symm))
  have hxa0a2 : x • a0 ≠ a2 := by
    intro he
    exact h02 ((MulAction.toPerm x).injective (he.trans hx2.symm))
  have hxa1_adj : (RankTwo.graph F).Adj a2 (x • a1) := by
    simpa only [hx2] using (trackGraphAction.map_adj x h12).symm
  have hxa0a1_adj : (RankTwo.graph F).Adj (x • a1) (x • a0) :=
    trackGraphAction.map_adj x h01.symm
  have hcardT : ({a1, a3, x • a1} : Set (RankTwo.Vertex F)).ncard = 3 := by
    simp [h13, hxa1a3.symm, hx1.symm]
  have hf : Finite ((RankTwo.graph F).neighborSet a2) :=
    Nat.finite_of_card_ne_zero (by rw [h.card_neighbor a2]; decide)
  have hneigh : (RankTwo.graph F).neighborSet a2 =
      ({a1, a3, x • a1} : Set (RankTwo.Vertex F)) := by
    apply (Set.eq_of_subset_of_ncard_le ?_ ?_).symm
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact h12.symm
      · exact h23
      · exact hxa1_adj
    · rw [hcardT]
      have hcard : ((RankTwo.graph F).neighborSet a2).ncard = 3 := by
        rw [← Nat.card_coe_set_eq]
        exact h.card_neighbor a2
      exact hcard.le
  intro u v hv hne hvu hmu
  have hv_cases : v = a1 ∨ v = x • a1 := by
    have hv' : v = a1 ∨ v = a3 ∨ v = x • a1 := by
      have : v ∈ ({a1, a3, x • a1} : Set (RankTwo.Vertex F)) := by
        rw [← hneigh]
        exact hv
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    rcases hv' with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact (hne rfl).elim
    · exact Or.inr rfl
  rcases hv_cases with rfl | rfl
  · rcases hbranch ha2 h12.symm h01.symm hvu h02 hmu with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
  · have halt := hbranch ha2 hxa1_adj hxa0a1_adj hvu hxa0a2 hmu
    rcases halt with h0 | h1
    · exact Or.inr (Or.inr (Or.inl (h0.trans hxa0)))
    · right; right; right
      calc
        d.label u = (d.label a0 * C) * d.label a2 := h1.trans (by rw [hxa0])
        _ = d.label a0 * (C * d.label a2) := mul_assoc _ _ _
        _ = d.label a0 * (d.label a2 * C) := by rw [hC.eq.symm]
        _ = d.label a0 * d.label a2 * C := (mul_assoc _ _ _).symm

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt


@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem CanonicalLabelSetup.midpoint_of_aligned_arms
    (d : CanonicalLabelSetup F s) (h : CubicTreeAction F) (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (hAligned : ∀ u₀ u₁ u₇ u₈ : RankTwo.Vertex F,
      (RankTwo.graph F).Adj u₀ u₁ →
      (RankTwo.graph F).Adj u₁ (d.track.vertex (d.center+2)) →
      u₁ ≠ d.track.vertex (d.center+3) → u₀ ≠ d.track.vertex (d.center+2) →
      (RankTwo.graph F).Adj (d.track.vertex (d.center+6)) u₇ →
      (RankTwo.graph F).Adj u₇ u₈ →
      u₇ ≠ d.track.vertex (d.center+5) → u₈ ≠ d.track.vertex (d.center+6) →
      ⁅d.label u₀, d.label u₈⁆ = d.label (d.track.vertex (d.center+4))) :
    ∀ {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) 8 v),
      p.Nonbacktracking → v.type = d.side →
      ⁅d.label v, d.label p.endpoint⁆ = d.label (p.toWalk.getVert 4) := by
  intro v₀ p hp hv₀
  rcases p with ⟨⟨v₁, h01⟩, ⟨⟨v₂, h12⟩, ⟨⟨v₃, h23⟩,
    ⟨⟨v₄, h34⟩, ⟨⟨v₅, h45⟩, ⟨⟨v₆, h56⟩,
      ⟨⟨v₇, h67⟩, ⟨⟨v₈, h78⟩, rest⟩⟩⟩⟩⟩⟩⟩⟩
  change ⁅d.label v₀, d.label v₈⁆ = d.label v₄
  rcases hp with ⟨h20, h31, h42, h53, h64, h75, h86, _⟩
  have htwo : ∀ {x y z : RankTwo.Vertex F},
      (RankTwo.graph F).Adj x y → (RankTwo.graph F).Adj y z → x.type = z.type := by
    intro x y z hxy hyz
    have hxy' := hxy.1
    have hyz' := hyz.1
    cases hx : x.type <;> cases hy : y.type <;> cases hz : z.type <;> simp_all
  have hv₂ : v₂.type = d.side := (htwo h01 h12).symm.trans hv₀
  have hv₄ : v₄.type = d.side := (htwo h23 h34).symm.trans hv₂
  have hv₆ : v₆.type = d.side := (htwo h45 h56).symm.trans hv₄
  have hv₈ : v₈.type = d.side := (htwo h67 h78).symm.trans hv₆
  let q : BasedWalk (RankTwo.graph F) 4 v₂ :=
    ⟨⟨v₃, h23⟩, ⟨⟨v₄, h34⟩, ⟨⟨v₅, h45⟩, ⟨⟨v₆, h56⟩, PUnit.unit⟩⟩⟩⟩
  have hq : q.Nonbacktracking := ⟨h42, h53, h64, trivial⟩
  obtain ⟨g, hg⟩ := h.congruent_arcs s hshort (show 4 ≤ s by omega) q
    (d.track.arc (d.center+2) 4) hq (d.track.arc_nonbacktracking _ _)
    (hv₂.trans (by simpa only [mul_one] using (d.shifted_type 1).symm))
  change [g • v₂, g • v₃, g • v₄, g • v₅, g • v₆] =
    [d.track.vertex (d.center+2), d.track.vertex (d.center+2+1),
      d.track.vertex (d.center+2+1+1), d.track.vertex (d.center+2+1+1+1),
      d.track.vertex (d.center+2+1+1+1+1)] at hg
  simp only [List.cons.injEq, and_true,
    show d.center+2+1 = d.center+3 by omega,
    show d.center+3+1 = d.center+4 by omega,
    show d.center+4+1 = d.center+5 by omega,
    show d.center+5+1 = d.center+6 by omega] at hg
  obtain ⟨hg₂, hg₃, hg₄, hg₅, hg₆⟩ := hg
  have hmid := hAligned (g • v₀) (g • v₁) (g • v₇) (g • v₈)
    (trackGraphAction.map_adj g h01)
    (by simpa only [hg₂] using trackGraphAction.map_adj g h12)
    (by rw [← hg₃]; exact fun he => h31 ((MulAction.toPerm g).injective he).symm)
    (by rw [← hg₂]; exact fun he => h20 ((MulAction.toPerm g).injective he).symm)
    (by simpa only [hg₆] using trackGraphAction.map_adj g h67)
    (trackGraphAction.map_adj g h78)
    (by rw [← hg₅]; exact fun he => h75 ((MulAction.toPerm g).injective he))
    (by rw [← hg₆]; exact fun he => h86 ((MulAction.toPerm g).injective he))
  apply (MulAut.conj g).injective
  rw [map_commutatorElement]
  change ⁅g * d.label v₀ * g⁻¹, g * d.label v₈ * g⁻¹⁆ = g * d.label v₄ * g⁻¹
  rw [← d.conjugate g v₀ hv₀, ← d.conjugate g v₈ hv₈,
    ← d.conjugate g v₄ hv₄, hg₄]
  exact hmid

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt


namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem CanonicalLabelSetup.label_smul_eq_mul_commutator
    (d : CanonicalLabelSetup F s) {a b : RankTwo.Vertex F} (ha : a.type = d.side) :
    d.label (d.label b • a) = d.label a * ⁅d.label a, d.label b⁆ := by
  rw [d.conjugate _ _ ha]
  simp only [commutatorElement_def, d.label_inv ha, ← mul_assoc,
    d.label_mul_self ha, one_mul]

/-- The single source track commutator determines the midpoint commutator on
all eight-arcs, using the established neighbor-product consequence. -/
theorem CanonicalLabelSetup.midpoint_of_radiusFive_track_commutator
    (d : CanonicalLabelSetup F s) (h : CubicTreeAction F) (hr : d.radius = 5)
    (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (htrack : ⁅d.label (d.track.vertex d.center),
      d.label (d.track.vertex (d.center+8))⁆ = d.label (d.track.vertex (d.center+4))) :
    ∀ {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) 8 v),
      p.Nonbacktracking → v.type = d.side →
      ⁅d.label v, d.label p.endpoint⁆ = d.label (p.toWalk.getVert 4) := by
  apply d.midpoint_of_aligned_arms h hs hshort
  intro u₀ u₁ u₇ u₈ h01 h12 hn13 hn02 h67 h78 hn75 hn86
  let p : ℤ → RankTwo.Vertex F := fun i => d.track.vertex (d.center+i)
  let z : ℤ → G := fun i => d.label (p i)
  have hinj : Function.Injective p := by
    intro i j he
    have hh := d.track.injective he
    omega
  have hadj (i : ℤ) : (RankTwo.graph F).Adj (p i) (p (i+1)) := by
    simpa only [p, add_assoc] using d.track.adjacent (d.center+i)
  have ht (k : ℤ) : (p (2*k)).type = d.side := d.shifted_type k
  have hf (k i : ℤ) : z (2*k) • p i = p i ↔ 2*k-6 ≤ i ∧ i ≤ 2*k+6 := by
    dsimp only [z, p]
    rw [d.shifted_fixed_iff, hr]
    omega
  have hc (i j : ℤ) (hlo : -3 ≤ i-j) (hhi : i-j ≤ 3) :
      Commute (z (2*i)) (z (2*j)) :=
    d.labels_commute_of_fixed (ht j) ((hf i (2*j)).2 (by omega))
  have htrack' : ⁅z 0, z 8⁆ = z 4 := by
    simpa only [z, p, add_zero] using htrack
  have hreverse : ⁅z 8, z 0⁆ = z 4 := by
    rw [← commutatorElement_inv, htrack']
    exact d.label_inv (ht 2)
  have himage₀ : d.label (z 8 • p 0) = z 0 * z 4 := by
    exact (d.label_smul_eq_mul_commutator (a := p 0) (b := p 8) (ht 0)).trans
      (congrArg (z 0 * ·) htrack')
  have himage₈ : d.label (z 0 • p 8) = z 8 * z 4 := by
    exact (d.label_smul_eq_mul_commutator (a := p 8) (b := p 0) (ht 4)).trans
      (congrArg (z 8 * ·) hreverse)
  have hx : d.label u₀ = z 0 ∨ d.label u₀ = z 0*z 2 ∨
      d.label u₀ = z 0*z 4 ∨ d.label u₀ = z 0*z 2*z 4 := by
    apply d.five_endpoint_alternatives h (hadj 0) (hadj 1) (hadj 2)
      (fun he => by have := hinj he; norm_num at this)
      (fun he => by have := hinj he; norm_num at this) (ht 0) (z 8) (z 4)
      ((hf 4 2).2 (by norm_num)) ((hf 4 3).2 (by norm_num))
      (fun he => by have := (hf 4 1).1 he; omega)
      himage₀ (hc 1 2 (by norm_num) (by norm_num)) d.branch_label_alternative
    · exact h12.symm
    · exact hn13
    · exact h01.symm
    · exact hn02
  have hy : d.label u₈ = z 8 ∨ d.label u₈ = z 8*z 6 ∨
      d.label u₈ = z 8*z 4 ∨ d.label u₈ = z 8*z 6*z 4 := by
    apply d.five_endpoint_alternatives h (hadj 7).symm (hadj 6).symm (hadj 5).symm
      (fun he => by have := hinj he; norm_num at this)
      (fun he => by have := hinj he; norm_num at this) (ht 4) (z 0) (z 4)
      ((hf 0 6).2 (by norm_num)) ((hf 0 5).2 (by norm_num))
      (fun he => by have := (hf 0 7).1 he; omega)
      himage₈ (hc 3 2 (by norm_num) (by norm_num)) d.branch_label_alternative
    · exact h67
    · exact hn75
    · exact h78
    · exact hn86
  exact fiveEndpoint_commutator
    (hc 0 2 (by norm_num) (by norm_num))
    (hc 0 3 (by norm_num) (by norm_num))
    (hc 1 2 (by norm_num) (by norm_num))
    (hc 1 3 (by norm_num) (by norm_num))
    (hc 1 4 (by norm_num) (by norm_num))
    (hc 2 3 (by norm_num) (by norm_num))
    (hc 2 4 (by norm_num) (by norm_num)) htrack' hx hy

/-- The aligned source commutator excludes the remaining radius-five case. -/
theorem CanonicalLabelSetup.radius_ne_five_of_track_commutator
    (d : CanonicalLabelSetup F s) (h : CubicTreeAction F) (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (htrack : ⁅d.label (d.track.vertex d.center),
      d.label (d.track.vertex (d.center+8))⁆ = d.label (d.track.vertex (d.center+4))) :
    d.radius ≠ 5 := by
  intro hr
  exact d.radius_ne_five_of_midpoint
    (d.midpoint_of_radiusFive_track_commutator h hr hs hshort htrack) hr

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
