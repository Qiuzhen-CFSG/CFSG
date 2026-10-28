module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsLabels
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.OddCanonicalRadius.NeighborhoodProduct
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Transporting the radius-three commutator

The single track relation (6.12.3) gives the commutator on every six-arc.
Align the middle two edges; the folded branches change endpoint labels by
commuting interior labels. This uses only the original short-arc regularity,
without requiring six-arc transitivity.

Source: Goldschmidt (1980), (6.12.3)--(6.12.5), printed p.404.
-/

@[expose] public section
noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem remove_left_endpoint_factor (a : G) {b y : G}
    (hby : Commute b y) : ⁅a * b, y⁆ = ⁅a, y⁆ := by
  simp only [commutatorElement_mul_left_eq_conj_mul, hby.commutator_eq,
    mul_one, mul_inv_cancel, one_mul]

private theorem remove_right_endpoint_factor (b : G) {x c : G}
    (hxc : Commute x c) : ⁅x, b * c⁆ = ⁅x, b⁆ := by
  simp only [commutatorElement_mul_right_eq_mul_conj, hxc.commutator_eq,
    mul_one, mul_inv_cancel_right]

private theorem type_of_two_steps {a b c : RankTwo.Vertex F}
    (hab : (RankTwo.graph F).Adj a b) (hbc : (RankTwo.graph F).Adj b c) : c.type = a.type := by
  have h0 := hab.1
  have h1 := hbc.1
  cases h2 : a.type <;> cases h3 : b.type <;> cases h4 : c.type <;> simp_all

private theorem CanonicalLabelSetup.radiusThree_endpoint_alternatives
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


private theorem endpoint_commutator {a b c e x y : G}
    (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (hbe : Commute b e) (hce : Commute c e)
    (hae : ⁅a, e⁆ = b*c)
    (hx : x = a ∨ x = a*b ∨ x = a*(b*c) ∨ x = a*b*(b*c))
    (hy : y = e ∨ y = e*c ∨ y = e*(b*c) ∨ y = e*c*(b*c)) :
    ⁅x, y⁆ = b*c := by
  have hxe : ⁅x, e⁆ = b*c := by
    rcases hx with rfl | rfl | rfl | rfl
    · exact hae
    · exact (remove_left_endpoint_factor a hbe).trans hae
    · exact (remove_left_endpoint_factor a (hbe.mul_left hce)).trans hae
    · exact (remove_left_endpoint_factor (a*b) (hbe.mul_left hce)).trans
        ((remove_left_endpoint_factor a hbe).trans hae)
  have hxb : Commute x b := by
    rcases hx with rfl | rfl | rfl | rfl
    · exact hab
    · exact hab.mul_left (Commute.refl b)
    · exact hab.mul_left ((Commute.refl b).mul_left hbc.symm)
    · exact (hab.mul_left (Commute.refl b)).mul_left ((Commute.refl b).mul_left hbc.symm)
  have hxc : Commute x c := by
    rcases hx with rfl | rfl | rfl | rfl
    · exact hac
    · exact hac.mul_left hbc
    · exact hac.mul_left (hbc.mul_left (Commute.refl c))
    · exact (hac.mul_left hbc).mul_left (hbc.mul_left (Commute.refl c))
  rcases hy with rfl | rfl | rfl | rfl
  · exact hxe
  · exact (remove_right_endpoint_factor e hxc).trans hxe
  · exact (remove_right_endpoint_factor e (hxb.mul_right hxc)).trans hxe
  · exact (remove_right_endpoint_factor (e*c) (hxb.mul_right hxc)).trans
      ((remove_right_endpoint_factor e hxc).trans hxe)

private theorem CanonicalLabelSetup.label_smul_eq_mul_commutator
    (d : CanonicalLabelSetup F s) {a b : RankTwo.Vertex F} (ha : a.type = d.side) :
    d.label (d.label b • a) = d.label a * ⁅d.label a, d.label b⁆ := by
  rw [d.conjugate _ _ ha]
  simp only [commutatorElement_def, d.label_inv ha, ← mul_assoc,
    d.label_mul_self ha, one_mul]

private theorem CanonicalLabelSetup.radiusThree_aligned_arms
    (d : CanonicalLabelSetup F s) (h : CubicTreeAction F) (hr : d.radius = 3)
    (htrack : ⁅d.label (d.track.vertex (d.center-2)),
      d.label (d.track.vertex (d.center+4))⁆ =
        d.label (d.track.vertex d.center) * d.label (d.track.vertex (d.center+2)))
    (u₀ u₁ u₅ u₆ : RankTwo.Vertex F)
    (h01 : (RankTwo.graph F).Adj u₀ u₁)
    (h12 : (RankTwo.graph F).Adj u₁ (d.track.vertex d.center))
    (hn13 : u₁ ≠ d.track.vertex (d.center+1))
    (hn02 : u₀ ≠ d.track.vertex d.center)
    (h45 : (RankTwo.graph F).Adj (d.track.vertex (d.center+2)) u₅)
    (h56 : (RankTwo.graph F).Adj u₅ u₆)
    (hn53 : u₅ ≠ d.track.vertex (d.center+1))
    (hn64 : u₆ ≠ d.track.vertex (d.center+2)) :
    ⁅d.label u₀, d.label u₆⁆ =
      d.label (d.track.vertex d.center) * d.label (d.track.vertex (d.center+2)) := by
  let p : ℤ → RankTwo.Vertex F := fun i => d.track.vertex (d.center+i)
  let z : ℤ → G := fun i => d.label (p i)
  have hinj : Function.Injective p := by
    intro i j he
    have hh := d.track.injective he
    omega
  have hadj (i : ℤ) : (RankTwo.graph F).Adj (p i) (p (i+1)) := by
    simpa only [p, add_assoc] using d.track.adjacent (d.center+i)
  have ht (k : ℤ) : (p (2*k)).type = d.side := d.shifted_type k
  have hf (k i : ℤ) : z (2*k) • p i = p i ↔ 2*k-4 ≤ i ∧ i ≤ 2*k+4 := by
    dsimp only [z, p]
    rw [d.shifted_fixed_iff, hr]
    omega
  have hc (i j : ℤ) (hlo : -2 ≤ i-j) (hhi : i-j ≤ 2) :
      Commute (z (2*i)) (z (2*j)) :=
    d.labels_commute_of_fixed (ht j) ((hf i (2*j)).2 (by omega))
  have htm : (p (-2)).type = d.side := by simpa using ht (-1)
  have ham : (RankTwo.graph F).Adj (p (-2)) (p (-1)) := by simpa using hadj (-2)
  have ham' : (RankTwo.graph F).Adj (p (-1)) (p 0) := by simpa using hadj (-1)
  have hcm0 : Commute (z (-2)) (z 0) := by simpa using hc (-1) 0 (by omega) (by omega)
  have hcm2 : Commute (z (-2)) (z 2) := by simpa using hc (-1) 1 (by omega) (by omega)
  have hc02 : Commute (z 0) (z 2) := by simpa using hc 0 1 (by omega) (by omega)
  have hc04 : Commute (z 0) (z 4) := by simpa using hc 0 2 (by omega) (by omega)
  have hc24 : Commute (z 2) (z 4) := by simpa using hc 1 2 (by omega) (by omega)
  have hi0 : (z 0)⁻¹ = z 0 := d.label_inv (by simpa using ht 0)
  have hi2 : (z 2)⁻¹ = z 2 := d.label_inv (by simpa using ht 1)
  have hfm (i : ℤ) : z (-2) • p i = p i ↔ -6 ≤ i ∧ i ≤ 2 := by
    simpa using hf (-1) i
  have htrack' : ⁅z (-2), z 4⁆ = z 0*z 2 := by
    simpa only [z, p, add_zero, sub_eq_add_neg] using htrack
  have hreverse : ⁅z 4, z (-2)⁆ = z 0*z 2 := by
    rw [← commutatorElement_inv, htrack', mul_inv_rev,
      hi2, hi0]
    exact hc02.symm.eq
  have himage₀ : d.label (z 4 • p (-2)) = z (-2) * (z 0*z 2) := by
    exact (d.label_smul_eq_mul_commutator (a := p (-2)) (b := p 4) htm).trans
      (congrArg (z (-2) * ·) htrack')
  have himage₆ : d.label (z (-2) • p 4) = z 4 * (z 0*z 2) := by
    exact (d.label_smul_eq_mul_commutator (a := p 4) (b := p (-2)) (ht 2)).trans
      (congrArg (z 4 * ·) hreverse)
  have hx : d.label u₀ = z (-2) ∨ d.label u₀ = z (-2)*z 0 ∨
      d.label u₀ = z (-2)*(z 0*z 2) ∨ d.label u₀ = z (-2)*z 0*(z 0*z 2) := by
    apply d.radiusThree_endpoint_alternatives h ham ham' (hadj 0)
      (fun he => by have := hinj he; norm_num at this)
      (fun he => by have := hinj he; norm_num at this) htm (z 4) (z 0*z 2)
      ((hf 2 0).2 (by norm_num)) ((hf 2 1).2 (by norm_num))
      (fun he => by have := (hf 2 (-1)).1 he; omega)
      himage₀ ((Commute.refl _).mul_right hc02)
      d.branch_label_alternative
    · simpa only [p, add_zero] using h12.symm
    · exact hn13
    · exact h01.symm
    · simpa only [p, add_zero] using hn02
  have hy : d.label u₆ = z 4 ∨ d.label u₆ = z 4*z 2 ∨
      d.label u₆ = z 4*(z 0*z 2) ∨ d.label u₆ = z 4*z 2*(z 0*z 2) := by
    apply d.radiusThree_endpoint_alternatives h (hadj 3).symm (hadj 2).symm (hadj 1).symm
      (fun he => by have := hinj he; norm_num at this)
      (fun he => by have := hinj he; norm_num at this) (ht 2) (z (-2)) (z 0*z 2)
      ((hfm 2).2 (by norm_num)) ((hfm 1).2 (by norm_num))
      (fun he => by have := (hfm 3).1 he; omega)
      himage₆ (hc02.symm.mul_right (Commute.refl _))
      d.branch_label_alternative
    · exact h45
    · exact hn53
    · exact h56
    · exact hn64
  simpa only [z, p, add_zero] using
    endpoint_commutator hcm0 hcm2 hc02 hc04 hc24 htrack' hx hy

/-- A single track commutator gives the source formula on every based six-arc. -/
theorem CanonicalLabelSetup.six_based_arc_of_radiusThree_track_commutator
    (d : CanonicalLabelSetup F s) (h : LargeTreeSource F s) (hr : d.radius = 3)
    (htrack : ⁅d.label (d.track.vertex (d.center-2)),
      d.label (d.track.vertex (d.center+4))⁆ =
        d.label (d.track.vertex d.center) * d.label (d.track.vertex (d.center+2)))
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) 6 v)
    (hp : p.Nonbacktracking) (hv : v.type = d.side) :
    ⁅d.label v, d.label p.endpoint⁆ =
      d.label (p.toWalk.getVert 2) * d.label (p.toWalk.getVert 4) := by
  rcases p with ⟨⟨v₁, h01⟩, ⟨⟨v₂, h12⟩, ⟨⟨v₃, h23⟩,
    ⟨⟨v₄, h34⟩, ⟨⟨v₅, h45⟩, ⟨⟨v₆, h56⟩, rest⟩⟩⟩⟩⟩⟩
  change ⁅d.label v, d.label v₆⁆ = d.label v₂ * d.label v₄
  rcases hp with ⟨h20, h31, h42, h53, h64, _⟩
  have hv₂ : v₂.type = d.side := (type_of_two_steps h01 h12).trans hv
  have hv₄ : v₄.type = d.side := (type_of_two_steps h23 h34).trans hv₂
  have hv₆ : v₆.type = d.side := (type_of_two_steps h45 h56).trans hv₄
  let q : BasedWalk (RankTwo.graph F) 2 v₂ :=
    ⟨⟨v₃, h23⟩, ⟨⟨v₄, h34⟩, PUnit.unit⟩⟩
  have hq : q.Nonbacktracking := ⟨h42, trivial⟩
  obtain ⟨g, hg⟩ := h.action.toCubicTreeAction.congruent_arcs s h.regular
    (show 2 ≤ s by have := h.five_le; omega) q
    (d.track.arc d.center 2) hq (d.track.arc_nonbacktracking _ _)
    (hv₂.trans d.center_type.symm)
  change [g • v₂, g • v₃, g • v₄] =
    [d.track.vertex d.center, d.track.vertex (d.center+1),
      d.track.vertex (d.center+1+1)] at hg
  simp only [List.cons.injEq, and_true, show d.center+1+1 = d.center+2 by omega] at hg
  obtain ⟨hg₂, hg₃, hg₄⟩ := hg
  have he := d.radiusThree_aligned_arms h.action.toCubicTreeAction hr htrack
    (g • v) (g • v₁) (g • v₅) (g • v₆)
    (trackGraphAction.map_adj g h01)
    (by simpa only [hg₂] using trackGraphAction.map_adj g h12)
    (by rw [← hg₃]; exact fun he => h31 ((MulAction.toPerm g).injective he).symm)
    (by rw [← hg₂]; exact fun he => h20 ((MulAction.toPerm g).injective he).symm)
    (by simpa only [hg₄] using trackGraphAction.map_adj g h45)
    (trackGraphAction.map_adj g h56)
    (by rw [← hg₃]; exact fun he => h53 ((MulAction.toPerm g).injective he))
    (by rw [← hg₄]; exact fun he => h64 ((MulAction.toPerm g).injective he))
  apply (MulAut.conj g).injective
  rw [map_commutatorElement, map_mul]
  change ⁅g*d.label v*g⁻¹, g*d.label v₆*g⁻¹⁆ =
    (g*d.label v₂*g⁻¹)*(g*d.label v₄*g⁻¹)
  rw [← d.conjugate g v hv, ← d.conjugate g v₆ hv₆,
    ← d.conjugate g v₂ hv₂, ← d.conjugate g v₄ hv₄, hg₂, hg₄]
  exact he

/-- The literal walk formulation used by the local Mathieu relations. -/
theorem CanonicalLabelSetup.six_arc_of_radiusThree_track_commutator
    (d : CanonicalLabelSetup F s) (h : LargeTreeSource F s) (hr : d.radius = 3)
    (htrack : ⁅d.label (d.track.vertex (d.center-2)),
      d.label (d.track.vertex (d.center+4))⁆ =
        d.label (d.track.vertex d.center) * d.label (d.track.vertex (d.center+2)))
    (a b : RankTwo.Vertex F) (p : (RankTwo.graph F).Walk a b)
    (ha : a.type = d.side) (hp : p.IsPath) (hlen : p.length = 6) :
    ⁅d.label a, d.label b⁆ = d.label (p.getVert 2) * d.label (p.getVert 4) := by
  let q : BasedWalk (RankTwo.graph F) 6 a := hlen ▸ BasedWalk.ofWalk p
  have hq : q.Nonbacktracking := by
    dsimp only [q]
    simpa only [BasedWalk.nonbacktracking_cast] using
      BasedWalk.nonbacktracking_ofWalk_of_isPath p hp
  have hqe : q.endpoint = b := by
    dsimp only [q]
    simp only [BasedWalk.endpoint_cast, BasedWalk.endpoint_ofWalk]
  have hqv : q.toWalk.support = p.support := by
    rw [BasedWalk.support_toWalk]
    dsimp only [q]
    simp only [BasedWalk.vertices_cast, BasedWalk.vertices_ofWalk]
  have hget (n : ℕ) (hn : n ≤ 6) : q.toWalk.getVert n = p.getVert n := by
    rw [q.toWalk.getVert_eq_support_getElem (by rw [BasedWalk.length_toWalk]; exact hn),
      p.getVert_eq_support_getElem (by omega)]
    simp only [hqv]
  have he := d.six_based_arc_of_radiusThree_track_commutator h hr htrack q hq ha
  simpa only [hqe, hget 2 (by omega), hget 4 (by omega)] using he

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
