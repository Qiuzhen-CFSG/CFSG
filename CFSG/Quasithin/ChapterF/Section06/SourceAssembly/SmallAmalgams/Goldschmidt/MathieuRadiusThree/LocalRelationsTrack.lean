module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelCenter
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SourceCuts
public import Theory.GroupAction.CubicTree.TrackArcs
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The nondegenerate radius-three track commutator

Short-arc transitivity carries each folded four-edge path to a straight
track segment. Its endpoint-label product cannot equal one or the midpoint
label: a suitable track vertex is fixed by the first endpoint and midpoint
labels, but moved by the other endpoint label. Applied in both orientations,
this excludes the two single-label values of the six-edge commutator.

The folded products also put the commutator in both literal radius-two
label groups. Consequently the source central correction implies the
required two-label value without additional membership or exclusion premises.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), the paragraph
preceding (6.12.3), printed p.404.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree Subgroup.CosetGeometry
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem four_arc_product
    (d : CanonicalLabelSetup F s) (h : LargeTreeSource F s) (hr : d.radius = 3)
    {v₀ v₁ v₂ v₃ v₄ : RankTwo.Vertex F}
    (h01 : (RankTwo.graph F).Adj v₀ v₁)
    (h12 : (RankTwo.graph F).Adj v₁ v₂)
    (h23 : (RankTwo.graph F).Adj v₂ v₃)
    (h34 : (RankTwo.graph F).Adj v₃ v₄)
    (h20 : v₂ ≠ v₀) (h31 : v₃ ≠ v₁) (h42 : v₄ ≠ v₂)
    (hv₀ : v₀.type = d.side) :
    d.label v₀ * d.label v₄ ≠ 1 ∧ d.label v₀ * d.label v₄ ≠ d.label v₂ := by
  let q : BasedWalk (RankTwo.graph F) 4 v₀ :=
    ⟨⟨v₁, h01⟩, ⟨⟨v₂, h12⟩, ⟨⟨v₃, h23⟩, ⟨⟨v₄, h34⟩, PUnit.unit⟩⟩⟩⟩
  have hq : q.Nonbacktracking := ⟨h20, h31, h42, trivial⟩
  obtain ⟨g, hg⟩ := h.action.toCubicTreeAction.congruent_arcs s h.regular
    (show 4 ≤ s by have := h.five_le; omega) q (d.track.arc d.center 4)
    hq (d.track.arc_nonbacktracking _ _) (hv₀.trans d.center_type.symm)
  change [g • v₀, g • v₁, g • v₂, g • v₃, g • v₄] =
    [d.track.vertex d.center, d.track.vertex (d.center+1),
      d.track.vertex (d.center+1+1), d.track.vertex (d.center+1+1+1),
      d.track.vertex (d.center+1+1+1+1)] at hg
  simp only [List.cons.injEq, and_true,
    show d.center+1+1 = d.center+2 by omega,
    show d.center+2+1 = d.center+3 by omega,
    show d.center+3+1 = d.center+4 by omega] at hg
  obtain ⟨hg₀, _, hg₂, _, hg₄⟩ := hg
  have hv₂ : v₂.type = d.side := by
    have hh := d.shifted_type 1
    simpa only [mul_one, ← hg₂, CosetGeometry.smul_type] using hh
  have hv₄ : v₄.type = d.side := by
    have hh := d.shifted_type 2
    simpa only [show (2:ℤ)*2=4 by norm_num, ← hg₄, CosetGeometry.smul_type] using hh
  have hc₀ : d.label (d.track.vertex d.center) = (MulAut.conj g) (d.label v₀) := by
    rw [← hg₀]
    exact d.conjugate g v₀ hv₀
  have hc₂ : d.label (d.track.vertex (d.center+2)) = (MulAut.conj g) (d.label v₂) := by
    rw [← hg₂]
    exact d.conjugate g v₂ hv₂
  have hc₄ : d.label (d.track.vertex (d.center+4)) = (MulAut.conj g) (d.label v₄) := by
    rw [← hg₄]
    exact d.conjugate g v₄ hv₄
  let w := d.track.vertex (d.center-2)
  have hf₀ : d.label (d.track.vertex d.center) • w = w := by
    simpa only [mul_zero, add_zero] using
      (d.shifted_fixed_iff 0 (d.center-2)).mpr (by rw [hr]; omega)
  have hf₂ : d.label (d.track.vertex (d.center+2)) • w = w := by
    simpa only [mul_one] using
      (d.shifted_fixed_iff 1 (d.center-2)).mpr (by rw [hr]; omega)
  have hn₄ : d.label (d.track.vertex (d.center+4)) • w ≠ w := by
    intro he
    have hh := (d.shifted_fixed_iff 2 (d.center-2)).mp he
    rw [hr] at hh
    omega
  have hno (z : G) (hz : z • w = w)
      (he : d.label (d.track.vertex d.center) *
        d.label (d.track.vertex (d.center+4)) = z) : False := by
    apply hn₄
    apply (MulAction.toPerm (d.label (d.track.vertex d.center))).injective
    change d.label (d.track.vertex d.center) •
      (d.label (d.track.vertex (d.center+4)) • w) =
      d.label (d.track.vertex d.center) • w
    rw [← mul_smul, he, hz, hf₀]
  constructor
  · intro he
    apply hno 1 (one_smul G w)
    rw [hc₀, hc₄, ← map_mul, he, map_one]
  · intro he
    apply hno _ hf₂
    rw [hc₀, hc₄, hc₂, ← map_mul, he]

private theorem folded_commutator
    (d : CanonicalLabelSetup F s) (h : LargeTreeSource F s) (hr : d.radius = 3)
    {a b c : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b)
    (hbc : (RankTwo.graph F).Adj b c) (hne : a ≠ c)
    (ha : a.type = d.side) (g : G) (hgc : g • c = c) (hgb : g • b ≠ b) :
    ⁅d.label a, g⁆ ≠ 1 ∧ ⁅d.label a, g⁆ ≠ d.label c := by
  have hcb : (RankTwo.graph F).Adj c (g • b) := by
    simpa only [hgc] using trackGraphAction.map_adj g hbc.symm
  have hba : (RankTwo.graph F).Adj (g • b) (g • a) :=
    trackGraphAction.map_adj g hab.symm
  have hac : g • a ≠ c := by
    rw [← hgc]
    exact (MulAction.toPerm g).injective.ne hne
  have hh := four_arc_product d h hr hab hbc hcb hba hne.symm hgb hac ha
  have he : d.label a * d.label (g • a) = ⁅d.label a, g⁆ := by
    rw [d.conjugate g a ha, commutatorElement_def, d.label_inv ha]
    simp only [mul_assoc]
  rwa [he] at hh

/-- The track commutator is nonidentity and differs from both midpoint
labels, as required before (6.12.3). -/
theorem CanonicalLabelSetup.radiusThree_track_commutator_ne
    (d : CanonicalLabelSetup F s) (h : LargeTreeSource F s) (hr : d.radius = 3) :
    let u := ⁅d.label (d.track.vertex (d.center-2)),
      d.label (d.track.vertex (d.center+4))⁆
    u ≠ 1 ∧ u ≠ d.label (d.track.vertex d.center) ∧
      u ≠ d.label (d.track.vertex (d.center+2)) := by
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
  have hleft : ⁅z (-2), z 4⁆ ≠ 1 ∧ ⁅z (-2), z 4⁆ ≠ z 0 :=
    folded_commutator d h hr (by simpa using hadj (-2)) (by simpa using hadj (-1))
      (fun he => by have := hinj he; omega) (by simpa using ht (-1)) (z 4)
      (by simpa using (hf 2 0).mpr (by omega))
      (by simpa using (show z (2*2) • p (-1) ≠ p (-1) from
        fun he => by have := (hf 2 (-1)).mp he; omega))
  have hright : ⁅z 4, z (-2)⁆ ≠ 1 ∧ ⁅z 4, z (-2)⁆ ≠ z 2 :=
    folded_commutator d h hr (hadj 3).symm (hadj 2).symm
      (fun he => by have := hinj he; omega) (ht 2) (z (-2))
      (by simpa using (hf (-1) 2).mpr (by omega))
      (by simpa using (show z (2*(-1)) • p 3 ≠ p 3 from
        fun he => by have := (hf (-1) 3).mp he; omega))
  have hne : ⁅z (-2), z 4⁆ ≠ z 2 := by
    intro he
    apply hright.2
    rw [← commutatorElement_inv, he]
    exact d.label_inv (ht 1)
  simpa only [z, p, add_zero, sub_eq_add_neg] using
    And.intro hleft.1 (And.intro hleft.2 hne)

private theorem track_dist_two_le (d : CanonicalLabelSetup F s)
    (h : LargeTreeSource F s) (i : ℤ) :
    (RankTwo.graph F).dist (d.track.vertex i) (d.track.vertex (i+2)) ≤ 2 := by
  have hh := h.action.tree.connected.dist_triangle
    (u := d.track.vertex i) (v := d.track.vertex (i+1)) (w := d.track.vertex (i+2))
  have h01 := dist_eq_one_iff_adj.mpr (d.track.adjacent i)
  have h12 : (RankTwo.graph F).dist (d.track.vertex (i+1)) (d.track.vertex (i+2)) = 1 :=
    dist_eq_one_iff_adj.mpr (by simpa only [show i+1+1=i+2 by omega] using d.track.adjacent (i+1))
  omega

private theorem label_commutator_mem (d : CanonicalLabelSetup F s)
    {a b : RankTwo.Vertex F} {r : ℕ} (hb : b.type = d.side)
    (hd : (RankTwo.graph F).dist a b ≤ r) (g : G) (hg : g • a = a) :
    ⁅d.label b, g⁆ ∈ d.labelBall a r := by
  have hgb : (g • b).type = d.side := by simpa only [CosetGeometry.smul_type] using hb
  have hdist : (RankTwo.graph F).dist a (g • b) ≤ r := by
    have hh := RankTwo.dist_smul F g a b
    rw [hg] at hh
    exact hh ▸ hd
  have hm := (d.labelBall a r).mul_mem (d.label_mem_labelBall hb hd)
    (d.label_mem_labelBall hgb hdist)
  have he : d.label b * d.label (g • b) = ⁅d.label b, g⁆ := by
    rw [d.conjugate g b hb, commutatorElement_def, d.label_inv hb]
    simp only [mul_assoc]
  rwa [he] at hm

/-- The literal track commutator belongs to both radius-two label groups
and to their mutual commutator subgroup. -/
theorem CanonicalLabelSetup.radiusThree_track_commutator_mem
    (d : CanonicalLabelSetup F s) (h : LargeTreeSource F s) (hr : d.radius = 3) :
    let a := d.track.vertex d.center
    let b := d.track.vertex (d.center+2)
    let u := ⁅d.label (d.track.vertex (d.center-2)),
      d.label (d.track.vertex (d.center+4))⁆
    u ∈ d.labelBall a 2 ∧ u ∈ d.labelBall b 2 ∧
      u ∈ ⁅d.labelBall a 2, d.labelBall b 2⁆ := by
  let a := d.track.vertex d.center
  let b := d.track.vertex (d.center+2)
  let x := d.track.vertex (d.center-2)
  let y := d.track.vertex (d.center+4)
  have hx : x.type = d.side := by simpa [x, sub_eq_add_neg] using d.shifted_type (-1)
  have hy : y.type = d.side := by simpa [y] using d.shifted_type 2
  have hax : (RankTwo.graph F).dist a x ≤ 2 := by
    simpa only [a, x, show d.center-2+2=d.center by omega, dist_comm] using
      track_dist_two_le d h (d.center-2)
  have hby : (RankTwo.graph F).dist b y ≤ 2 := by
    simpa only [b, y, show d.center+2+2=d.center+4 by omega] using
      track_dist_two_le d h (d.center+2)
  have hya : d.label y • a = a := by
    simpa only [a, y, show (2:ℤ)*2=4 by norm_num] using
      (d.shifted_fixed_iff 2 d.center).mpr (by rw [hr]; omega)
  have hxb : d.label x • b = b := by
    simpa only [b, x, show (2:ℤ)*(-1) = -2 by norm_num, sub_eq_add_neg] using
      (d.shifted_fixed_iff (-1) (d.center+2)).mpr (by rw [hr]; omega)
  refine ⟨label_commutator_mem d hx hax (d.label y) hya, ?_, ?_⟩
  · have hh := (d.labelBall b 2).inv_mem (label_commutator_mem d hy hby (d.label x) hxb)
    simpa only [commutatorElement_inv] using hh
  · exact commutator_mem_commutator (d.label_mem_labelBall hx hax)
      (d.label_mem_labelBall hy hby)

/-- Source (6.12.1) now implies (6.12.3), with both the membership and the
excluded single-label alternative discharged on the actual chosen track. -/
theorem CanonicalLabelSetup.radiusThree_track_commutator_of_central_correction
    (d : CanonicalLabelSetup F s) (h : LargeTreeSource F s) (hr : d.radius = 3)
    (hc : ∀ g ∈ RankTwo.stabilizer F (d.track.vertex d.center),
      Commute (⁅d.label (d.track.vertex (d.center-2)),
        d.label (d.track.vertex (d.center+4))⁆ *
          d.label (d.track.vertex (d.center+2))) g) :
    ⁅d.label (d.track.vertex (d.center-2)),
      d.label (d.track.vertex (d.center+4))⁆ =
        d.label (d.track.vertex d.center) * d.label (d.track.vertex (d.center+2)) := by
  exact d.radiusTwo_central_correction h.action.toCubicTreeAction
    (by omega) (by have := h.five_le; omega) d.center_type
    (by simpa only [mul_one] using d.shifted_type 1)
    (track_dist_two_le d h d.center)
    (d.radiusThree_track_commutator_mem h hr).1
    (d.radiusThree_track_commutator_ne h hr).2.2 hc
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
