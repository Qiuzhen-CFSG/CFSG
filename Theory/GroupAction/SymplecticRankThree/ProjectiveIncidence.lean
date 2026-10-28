module
public import Theory.GroupAction.SymplecticRankThree.PolarityDesign
public import Mathlib.Data.Set.Card.Arithmetic

/-!
# Projective incidence from Higman's polarity design

Assume the proved polarity-design parameters and that every line has q+1
points. Distinct polar blocks intersect in a line. In one block, the lines
joining a point c to the points of a line not containing c are disjoint off
c; their cardinalities fill the block. Thus coplanar lines meet. Applying
this to two block intersections proves that any three blocks meet, and by
polarity any three points lie in a block. Noncollinear triples determine
that block uniquely. This proves the Veblen intersection axiom directly,
without invoking Dembowski–Wagner. The source degree supplies four
noncoplanar points. All statements include q=2.

These are incidence axioms, not field coordinatization or symplectic
recognition. Constructing a four-dimensional vector space, the alternating
form and the induced semilinear action remains a separate obligation.

Source: Higman, *Finite permutation groups of rank 3*, Math. Z. 86 (1964),
Lemma 10, pp.153–154. The counting argument here proves the required
incidence consequences rather than assuming the cited reconstruction.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree.PolarityDesign
variable {Ω : Type*} [Finite Ω] {q : ℕ} (D : PolarityDesign Ω q)
variable (hline : ∀ a b, a ≠ b → (D.line a b).ncard = q+1)

include hline

theorem intersection_eq_line {a b x y : Ω} (hab : a ≠ b)
    (hx : x ∈ D.block a ∩ D.block b) (hy : y ∈ D.block a ∩ D.block b)
    (hxy : x ≠ y) : D.block a ∩ D.block b = D.line x y := by
  symm
  apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite _)
  · exact fun z hz => ⟨hz a hx.1 hy.1, hz b hx.2 hy.2⟩
  · rw [show (D.block a ∩ D.block b).ncard = q+1 from D.intersection_card hab,
      hline x y hxy]

theorem block_pencil {p a b c : Ω} (hab : a ≠ b)
    (ha : a ∈ D.block p) (hb : b ∈ D.block p) (hc : c ∈ D.block p)
    (hcL : c ∉ D.line a b) :
    (⋃ x ∈ D.line a b, D.line c x \ {c}) = D.block p \ {c} := by
  classical
  have hcx : ∀ x ∈ D.line a b, c ≠ x := fun x hx he => hcL (he.symm ▸ hx)
  have hdis : (D.line a b).PairwiseDisjoint (fun x => D.line c x \ {c}) := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have hcz : c ≠ z := Ne.symm hz.2
    have he : D.line c x = D.line c y :=
      (D.line_eq_of_mem (hcx x hx) hz.1 hcz).symm.trans
        (D.line_eq_of_mem (hcx y hy) hz'.1 hcz)
    have hxyL : D.line x y = D.line c x :=
      D.line_eq_of_mem_of_mem (hcx x hx) (D.right_mem_line c x)
        (he.symm ▸ D.right_mem_line c y) hxy
    have habL := D.line_eq_of_mem_of_mem hab hx hy hxy
    exact hcL (habL ▸ hxyL.symm ▸ D.left_mem_line c x)
  apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite _)
  · intro z hz
    obtain ⟨x,hx,hz⟩ := Set.mem_iUnion₂.mp hz
    exact ⟨hz.1 p hc ((D.line_subset_block ha hb) hx),hz.2⟩
  · rw [(Set.toFinite (D.line a b)).ncard_biUnion (fun _ _ => Set.toFinite _) hdis]
    have hs : (∑ᶠ x ∈ D.line a b, (D.line c x \ {c}).ncard) =
        ∑ᶠ x ∈ D.line a b, q := by
      apply finsum_mem_congr rfl
      intro x hx
      rw [Set.ncard_sdiff_singleton_of_mem (D.left_mem_line c x),hline c x (hcx x hx)]
      omega
    rw [hs, Set.ncard_sdiff_singleton_of_mem hc]
    rw [show (D.block p).ncard = q^2+q+1 from D.block_card p]
    rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Set.ncard_eq_toFinset_card, hline a b hab]
    simp only [Nat.cast_id, Nat.add_sub_cancel]
    nlinarith

theorem coplanar_lines_meet {p a b c d : Ω} (hab : a ≠ b) (hcd : c ≠ d)
    (ha : a ∈ D.block p) (hb : b ∈ D.block p)
    (hc : c ∈ D.block p) (hd : d ∈ D.block p) :
    (D.line a b ∩ D.line c d).Nonempty := by
  by_cases hcL : c ∈ D.line a b
  · exact ⟨c,hcL,D.left_mem_line c d⟩
  have hdU : d ∈ ⋃ x ∈ D.line a b, D.line c x \ {c} :=
    (D.block_pencil hline hab ha hb hc hcL).symm ▸ ⟨hd,Ne.symm hcd⟩
  obtain ⟨x,hx,hdx⟩ := Set.mem_iUnion₂.mp hdU
  have hcx : c ≠ x := fun he => hcL (he.symm ▸ hx)
  exact ⟨x,hx,(D.line_eq_of_mem hcx hdx.1 hcd).symm ▸ D.right_mem_line c x⟩

theorem triple_blocks_nonempty (hq : 1 ≤ q) (a b c : Ω) :
    (D.block a ∩ D.block b ∩ D.block c).Nonempty := by
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      exact ⟨a,⟨D.refl a,D.refl a⟩,D.refl a⟩
    · have hn : (D.block a ∩ D.block c).Nonempty := (Set.ncard_pos).mp (by
        rw [show (D.block a ∩ D.block c).ncard = q+1 from D.intersection_card hac]
        omega)
      obtain ⟨x,hx,hx'⟩ := hn
      exact ⟨x,⟨hx,hx⟩,hx'⟩
  by_cases hac : a = c
  · subst c
    have hn : (D.block a ∩ D.block b).Nonempty := (Set.ncard_pos).mp (by
      rw [show (D.block a ∩ D.block b).ncard = q+1 from D.intersection_card hab]
      omega)
    obtain ⟨x,hx,hx'⟩ := hn
    exact ⟨x,⟨hx,hx'⟩,hx⟩
  obtain ⟨x,hx,y,hy,hxy⟩ := (Set.one_lt_ncard).mp (show 1 < (D.block a ∩ D.block b).ncard by
    rw [show (D.block a ∩ D.block b).ncard = q+1 from D.intersection_card hab]
    omega)
  obtain ⟨z,hz,w,hw,hzw⟩ := (Set.one_lt_ncard).mp (show 1 < (D.block a ∩ D.block c).ncard by
    rw [show (D.block a ∩ D.block c).ncard = q+1 from D.intersection_card hac]
    omega)
  obtain ⟨u,hu,hu'⟩ := D.coplanar_lines_meet hline hxy hzw hx.1 hy.1 hz.1 hw.1
  rw [← D.intersection_eq_line hline hab hx hy hxy] at hu
  rw [← D.intersection_eq_line hline hac hz hw hzw] at hu'
  exact ⟨u,hu,hu'.2⟩

theorem exists_block_of_three (hq : 1 ≤ q) (a b c : Ω) :
    ∃ p, a ∈ D.block p ∧ b ∈ D.block p ∧ c ∈ D.block p := by
  obtain ⟨p,⟨ha,hb⟩,hc⟩ := D.triple_blocks_nonempty hline hq a b c
  exact ⟨p,D.symm ha,D.symm hb,D.symm hc⟩

theorem existsUnique_block_of_noncollinear (hq : 1 ≤ q) {a b c : Ω}
    (hab : a ≠ b) (hc : c ∉ D.line a b) :
    ∃! p, a ∈ D.block p ∧ b ∈ D.block p ∧ c ∈ D.block p := by
  obtain ⟨p,ha,hb,hc'⟩ := D.exists_block_of_three hline hq a b c
  refine ⟨p,⟨ha,hb,hc'⟩,?_⟩
  intro z hz
  by_contra hzp
  have he := D.intersection_eq_line hline hzp ⟨hz.1,ha⟩ ⟨hz.2.1,hb⟩ hab
  exact hc (he ▸ ⟨hz.2.2,hc'⟩)

theorem line_meets_block (hq : 1 ≤ q) {a b : Ω} (hab : a ≠ b) (p : Ω) :
    (D.line a b ∩ D.block p).Nonempty := by
  obtain ⟨x,hx,y,hy,hxy⟩ := (Set.one_lt_ncard).mp
    (show 1 < (D.block a ∩ D.block b).ncard by
      rw [show (D.block a ∩ D.block b).ncard = q+1 from D.intersection_card hab]
      omega)
  have he := D.intersection_eq_line hline hxy
    (show a ∈ D.block x ∩ D.block y from ⟨D.symm hx.1,D.symm hy.1⟩)
    (show b ∈ D.block x ∩ D.block y from ⟨D.symm hx.2,D.symm hy.2⟩) hab
  rw [← he]
  exact D.triple_blocks_nonempty hline hq x y p

theorem exists_block_of_intersecting_lines (hq : 1 ≤ q) {a b c d : Ω}
    (hcd : c ≠ d) (hmeet : (D.line a b ∩ D.line c d).Nonempty) :
    ∃ p, a ∈ D.block p ∧ b ∈ D.block p ∧ c ∈ D.block p ∧ d ∈ D.block p := by
  obtain ⟨w,hw,hw'⟩ := hmeet
  by_cases hcw : c = w
  · obtain ⟨p,ha,hb,hd⟩ := D.exists_block_of_three hline hq a b d
    exact ⟨p,ha,hb,hcw.symm ▸ (D.line_subset_block ha hb) hw,hd⟩
  · obtain ⟨p,ha,hb,hc⟩ := D.exists_block_of_three hline hq a b c
    have he := D.line_eq_of_mem hcd hw' hcw
    exact ⟨p,ha,hb,hc,(D.line_subset_block hc ((D.line_subset_block ha hb) hw))
      (he.symm ▸ D.right_mem_line c d)⟩

/-- The Veblen intersection axiom is a theorem of the design and line counts. -/
theorem veblen (hq : 1 ≤ q) {a b c d : Ω}
    (hcd : c ≠ d) (hac : a ≠ c) (hbd : b ≠ d)
    (hmeet : (D.line a b ∩ D.line c d).Nonempty) :
    (D.line a c ∩ D.line b d).Nonempty := by
  obtain ⟨p,ha,hb,hc,hd⟩ := D.exists_block_of_intersecting_lines hline hq hcd hmeet
  exact D.coplanar_lines_meet hline hac hbd ha hc hb hd

/-- Four points spanning the incidence space, from the source degree. -/
theorem exists_noncoplanar (hq : 2 ≤ q)
    (hdegree : Nat.card Ω = q^3+q^2+q+1) :
    ∃ a b c d : Ω, a ≠ b ∧ c ∉ D.line a b ∧
      ¬ ∃ p, a ∈ D.block p ∧ b ∈ D.block p ∧ c ∈ D.block p ∧ d ∈ D.block p := by
  have hpos : 0 < Nat.card Ω := by rw [hdegree]; omega
  let : Nonempty Ω := (Nat.card_pos_iff).mp hpos |>.1
  obtain ⟨p⟩ := ‹Nonempty Ω›
  obtain ⟨a,ha,b,hb,hab⟩ := (Set.one_lt_ncard).mp
    (show 1 < (D.block p).ncard by rw [show (D.block p).ncard = q^2+q+1 from D.block_card p]; nlinarith)
  have hnot : ¬ D.block p ⊆ D.line a b := by
    intro hh
    have hn := Set.ncard_le_ncard hh
    rw [hline a b hab,show (D.block p).ncard = q^2+q+1 from D.block_card p] at hn
    nlinarith
  obtain ⟨c,hc,hcL⟩ := Set.not_subset.mp hnot
  have hout : ¬ (Set.univ : Set Ω) ⊆ D.block p := by
    intro hh
    have hn := Set.ncard_le_ncard hh
    rw [Set.ncard_univ,hdegree,show (D.block p).ncard = q^2+q+1 from D.block_card p] at hn
    have : 0 < q^3 := pow_pos (by omega) _
    omega
  obtain ⟨d,_,hd⟩ := Set.not_subset.mp hout
  refine ⟨a,b,c,d,hab,hcL,?_⟩
  rintro ⟨z,hza,hzb,hzc,hzd⟩
  have hu := D.existsUnique_block_of_noncollinear hline (by omega) hab hcL
  have he : z = p := hu.unique ⟨hza,hzb,hzc⟩ ⟨ha,hb,hc⟩
  exact hd (he ▸ hzd)

end Theory.GroupAction.SymplecticRankThree.PolarityDesign
