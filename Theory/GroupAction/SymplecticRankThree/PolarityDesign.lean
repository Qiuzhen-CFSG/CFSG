module
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Tauto

/-!
# Lines and pointwise kernels of a finite polarity design

A reflexive symmetric incidence relation has blocks of size q²+q+1 and
pairwise block intersections of size q+1. Defining a line as the intersection
of all blocks through two points gives unique lines and the upper bound q+1.
An incidence automorphism fixing a block pointwise and an outside point fixes
a second block, then all points off the joining line, and finally the line by
counting. The only numerical restriction for this semiregularity argument is
q ≥ 2, so the binary case is included.

Once all hyperbolic lines have q+1 points, the singular lines are the
intersections of their polar blocks and have the same size. This module proves
the elementary incidence part of Higman §§7–8; it does not assert projective
reconstruction, coordinatization, or symplectic group recognition.

Source: D. G. Higman, *Finite permutation groups of rank 3*, Math. Z. 86
(1964), 145–156, §7(ii), (vii), and Lemma 10, printed pp.151–154.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree

/-- A symmetric incidence relation with the point/hyperplane parameters of
projective three-space. No projective coordinatization is part of this data. -/
structure PolarityDesign (Ω : Type*) [Finite Ω] (q : ℕ) where
  incident : Ω → Ω → Prop
  refl : ∀ a, incident a a
  symm : ∀ {a b}, incident a b → incident b a
  block_card : ∀ a, {b | incident a b}.ncard = q^2+q+1
  intersection_card : ∀ {a b}, a ≠ b →
    ({x | incident a x} ∩ {x | incident b x}).ncard = q+1

namespace PolarityDesign
variable {Ω : Type*} [Finite Ω] {q : ℕ} (D : PolarityDesign Ω q)

@[expose] def block (a : Ω) : Set Ω := {b | D.incident a b}
@[expose] def line (a b : Ω) : Set Ω :=
  {x | ∀ z, D.incident z a → D.incident z b → D.incident z x}

@[simp] theorem mem_block {a b : Ω} : b ∈ D.block a ↔ D.incident a b := Iff.rfl
@[simp] theorem mem_line {a b x : Ω} : x ∈ D.line a b ↔
    ∀ z, D.incident z a → D.incident z b → D.incident z x := Iff.rfl

theorem incident_comm {a b : Ω} : D.incident a b ↔ D.incident b a := ⟨D.symm, D.symm⟩
@[simp] theorem left_mem_line (a b : Ω) : a ∈ D.line a b := fun _ ha _ => ha
@[simp] theorem right_mem_line (a b : Ω) : b ∈ D.line a b := fun _ _ hb => hb

theorem line_comm (a b : Ω) : D.line a b = D.line b a := by
  ext x
  simp only [mem_line]
  tauto

theorem line_subset_block {a b z : Ω} (ha : D.incident z a) (hb : D.incident z b) :
    D.line a b ⊆ D.block z := fun _ hx => hx z ha hb

/-- The defining intersections for any two points on a line agree. -/
theorem common_blocks_eq {a b x : Ω} (hab : a ≠ b) (hx : x ∈ D.line a b)
    (hax : a ≠ x) : D.block a ∩ D.block b = D.block a ∩ D.block x := by
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · intro z hz
    exact ⟨hz.1, D.symm (hx z (D.symm hz.1) (D.symm hz.2))⟩
  · rw [show (D.block a ∩ D.block x).ncard = q+1 from D.intersection_card hax,
      show (D.block a ∩ D.block b).ncard = q+1 from D.intersection_card hab]

theorem line_eq_of_mem {a b x : Ω} (hab : a ≠ b) (hx : x ∈ D.line a b)
    (hax : a ≠ x) : D.line a x = D.line a b := by
  have he := D.common_blocks_eq hab hx hax
  ext y
  change (∀ z, D.incident z a → D.incident z x → D.incident z y) ↔
    (∀ z, D.incident z a → D.incident z b → D.incident z y)
  constructor
  · intro h z hza hzb
    have hz : z ∈ D.block a ∩ D.block x := he ▸ ⟨D.symm hza, D.symm hzb⟩
    exact h z hza (D.symm hz.2)
  · intro h z hza hzx
    have hz : z ∈ D.block a ∩ D.block b := he.symm ▸ ⟨D.symm hza, D.symm hzx⟩
    exact h z hza (D.symm hz.2)

/-- Two different points of a line generate that same line. -/
theorem line_eq_of_mem_of_mem {a b x y : Ω} (hab : a ≠ b)
    (hx : x ∈ D.line a b) (hy : y ∈ D.line a b) (hxy : x ≠ y) :
    D.line x y = D.line a b := by
  by_cases hax : a = x
  · subst x
    exact D.line_eq_of_mem hab hy hxy
  · have hxa : D.line x a = D.line a b :=
      (D.line_comm x a).trans (D.line_eq_of_mem hab hx hax)
    rw [← hxa] at hy
    exact (D.line_eq_of_mem (Ne.symm hax) hy hxy).trans hxa

/-- A hyperbolic line meets the polar block of either endpoint only there. -/
theorem hyperbolic_line_inter_block {a b : Ω} (hab : ¬ D.incident a b) :
    D.line a b ∩ D.block a = {a} := by
  have hne : a ≠ b := fun h => hab (h ▸ D.refl a)
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hn
    have hax : a ≠ x := Ne.symm hn
    have he := D.common_blocks_eq hne hx.1 hax
    have ha : a ∈ D.block a ∩ D.block x := ⟨D.refl a, D.symm hx.2⟩
    have : a ∈ D.block a ∩ D.block b := he.symm ▸ ha
    exact hab (D.symm this.2)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact ⟨D.left_mem_line a b, D.refl a⟩

/-- A line not contained in a block meets it in at most one point. -/
theorem line_block_unique {a b z x y : Ω} (hab : a ≠ b)
    (hza : ¬ D.incident z a) (hx : x ∈ D.line a b) (hy : y ∈ D.line a b)
    (hzx : D.incident z x) (hzy : D.incident z y) : x = y := by
  by_contra hxy
  have he := D.line_eq_of_mem_of_mem hab hx hy hxy
  have ha : a ∈ D.line x y := he.symm ▸ D.left_mem_line a b
  exact hza (ha z hzx hzy)

/-- Every line has at most q+1 points; this uses no group recognition. -/
theorem line_card_le (hq : 1 ≤ q) {a b : Ω} (hab : a ≠ b) :
    (D.line a b).ncard ≤ q+1 := by
  have hc : 1 < (D.block a ∩ D.block b).ncard := by
    rw [show (D.block a ∩ D.block b).ncard = q+1 from D.intersection_card hab]
    omega
  obtain ⟨z,hz,w,hw,hzw⟩ := (Set.one_lt_ncard).mp hc
  have hsub : D.line a b ⊆ D.block z ∩ D.block w :=
    fun x hx => ⟨hx z (D.symm hz.1) (D.symm hz.2), hx w (D.symm hw.1) (D.symm hw.2)⟩
  exact (Set.ncard_le_ncard hsub).trans_eq (D.intersection_card hzw)

/-- An automorphism fixing the polar block moves each point only along its
line with the pole. -/
theorem map_mem_line_of_fixes_block (e : Ω ≃ Ω)
    (he : ∀ x y, D.incident (e x) (e y) ↔ D.incident x y)
    {a : Ω} (ha : ∀ x ∈ D.block a, e x = x) (x : Ω) :
    e x ∈ D.line a x := by
  intro z hza hzx
  have hz := ha z (D.symm hza)
  simpa only [hz] using (he z x).mpr hzx

/-- The kernel on one polar block acts semiregularly on its complement.
This is Higman §7(vii), proved directly from incidence and counting. -/
theorem eq_refl_of_fixes_block_and_point (hq : 2 ≤ q) (e : Ω ≃ Ω)
    (he : ∀ x y, D.incident (e x) (e y) ↔ D.incident x y)
    {a b : Ω} (ha : ∀ x ∈ D.block a, e x = x)
    (hab : ¬ D.incident a b) (hb : e b = b) : e = Equiv.refl Ω := by
  have hba : ¬ D.incident b a := fun h => hab (D.symm h)
  have hne : a ≠ b := fun h => hab (h ▸ D.refl a)
  have hb' : ∀ x ∈ D.block b, e x = x := by
    intro x hx
    by_cases hax : D.incident a x
    · exact ha x hax
    · have hax' : a ≠ x := fun h => hax (h ▸ D.refl a)
      apply D.line_block_unique hax' hba (D.map_mem_line_of_fixes_block e he ha x)
        (D.right_mem_line a x)
      · simpa only [hb] using (he b x).mpr hx
      · exact hx
  have hoff : ∀ y, y ∉ D.line a b → e y = y := by
    intro y hy
    have hay : a ≠ y := fun h => hy (h ▸ D.left_mem_line a b)
    have hby : b ≠ y := fun h => hy (h ▸ D.right_mem_line a b)
    by_contra hey
    have hya := D.map_mem_line_of_fixes_block e he ha y
    have hyb := D.map_mem_line_of_fixes_block e he hb' y
    have hL : D.line a y = D.line b y := by
      exact (D.line_eq_of_mem_of_mem hay (D.right_mem_line a y) hya (Ne.symm hey)).symm.trans
        (D.line_eq_of_mem_of_mem hby (D.right_mem_line b y) hyb (Ne.symm hey))
    have hbL : b ∈ D.line a y := hL.symm ▸ D.left_mem_line b y
    have habL : D.line a b = D.line a y := D.line_eq_of_mem hay hbL hne
    exact hy (habL.symm ▸ D.right_mem_line a y)
  apply Equiv.ext
  intro u
  by_contra hu
  have hsub : D.block u \ D.line a b ⊆ D.block u ∩ D.block (e u) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    change D.incident (e u) x
    simpa only [hoff x hx.2] using (he u x).mpr hx.1
  have hc := Set.ncard_le_ncard hsub
  rw [show (D.block u ∩ D.block (e u)).ncard = q+1 from
    D.intersection_card (Ne.symm hu)] at hc
  have hd := Set.ncard_le_ncard_sdiff_add_ncard (D.block u) (D.line a b)
  rw [show (D.block u).ncard = q^2+q+1 from D.block_card u] at hd
  have hl := D.line_card_le (by omega) hne
  have hs : q+1 < q^2 := by nlinarith
  omega

/-- The totally singular line step in Higman Lemma 10. Once hyperbolic
lines have q+1 points, a singular line is the intersection of its two polar blocks. -/
theorem singular_line_eq_inter
    (hhyp : ∀ a b, ¬ D.incident a b → (D.line a b).ncard = q+1)
    {a b : Ω} (hab : a ≠ b) (hab' : D.incident a b) :
    D.line a b = D.block a ∩ D.block b := by
  apply Set.Subset.antisymm
  · exact fun x hx => ⟨hx a (D.refl a) hab', hx b (D.symm hab') (D.refl b)⟩
  · intro x hx z hza hzb
    by_contra hzx
    have hsub : D.line z x ⊆ D.block a ∩ D.block b := fun y hy =>
      ⟨hy a (D.symm hza) hx.1, hy b (D.symm hzb) hx.2⟩
    have he : D.line z x = D.block a ∩ D.block b :=
      Set.eq_of_subset_of_ncard_le hsub (by
        rw [hhyp z x hzx,
          show (D.block a ∩ D.block b).ncard = q+1 from D.intersection_card hab])
    have ha : a ∈ D.line z x ∩ D.block z :=
      ⟨he.symm ▸ ⟨D.refl a, D.symm hab'⟩, hza⟩
    rw [D.hyperbolic_line_inter_block hzx, Set.mem_singleton_iff] at ha
    exact hzx (ha ▸ hx.1)

/-- All lines have the projective line size. This is the elementary part of
Higman Lemma 10, before projective-space reconstruction and coordinatization. -/
theorem all_lines_card
    (hhyp : ∀ a b, ¬ D.incident a b → (D.line a b).ncard = q+1)
    {a b : Ω} (hab : a ≠ b) : (D.line a b).ncard = q+1 := by
  by_cases h : D.incident a b
  · rw [D.singular_line_eq_inter hhyp hab h]
    exact D.intersection_card hab
  · exact hhyp a b h

/-- Incidence automorphisms preserve the lines defined by all common blocks. -/
theorem map_mem_line_iff (e : Ω ≃ Ω)
    (he : ∀ x y, D.incident (e x) (e y) ↔ D.incident x y) (a b x : Ω) :
    e x ∈ D.line (e a) (e b) ↔ x ∈ D.line a b := by
  constructor
  · intro hx z hza hzb
    exact (he z x).mp (hx (e z) ((he z a).mpr hza) ((he z b).mpr hzb))
  · intro hx z hza hzb
    obtain ⟨w, rfl⟩ := e.surjective z
    exact (he w x).mpr (hx w ((he w a).mp hza) ((he w b).mp hzb))

/-- A line's cardinality is preserved by an incidence automorphism. -/
theorem line_card_map (e : Ω ≃ Ω)
    (he : ∀ x y, D.incident (e x) (e y) ↔ D.incident x y) (a b : Ω) :
    (D.line (e a) (e b)).ncard = (D.line a b).ncard := by
  have hh : e '' D.line a b = D.line (e a) (e b) := by
    ext z
    obtain ⟨x,rfl⟩ := e.surjective z
    rw [Set.mem_image_equiv, e.symm_apply_apply, D.map_mem_line_iff e he]
  rw [← hh, Set.ncard_image_of_injective _ e.injective]

end PolarityDesign
end Theory.GroupAction.SymplecticRankThree
